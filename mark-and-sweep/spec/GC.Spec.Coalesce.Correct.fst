/// ---------------------------------------------------------------------------
/// GC.Spec.Coalesce.Correct - Correctness of the coalescing pass
/// ---------------------------------------------------------------------------
///
/// `coalesce_correct`: coalescing conserves free space, keeps the blue region
/// of the heap word for word, leaves no two blue objects adjacent, and leaves
/// every white object in place with its size.  See mark-and-sweep/NOTES.md.

module GC.Spec.Coalesce.Correct

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Coalesce

module SI = GC.Spec.SweepInv

module WE = GC.Spec.WalkEnd

#set-options "--z3rlimit 50 --fuel 2 --ifuel 1"

/// Same bound again, for a run whose end is `heap_size` itself (not
/// representable as an `hp_addr`, hence a separate `nat`-ended variant).
#push-options "--z3rlimit 12 --fuel 0 --ifuel 0"
let run_words_bound_top
  (fb: U64.t) (run_words: pos)
  : Lemma
    (requires
      U64.v fb >= U64.v mword /\
      U64.v fb - U64.v mword + run_words * U64.v mword == heap_size)
    (ensures run_words - 1 < pow2 54)
  = assert (run_words * U64.v mword <= heap_size);
    assert (heap_size <= pow2 57);
    FStar.Math.Lemmas.lemma_div_le (run_words * U64.v mword) (pow2 57) (U64.v mword);
    assert_norm (pow2 57 = pow2 54 * 8);
    FStar.Math.Lemmas.cancel_mul_div run_words (U64.v mword);
    assert_norm ((pow2 54 * 8) / 8 == pow2 54)
#pop-options

/// `mk_hp_addr (fb - mword)` and `hd_address (fb <: obj_addr)` are the same
/// address, spelled two ways: `white_inv`'s H-reachability clause (clause 6)
/// uses the former (a plain scalar, needing no `obj_addr` cast on `fb`); the
/// `flush_white_transfer`/`flush_density_transfer`/`flush_reaches_run_end`
/// family, whose signatures predate that clause, use the latter.  Bridges
/// the two so a `walk_visits` fact about one transfers to the other.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let h_addr_agree (fb: U64.t)
  : Lemma
    (requires U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\ U64.v fb % U64.v mword == 0)
    (ensures mk_hp_addr (U64.v fb - U64.v mword) == hd_address (fb <: obj_addr))
  = hd_address_spec (fb <: obj_addr)
#pop-options


let coalesce_aux_empty (g0 g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (coalesce_aux g0 g Seq.empty first_blue run_words fp ==
           flush_blue g first_blue run_words fp)
  = ()
let coalesce_aux_blue_step
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ is_blue (Seq.head objs) g0)
    (ensures
      coalesce_aux g0 g objs first_blue run_words fp ==
      coalesce_aux g0 g (Seq.tail objs)
        (if run_words = 0 then Seq.head objs else first_blue)
        (run_words + U64.v (wosize_of_object (Seq.head objs) g0) + 1) fp)
  = ()

let coalesce_aux_white_step
  (g0 g: heap) (objs: seq obj_addr) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0))
    (ensures
      (let (g', fp') = flush_blue g first_blue run_words fp in
       coalesce_aux g0 g objs first_blue run_words fp ==
       coalesce_aux g0 g' (Seq.tail objs) 0UL 0 fp'))
  = ()

/// ---------------------------------------------------------------------------
/// Free-space accounting
/// ---------------------------------------------------------------------------
///
/// The conserved quantity is the whole size of a block: header plus fields.
/// Coalescing reclaims the absorbed blocks' headers into the merged block's
/// field area, so wosize is not conserved but whole size is.
///
/// Before: B1(wz 2) B2(wz 2) B3(wz 3) B4(wz 1) -- whole 3 + 3 + 4 + 2 = 12
/// After:  B2, B3 merged, B2 has wosize 6      -- whole 3 + 7 + 2 = 12

/// Machine words occupied by an object: its fields plus its header.
let whsize (g: heap) (x: obj_addr) : GTot nat =
  1 + U64.v (wosize_of_object x g)

/// Total whole size of the blue objects of a walk.
let rec blue_whsize (g: heap) (objs: seq obj_addr)
  : GTot nat (decreases Seq.length objs) =
  if Seq.length objs = 0 then 0
  else
    let x = Seq.head objs in
    (if is_blue x g then whsize g x else 0)
    + blue_whsize g (Seq.tail objs)

let total_blue_whsize (g: heap) : GTot nat =
  blue_whsize g (objects zero_addr g)

/// The walk position immediately above x.
let next_pos (g: heap) (x: obj_addr) : GTot nat =
  U64.v (hd_address x) + whsize g x * U64.v mword

/// y sits directly above x, with no gap.
let adjacent (g: heap) (x y: obj_addr) : prop =
  next_pos g x == U64.v (hd_address y)

/// p lies within x's header-and-fields extent.
let in_extent (g: heap) (x: obj_addr) (p: nat) : prop =
  U64.v (hd_address x) <= p /\ p < next_pos g x

/// p is covered by some blue object.
let blue_covered (g: heap) (p: nat) : prop =
  exists (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x p

/// ---------------------------------------------------------------------------
/// Splitting the object walk at a position
/// ---------------------------------------------------------------------------

/// `a` is a position the walk from `s` lands on.
let rec walk_visits (g: heap) (s a: hp_addr)
  : GTot bool (decreases (heap_size - U64.v s)) =
  if U64.v s = U64.v a then true
  else if U64.v s + 8 >= heap_size then false
  else
    let wz = getWosize (read_word g s) in
    let next = U64.v s + (U64.v wz + 1) * 8 in
    if next > heap_size || next >= pow2 64 || next >= heap_size then false
    else begin
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      walk_visits g (mk_hp_addr next) a
    end

val objects_split_from (g: heap) (s a: hp_addr)
  : Lemma
    (requires Seq.length g == heap_size /\ walk_visits g s a)
    (ensures
      (exists (pre: seq obj_addr).
         objects s g == Seq.append pre (objects a g) /\
         (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
         (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)))
    (decreases (heap_size - U64.v s))

/// A visited position is at or above the walk start.
val walk_visits_above (g: heap) (s a: hp_addr)
  : Lemma (requires walk_visits g s a)
          (ensures U64.v s <= U64.v a)
          (decreases (heap_size - U64.v s))

let rec walk_visits_above g s a =
  if U64.v s = U64.v a then ()
  else begin
    let wz = getWosize (read_word g s) in
    let next = U64.v s + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
    walk_visits_above g (mk_hp_addr next) a
  end

let rec objects_split_from g s a =
  let pred (pre: seq obj_addr) : prop =
    objects s g == Seq.append pre (objects a g) /\
    (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
    (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)
  in
  /// The suffix bound, in both cases, from the upstream walk lemma.
  let above (y: obj_addr)
    : Lemma (Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)
    = objects_addresses_gt_start a g y;
      hd_address_spec y
  in
  FStar.Classical.forall_intro above;

  if U64.v s = U64.v a then begin
    Seq.lemma_eq_elim (objects s g) (Seq.append Seq.empty (objects a g));
    FStar.Classical.exists_intro pred Seq.empty
  end
  else begin
    /// `walk_visits` took its recursive branch, so the walk at `s` is
    /// non-empty and steps to `next < heap_size`.
    let wz = getWosize (read_word g s) in
    let next = U64.v s + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
    let nxt = mk_hp_addr next in
    walk_visits_above g nxt a;
    assert (U64.v s < U64.v a);
    WE.walk_end_step g s;
    WE.walk_head g s;
    f_address_spec s;
    let x : obj_addr = f_address s in
    hd_address_spec x;

    objects_split_from g nxt a;
    eliminate exists (pre: seq obj_addr).
        objects nxt g == Seq.append pre (objects a g) /\
        (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
        (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)
    with begin
      let pre' = Seq.cons x pre in
      Seq.lemma_tl x pre;
      Seq.lemma_eq_elim (objects s g) (Seq.cons x (objects nxt g));
      Seq.lemma_eq_elim (objects s g) (Seq.append pre' (objects a g));
      let below (y: obj_addr)
        : Lemma (Seq.mem y pre' ==> U64.v (hd_address y) < U64.v a)
        = mem_cons_lemma y x pre
      in
      FStar.Classical.forall_intro below;
      FStar.Classical.exists_intro pred pre'
    end
  end

val objects_split_at (g: heap) (a: hp_addr)
  : Lemma
    (requires Seq.length g == heap_size /\ walk_visits g zero_addr a)
    (ensures
      (exists (pre: seq obj_addr).
         objects zero_addr g == Seq.append pre (objects a g) /\
         (forall (y: obj_addr). Seq.mem y pre ==> U64.v (hd_address y) < U64.v a) /\
         (forall (y: obj_addr). Seq.mem y (objects a g) ==> U64.v (hd_address y) >= U64.v a)))

let objects_split_at g a = objects_split_from g zero_addr a

/// ---------------------------------------------------------------------------
/// The four obligations of `coalesce_correct`
/// ---------------------------------------------------------------------------

val coalesce_conserves_whsize (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures total_blue_whsize (fst (coalesce g)) == total_blue_whsize g)

val coalesce_preserves_blue_coverage (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in
       forall (p: nat). p < heap_size ==> (blue_covered g' p <==> blue_covered g p)))

val coalesce_no_adjacent_blue (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in
       forall (x y: obj_addr).
         Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
         is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))

val coalesce_preserves_white (g: heap)
  : Lemma
    (requires post_sweep_strong g /\ SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g) /\ is_white x g ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g))

/// ---------------------------------------------------------------------------
/// White preservation: the walk invariant
/// ---------------------------------------------------------------------------
///
/// `g0` is the frozen heap the walk reads colours from; `g` is the heap being
/// built.

let white_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  walk_pre g0 g start objs all_objs first_blue run_words /\
  Seq.length g == heap_size /\
  Seq.length g0 == heap_size /\
  SI.heap_objects_dense g /\
  post_sweep_strong g0 /\
  /// 1. Above the cursor, the two heaps agree word for word.
  (forall (p: hp_addr). U64.v p >= U64.v start /\
                        U64.v p + U64.v mword <= heap_size ==>
     read_word g p == read_word g0 p) /\
  /// 2. The cursor is a walk position of both heaps.
  walk_visits g zero_addr start /\
  walk_visits g0 zero_addr start /\
  /// 3. The remaining walk is the same in both heaps.
  objects start g == objs /\
  /// 4. Every white object of `g0` already passed is still a white object of
  ///    `g`, with the same size.
  (forall (x: obj_addr).
     Seq.mem x (objects zero_addr g0) /\ is_white x g0 /\
     U64.v (hd_address x) < U64.v start ==>
     Seq.mem x (objects zero_addr g) /\ is_white x g /\
     wosize_of_object x g == wosize_of_object x g0) /\
  /// 5. The pending run contains no white object of `g`.  Runs are built from
  ///    blue objects only, so this is true; it is not derivable from the
  ///    clauses above, and `flush_preserves_white` needs it.
  (run_words > 0 ==>
    (forall (y: obj_addr).
       Seq.mem y (objects zero_addr g) /\ is_white y g /\
       U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
       U64.v (hd_address y) < U64.v start ==> False)) /\
  /// 6. "H-reachability": the pending run's floor is itself a walk position
  ///    of `g`.  When a run starts, `first_blue` is the object at `start`,
  ///    whose floor *is* `start`, and clause 2 already gives `walk_visits g
  ///    zero_addr start`; when a run extends, the floor doesn't move and the
  ///    blue case writes nothing to `g`.  Needed by `flush_white_transfer`/
  ///    `flush_density_transfer` (and hence the induction itself) to route
  ///    around the gap documented for `flush_preserves_white`/`density`.
  (run_words > 0 ==>
    walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)))

/// ---------------------------------------------------------------------------
/// What the flush does
/// ---------------------------------------------------------------------------
///
/// `run_end` is a `nat`, not an `hp_addr`: a run can end exactly at
/// `heap_size`, which is not a valid address.  In all three the run occupies
/// `[first_blue - mword, run_end)`, so every write lands strictly below
/// `run_end`.

/// The run's geometry, shared by the three statements below.
let run_at (first_blue: U64.t) (run_words: nat) (run_end: nat) : prop =
  run_words > 0 ==>
    (U64.v first_blue >= U64.v mword /\
     U64.v first_blue < heap_size /\
     U64.v first_blue % U64.v mword == 0 /\
     U64.v first_blue - U64.v mword + run_words * U64.v mword == run_end)

/// Two heaps that agree word-for-word at every position at or above `bound`
/// produce identical object walks from any starting point at or above
/// `bound`.  Pure write-locality: `objects` only ever reads the header at its
/// current cursor, and the cursor only moves forward.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec objects_agree_above (g g1: heap) (s: hp_addr) (bound: nat)
  : Lemma
    (requires
      U64.v s >= bound /\
      (forall (q: hp_addr). U64.v q >= bound /\ U64.v q + U64.v mword <= heap_size ==>
         read_word g1 q == read_word g q))
    (ensures objects s g1 == objects s g)
    (decreases (heap_size - U64.v s))
  = if U64.v s + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      if next_nat > heap_size || next_nat >= pow2 64 then ()
      else if next_nat >= heap_size then ()
      else begin
        aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
        objects_agree_above g g1 (mk_hp_addr next_nat) bound
      end
    end
#pop-options

/// The flush leaves the heap at and above `run_end` unchanged, word for word,
/// and hence leaves the walk there unchanged too.
///
/// Carries clauses 1 and 3 of the invariant across the white case.
val flush_preserves_walk
  (g: heap) (run_end: nat) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\ run_end <= heap_size /\
      run_at first_blue run_words run_end)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       Seq.length g1 == heap_size /\
       (forall (p: hp_addr). U64.v p >= run_end /\
                             U64.v p + U64.v mword <= heap_size ==>
          read_word g1 p == read_word g p) /\
       (forall (s: hp_addr). U64.v s >= run_end ==>
          objects s g1 == objects s g)))

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let flush_preserves_walk g run_end first_blue run_words fp =
  let g1 = fst (flush_blue g first_blue run_words fp) in
  let outside (p: hp_addr)
    : Lemma
      (requires U64.v p >= run_end /\ U64.v p + U64.v mword <= heap_size)
      (ensures read_word g1 p == read_word g p)
    = flush_blue_preserves_outside g first_blue run_words fp p
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires outside);
  let walks (s: hp_addr)
    : Lemma
      (requires U64.v s >= run_end)
      (ensures objects s g1 == objects s g)
    = objects_agree_above g g1 s run_end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires walks)
#pop-options

/// Membership in a walk started at `s` implies the walk from `s` actually
/// visits the member's header position.  Purely structural: `objects` and
/// `walk_visits` share the same recursion, so this is the membership analogue
/// of `objects_addresses_gt_start`.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec objects_mem_implies_walk_visits (g: heap) (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires Seq.mem y (objects s g))
    (ensures walk_visits g s (hd_address y))
    (decreases (heap_size - U64.v s))
  = objects_nonempty_next s g;
    f_address_spec s;
    let obj = f_address s in
    if y = obj then begin
      hd_address_bounds y;
      hd_f_roundtrip s
    end else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      if next_nat >= heap_size then
        mem_cons_lemma y obj Seq.empty
      else begin
        let next = mk_hp_addr next_nat in
        mem_cons_lemma y obj (objects next g);
        objects_mem_implies_walk_visits g next y
      end
    end
#pop-options

/// Membership below the run transfers across the flush: if `y`'s header lies
/// strictly below `first_blue - mword`, and the walk from `s <= hd_address y`
/// reaches `y`, then the flushed heap's walk from `s` reaches `y` too.  The
/// entire path from `s` to `y` lies below the write range, so reads agree at
/// every step (`flush_blue_preserves_outside`) and the two walks step in
/// lockstep all the way to `y`.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec flush_membership_below
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v s <= U64.v (hd_address y) /\
      U64.v (hd_address y) < U64.v first_blue - U64.v mword /\
      Seq.mem y (objects s g))
    (ensures Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (decreases (Seq.length (objects s g)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    objects_nonempty_next s g;
    f_address_spec s;
    hd_address_spec y;
    let obj = f_address s in
    flush_blue_preserves_outside g first_blue run_words fp s;
    objects_nonempty_next s g1;
    if U64.v s = U64.v (hd_address y) then begin
      hd_address_bounds y;
      hd_f_roundtrip s;
      mem_cons_lemma y obj Seq.empty
    end else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      if next_nat >= heap_size then
        mem_cons_lemma y obj Seq.empty
      else begin
        let next = mk_hp_addr next_nat in
        mem_cons_lemma y obj (objects next g);
        objects_addresses_gt_start next g y;
        flush_membership_below g first_blue run_words fp next y;
        mem_cons_lemma y obj (objects next g1)
      end
    end
#pop-options

/// Mirror of `flush_membership_below`: membership below the run transfers
/// the other way, from the flushed heap back to the original.  Same proof,
/// `g` and `g1` exchanged (`flush_blue_preserves_outside`'s conclusion is a
/// plain equality, symmetric in use).
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec flush_membership_below_rev
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  (s: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      U64.v s <= U64.v (hd_address y) /\
      U64.v (hd_address y) < U64.v first_blue - U64.v mword /\
      Seq.mem y (objects s (fst (flush_blue g first_blue run_words fp))))
    (ensures Seq.mem y (objects s g))
    (decreases (Seq.length (objects s (fst (flush_blue g first_blue run_words fp)))))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    objects_nonempty_next s g1;
    f_address_spec s;
    hd_address_spec y;
    let obj = f_address s in
    flush_blue_preserves_outside g first_blue run_words fp s;
    objects_nonempty_next s g;
    if U64.v s = U64.v (hd_address y) then begin
      hd_address_bounds y;
      hd_f_roundtrip s;
      mem_cons_lemma y obj Seq.empty
    end else begin
      let wz = getWosize (read_word g1 s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      if next_nat >= heap_size then
        mem_cons_lemma y obj Seq.empty
      else begin
        let next = mk_hp_addr next_nat in
        mem_cons_lemma y obj (objects next g1);
        objects_addresses_gt_start next g1 y;
        flush_membership_below_rev g first_blue run_words fp next y;
        mem_cons_lemma y obj (objects next g)
      end
    end
#pop-options
/// The cursor advances to the next walk position.
val walk_visits_step (g: heap) (s p q: hp_addr)
  : Lemma (requires walk_visits g s p /\ Seq.length (objects p g) > 0 /\
                    U64.v q == U64.v p +
                      (U64.v (getWosize (read_word g p)) + 1) * U64.v mword /\
                    U64.v q < heap_size)
          (ensures walk_visits g s q)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec walk_visits_step g s p q
  : Lemma (requires walk_visits g s p /\ Seq.length (objects p g) > 0 /\
                    U64.v q == U64.v p +
                      (U64.v (getWosize (read_word g p)) + 1) * U64.v mword /\
                    U64.v q < heap_size)
          (ensures walk_visits g s q)
          (decreases (heap_size - U64.v s))
  = let wz_p = getWosize (read_word g p) in
    aligned_plus_mul8 (U64.v p) (U64.v wz_p + 1);
    if U64.v s = U64.v p then ()
    else begin
      walk_visits_above g s p;
      let wz = getWosize (read_word g s) in
      let next = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      walk_visits_step g (mk_hp_addr next) p q
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Corrected white/density transfer, for internal use only
/// ---------------------------------------------------------------------------
///
/// `flush_preserves_white` and `flush_preserves_density` above are not
/// provable as stated (see NOTES.md).  What *is* true, and is what
/// `coalesce_aux_preserves_white`'s own induction actually has on hand, is
/// the same statement plus one extra fact that only the induction (not a
/// standalone lemma about an arbitrary heap) can supply: that the walk from
/// `zero_addr` reaches `first_blue - mword` -- i.e. that the run is not just
/// arithmetic, but genuinely starts where a real object of `g` begins.  The
/// lemmas below take that fact as an explicit extra hypothesis and are
/// completely proved.

/// Append membership, the general form of `mem_cons_lemma`.
let mem_append_lemma (#a: eqtype) (x: a) (lo hi: Seq.seq a)
  : Lemma (Seq.mem x (Seq.append lo hi) <==> Seq.mem x lo \/ Seq.mem x hi)
  = Seq.Properties.lemma_append_count lo hi

/// Two heaps that agree at every position below `bound` have the same walk
/// reachability below `bound`: if the walk from `s <= bound` reaches `bound`
/// in one heap, it reaches `bound` in the other.  Mirrors `objects_agree_above`
/// (which handles positions *above* a bound) for the below-a-bound case.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_visits_agree_below (g g1: heap) (s bound: hp_addr)
  : Lemma
    (requires
      U64.v s <= U64.v bound /\
      (forall (q: hp_addr). U64.v q + U64.v mword <= U64.v bound ==>
         read_word g1 q == read_word g q) /\
      walk_visits g s bound)
    (ensures walk_visits g1 s bound)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v bound then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      walk_visits_above g next bound;
      walk_visits_agree_below g g1 next bound
    end
#pop-options

/// `objects p g`'s nonemptiness (as opposed to its full structure) depends
/// only on the single header word at `p`: whether there is room for it, and
/// whether its wosize overflows past the end of the heap.  So agreement at
/// `p` alone -- not agreement everywhere `objects` subsequently reads --
/// already transfers nonemptiness.
let objects_nonempty_transfers (g g1: heap) (p: hp_addr)
  : Lemma
    (requires read_word g1 p == read_word g p /\ Seq.length (objects p g) > 0)
    (ensures Seq.length (objects p g1) > 0)
  = ()

/// Given that `g`'s own walk from `zero_addr` reaches exactly
/// `first_blue - mword` (the run's start), the flushed heap's walk reaches
/// `re` (`run_end`) too: below the run start the two heaps agree, so the walk
/// gets there the same way; from there, the flushed heap's own header -- the
/// fresh merged one -- takes it straight to `re` in one step.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let flush_reaches_run_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)))
    (ensures walk_visits (fst (flush_blue g first_blue run_words fp)) zero_addr re)
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    walk_visits_above g zero_addr h;
    walk_visits_agree_below g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    walk_visits_step g1 zero_addr h re
#pop-options

/// The flushed heap's `zero_addr`-membership above the run agrees exactly
/// with the original heap's, given that both `first_blue - mword` and `re`
/// (`run_end`) are genuinely reached by `g`'s own walk from `zero_addr`.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_membership_above_run_iff
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re /\
      U64.v (hd_address y) >= U64.v re)
    (ensures
      (Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp))) <==>
       Seq.mem y (objects zero_addr g)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    flush_reaches_run_end g first_blue run_words fp re;
    flush_preserves_walk g (U64.v re) first_blue run_words fp;
    objects_split_from g zero_addr re;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects re g) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v re) /\
        (forall (z: obj_addr). Seq.mem z (objects re g) ==> U64.v (hd_address z) >= U64.v re)
    with begin
      objects_split_from g1 zero_addr re;
      eliminate exists (pre1: seq obj_addr).
          objects zero_addr g1 == Seq.append pre1 (objects re g1) /\
          (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v re) /\
          (forall (z: obj_addr). Seq.mem z (objects re g1) ==> U64.v (hd_address z) >= U64.v re)
      with begin
        mem_append_lemma y pre (objects re g);
        mem_append_lemma y pre1 (objects re g1)
      end
    end
#pop-options

/// The corrected `flush_preserves_white`: same conclusion, with the one
/// extra hypothesis that makes it true (see the section comment above).
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_white_transfer
  (g: heap) (re: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re /\
      (forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g /\
         U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
         U64.v (hd_address y) < U64.v re ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g ==>
         Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
         wosize_of_object y g1 == wosize_of_object y g))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let aux (y: obj_addr)
      : Lemma
        (requires Seq.mem y (objects zero_addr g) /\ is_white y g)
        (ensures
          Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
          wosize_of_object y g1 == wosize_of_object y g)
      = (if U64.v (hd_address y) < U64.v first_blue - U64.v mword then begin
           objects_addresses_gt_start zero_addr g y;
           hd_address_spec y;
           flush_membership_below g first_blue run_words fp zero_addr y
         end
         else if U64.v (hd_address y) < U64.v re then ()
         else
           flush_membership_above_run_iff g first_blue run_words fp re y);
        flush_blue_preserves_outside g first_blue run_words fp (hd_address y);
        is_white_iff y g; is_white_iff y g1;
        color_of_object_spec y g; color_of_object_spec y g1;
        wosize_of_object_spec y g; wosize_of_object_spec y g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// The flushed heap's walk from the run start unfolds to exactly one cons:
/// `first_blue` itself, then straight on to `re`.  Isolated as its own fact
/// (rather than inlined) so later proofs can use it without re-deriving the
/// header/wosize arithmetic each time.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let flush_h_decompose
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       walk_visits g1 zero_addr (hd_address (first_blue <: obj_addr)) /\
       objects (hd_address (first_blue <: obj_addr)) g1 ==
       Seq.cons (first_blue <: obj_addr) (objects re g1)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    walk_visits_above g zero_addr h;
    walk_visits_agree_below g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    f_hd_roundtrip fb;
    objects_nonempty_next h g1
#pop-options

/// `first_blue` itself is a member of the flushed heap's walk, given
/// H-reachability.  Shared by `flush_no_interior_member`'s edge case and
/// `flush_density_transfer`'s "lands exactly on H" case.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_h_is_member
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)))
    (ensures
      Seq.mem (first_blue <: obj_addr) (objects zero_addr (fst (flush_blue g first_blue run_words fp))))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    flush_h_decompose g first_blue run_words fp re;
    mem_cons_lemma fb fb (objects re g1);
    objects_split_from g1 zero_addr h;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h) /\
        (forall (z: obj_addr). Seq.mem z (objects h g1) ==> U64.v (hd_address z) >= U64.v h)
    with begin
      mem_append_lemma fb pre (objects h g1)
    end
#pop-options

/// No position strictly between `first_blue - mword` and `re` is ever a
/// member of the flushed heap's walk: the merged header takes the walk
/// straight from `H` to `re` in one step.
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let flush_no_interior_member
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr) (y: obj_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      U64.v (hd_address y) > U64.v (hd_address (first_blue <: obj_addr)) /\
      U64.v (hd_address y) < U64.v re)
    (ensures ~(Seq.mem y (objects zero_addr (fst (flush_blue g first_blue run_words fp)))))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    flush_h_decompose g first_blue run_words fp re;
    if Seq.mem y (objects zero_addr g1) then begin
      objects_split_from g1 zero_addr h;
      eliminate exists (pre: seq obj_addr).
          objects zero_addr g1 == Seq.append pre (objects h g1) /\
          (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h) /\
          (forall (z: obj_addr). Seq.mem z (objects h g1) ==> U64.v (hd_address z) >= U64.v h)
      with begin
        mem_append_lemma y pre (objects h g1);
        mem_cons_lemma y fb (objects re g1);
        hd_address_spec y;
        if y = fb then ()
        else if Seq.mem y (objects re g1) then objects_addresses_gt_start re g1 y
      end
    end
#pop-options

/// If the walk from `zero_addr` reaches both `start` and `bound`, with
/// `start <= bound`, it reaches `bound` starting from `start` too: the walk
/// is a single deterministic sequence, so reaching both means reaching one
/// from the other.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_visits_prefix_gen (g: heap) (s start bound: hp_addr)
  : Lemma
    (requires
      U64.v s <= U64.v start /\ U64.v start <= U64.v bound /\
      walk_visits g s start /\ walk_visits g s bound)
    (ensures walk_visits g start bound)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v start then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      walk_visits_above g next start;
      walk_visits_prefix_gen g next start bound
    end
#pop-options

let walk_visits_prefix (g: heap) (start bound: hp_addr)
  : Lemma
    (requires
      walk_visits g zero_addr start /\ walk_visits g zero_addr bound /\
      U64.v start <= U64.v bound)
    (ensures walk_visits g start bound)
  = walk_visits_above g zero_addr start;
    walk_visits_prefix_gen g zero_addr start bound

/// A walk position's next position never overshoots a target the walk
/// (from that position) is known to reach.
let walk_visits_next_bound (g: heap) (start bound: hp_addr)
  : Lemma
    (requires U64.v start < U64.v bound /\ walk_visits g start bound)
    (ensures
      (let wz = getWosize (read_word g start) in
       U64.v start + (U64.v wz + 1) * 8 <= U64.v bound))
  = let wz = getWosize (read_word g start) in
    let next_nat = U64.v start + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
    let next = mk_hp_addr next_nat in
    walk_visits_above g next bound

/// A position the walk from `zero_addr` reaches, with room for a header, is
/// never a dead end: density (plus the heap being nonempty to begin with)
/// carries the walk's own "doesn't stop early" property all the way from
/// `zero_addr` to any such position.  Needed because `walk_visits` only
/// records that the walk *reaches* a position, not that it *continues*
/// there -- that extra step is exactly what `SI.heap_objects_dense` supplies,
/// one hop at a time.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_visits_dense_continues (g: heap) (s p: hp_addr)
  : Lemma
    (requires
      SI.heap_objects_dense g /\ walk_visits g s p /\
      Seq.length (objects s g) > 0 /\
      Seq.mem (f_address s) (objects zero_addr g) /\
      U64.v p + 8 < heap_size)
    (ensures Seq.length (objects p g) > 0)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v p then ()
    else begin
      SI.objects_dense_step s g;
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      if U64.v next + 8 < heap_size then begin
        SI.objects_dense_obj_in s g;
        SI.obj_in_objects_elim (U64.uint_to_t (next_nat + 8)) g;
        f_address_spec next;
        walk_visits_dense_continues g next p
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Density via `walk_end`: the scalar route
/// ---------------------------------------------------------------------------
///
/// The earlier attempt at `flush_density_transfer` went straight at
/// `SI.heap_objects_dense`'s quantified form -- for every walk position with
/// room, show the walk continues -- and got stuck exactly where `flush_preserves_white`
/// did: transferring a single position's own nonemptiness across the flush.
/// `GC.Spec.WalkEnd` gives a scalar restatement of density (`walk_end g
/// zero_addr` is *the* address where the whole-heap walk stops) and a pair of
/// bridging lemmas (`walk_end_of_dense_top`, `dense_from_walk_end`), so the
/// job reduces to showing the flush doesn't move that one number.  That's
/// what's done below: `flush_preserves_walk_end` is the only real content;
/// `flush_density_transfer` is three lines around it.

/// Membership in a walk between two points already visited: if the walk
/// visits `a` starting from `s`, its ultimate stopping point from `s` is the
/// same as from `a` -- `a` is just an intermediate checkpoint. Unconditional,
/// no heap-agreement hypotheses needed: `walk_visits` and `walk_end` share
/// the same recursive step, so visiting `a` en route doesn't change where
/// the walk eventually halts.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_end_agree_on_visit (g: heap) (s a: hp_addr)
  : Lemma
    (requires walk_visits g s a)
    (ensures WE.walk_end g s == WE.walk_end g a)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v a then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      walk_end_agree_on_visit g next a
    end
#pop-options

/// Two heaps that agree at every position at or above `bound` have the same
/// `walk_end` from any starting point at or above `bound`.  Mirrors
/// `objects_agree_above`.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec walk_end_agree_above (g g1: heap) (s: hp_addr) (bound: nat)
  : Lemma
    (requires
      U64.v s >= bound /\
      (forall (q: hp_addr). U64.v q >= bound /\ U64.v q + U64.v mword <= heap_size ==>
         read_word g1 q == read_word g q))
    (ensures WE.walk_end g1 s == WE.walk_end g s)
    (decreases (heap_size - U64.v s))
  = if U64.v s + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      if next_nat > heap_size || next_nat >= pow2 64 then ()
      else if next_nat >= heap_size then ()
      else begin
        aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
        walk_end_agree_above g g1 (mk_hp_addr next_nat) bound
      end
    end
#pop-options

/// The flush leaves `walk_end` from `zero_addr` exactly where it was.  Below
/// the run, the two heaps agree, so the walk gets to `H` the same way in
/// both; from `H`, the flushed heap's one merged block covers exactly the
/// same ground -- `run_words` words -- as however many blocks the run held
/// in the original, so both heaps' walks resume at the same place, `re`;
/// above `re` the heaps agree again.  `H`- and `re`-reachability (from
/// `zero_addr`, in the original heap) are the same two extra facts
/// `flush_white_transfer` needed and for the same reason: they are what ties
/// `first_blue`/`run_words` to the heap's real layout, which
/// `SI.heap_objects_dense` alone does not supply.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let flush_preserves_walk_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t) (re: hp_addr)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re)
    (ensures WE.walk_end (fst (flush_blue g first_blue run_words fp)) zero_addr == WE.walk_end g zero_addr)
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    walk_visits_above g zero_addr h;
    walk_visits_agree_below g g1 zero_addr h;
    walk_end_agree_on_visit g zero_addr h;
    walk_end_agree_on_visit g1 zero_addr h;
    walk_visits_prefix g h re;
    walk_end_agree_on_visit g h re;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    let above (q: hp_addr)
      : Lemma
        (requires U64.v q >= U64.v re)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires above);
    walk_end_agree_above g g1 re (U64.v re)
#pop-options

/// The corrected `flush_preserves_density`: same extra hypotheses as
/// `flush_white_transfer`, plus the heap being nonempty to begin with (needed
/// by `dense_from_walk_end`).  `walk_end_of_dense_top` turns density(`g`)
/// into a scalar fact, `flush_preserves_walk_end` carries that scalar fact
/// across the flush unchanged, and `dense_from_walk_end` turns it back into
/// density(`g1`).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let flush_density_transfer
  (g: heap) (re: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v re /\
      SI.heap_objects_dense g /\
      Seq.length (objects zero_addr g) > 0 /\
      walk_visits g zero_addr (hd_address (first_blue <: obj_addr)) /\
      walk_visits g zero_addr re)
    (ensures SI.heap_objects_dense (fst (flush_blue g first_blue run_words fp)))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let h = hd_address (first_blue <: obj_addr) in
    hd_address_spec (first_blue <: obj_addr);
    WE.walk_end_of_dense_top g;
    flush_preserves_walk_end g first_blue run_words fp re;
    (if U64.v zero_addr < U64.v h then begin
       flush_blue_preserves_outside g first_blue run_words fp zero_addr;
       objects_nonempty_transfers g g1 zero_addr
     end else
       flush_h_decompose g first_blue run_words fp re);
    WE.dense_from_walk_end g1
#pop-options

/// `flush_white_transfer`'s edge case: the run runs all the way to the end of
/// the heap.  No H-reachability needed at all -- there is nothing above the
/// run to worry about, so every white object is simply below it, and
/// `flush_membership_below` (which never needed the extra hypothesis) does
/// the whole job.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let flush_white_transfer_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      (forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g /\
         U64.v (hd_address y) >= U64.v first_blue - U64.v mword ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g ==>
         Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
         wosize_of_object y g1 == wosize_of_object y g))
  = let g1 = fst (flush_blue g first_blue run_words fp) in
    let aux (y: obj_addr)
      : Lemma
        (requires Seq.mem y (objects zero_addr g) /\ is_white y g)
        (ensures
          Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
          wosize_of_object y g1 == wosize_of_object y g)
      = objects_addresses_gt_start zero_addr g y;
        hd_address_spec y;
        flush_membership_below g first_blue run_words fp zero_addr y;
        flush_blue_preserves_outside g first_blue run_words fp (hd_address y);
        is_white_iff y g; is_white_iff y g1;
        color_of_object_spec y g; color_of_object_spec y g1;
        wosize_of_object_spec y g; wosize_of_object_spec y g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// White preservation: the induction
/// ---------------------------------------------------------------------------

val coalesce_aux_preserves_white
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires white_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g0) /\ is_white x g0 ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g0))
    (decreases Seq.length objs)

/// If two heaps agree at `y`'s header word, `y`'s color and wosize agree
/// between them too -- both are read straight from that word.  Written once
/// because this exact conversion (word equality -> color/size equality, via
/// `is_white_iff`/`is_blue_iff`/`color_of_object_spec`/`wosize_of_object_spec`)
/// was being hand-written at every call site that needed it below, and was
/// missing at least one of its pieces at more than one of them.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let header_agree_transfers (g g': heap) (y: obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      read_word g (hd_address y) == read_word g' (hd_address y))
    (ensures
      (is_white y g <==> is_white y g') /\
      (is_blue y g <==> is_blue y g') /\
      wosize_of_object y g == wosize_of_object y g')
  = color_of_object_spec y g;
    color_of_object_spec y g';
    is_white_iff y g;
    is_white_iff y g';
    is_blue_iff y g;
    is_blue_iff y g';
    wosize_of_object_spec y g;
    wosize_of_object_spec y g'
#pop-options

/// If `y` is on the walk from `lo`, then `lo <= hd_address y`: two
/// `mword`-aligned addresses that differ at all differ by a whole word.
/// General and independent of `white_inv` -- usable with `lo = zero_addr` or
/// `lo = nxt` alike.  Pulled out as its own lemma because the same
/// three-line arithmetic argument was being re-derived by hand at several
/// call sites below and got the wrong lemma (`hd_address_bounds`, an upper
/// bound, instead of `hd_address_spec`, the exact equation) more than once.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let mem_from_le_hd_address (lo: hp_addr) (g: heap) (y: obj_addr)
  : Lemma
    (requires Seq.mem y (objects lo g))
    (ensures U64.v lo <= U64.v (hd_address y))
  = objects_addresses_gt_start lo g y;
    hd_address_spec y;
    assert (U64.v y % U64.v mword == 0);
    assert (U64.v lo % U64.v mword == 0);
    FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v y) (U64.v lo) (U64.v mword);
    assert ((U64.v y - U64.v lo) % U64.v mword == 0);
    assert (U64.v y - U64.v lo >= U64.v mword)
#pop-options

/// The consequences of `white_inv` that every one of the four blue/white x
/// top/continuing case lemmas below needs.  Extracted into one place after
/// each kept re-deriving these independently and kept independently
/// forgetting one: `caw_top_white` lacked a conjunct `caw_top_blue` had,
/// `caw_top`'s blue branch lacked a case split its white branch had, and
/// `first_blue % mword == 0` went missing from three call sites at once.
let caw_shared_facts (g0 g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: nat) : prop =
  (run_words > 0 ==>
     U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
     U64.v first_blue % U64.v mword == 0 /\
     U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
     walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword))) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
     U64.v zero_addr <= U64.v (hd_address y)) /\
  (forall (w: obj_addr).
     Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
     U64.v (hd_address w) < U64.v start ==>
     Seq.mem w (objects zero_addr g) /\ is_white w g /\
     wosize_of_object w g == wosize_of_object w g0) /\
  (run_words > 0 ==>
     (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_white y g /\
        U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
        U64.v (hd_address y) < U64.v start ==> False))

/// Establishes `caw_shared_facts` from `white_inv`, in the one place
/// (`white_inv`'s own clauses, directly available where this is called)
/// where each piece is genuinely primitive.  Called as the first line of
/// `caw_empty`, `caw_top`, `caw_blue_head` and `caw_white_head` -- the only
/// four places that actually have `white_inv` in scope.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let caw_unpack_white_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : Lemma
    (requires white_inv g0 g start objs first_blue run_words all_objs)
    (ensures caw_shared_facts g0 g start first_blue run_words)
  = let alignment (y: obj_addr)
      : Lemma
        (requires Seq.mem y (objects zero_addr g))
        (ensures U64.v zero_addr <= U64.v (hd_address y))
      = mem_from_le_hd_address zero_addr g y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires alignment)
#pop-options

/// Empty case (`objs` empty): every `g0`-global white object has `hd < start`
/// (`objs == objects start g0 == Seq.empty`, so `objects_split_from` puts the
/// whole global list below `start`), so clause 4 already carries it to `g`;
/// `flush_white_transfer` carries it on to the flushed heap (vacuously, if
/// `run_words = 0`, since the flush is then the identity).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      (let g' = fst (flush_blue g first_blue run_words fp) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g0) /\ is_white x g0 ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g0))
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    Seq.lemma_eq_elim objs Seq.empty;
    objects_split_from g0 zero_addr start;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g0 == Seq.append pre (objects start g0) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g0) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      (if run_words > 0 then begin
         run_words_bound first_blue run_words start;
         h_addr_agree first_blue;
         flush_white_transfer g start first_blue run_words fp
       end);
      let final (x: obj_addr)
        : Lemma
          (requires Seq.mem x (objects zero_addr g0) /\ is_white x g0)
          (ensures
            Seq.mem x (objects zero_addr (fst (flush_blue g first_blue run_words fp))) /\
            is_white x (fst (flush_blue g first_blue run_words fp)) /\
            wosize_of_object x (fst (flush_blue g first_blue run_words fp)) ==
              wosize_of_object x g0)
        = mem_append_lemma x pre (objects start g0)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires final)
    end
#pop-options

/// The shared "clause 5" step: extending a pending run by one more blue
/// object `x` (header at `start`) keeps it white-free, up to any bound `hi`
/// for which `x` is known to be the only `g`-object with header in
/// `[start, hi)`.  Used by both places a run gets extended and then
/// immediately flushed: the heap-top case (`hi = heap_size`) and the
/// ordinary continuing-run case (`hi = nxt`, the next cursor).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_extend_run_white_free
  (g0 g: heap) (start: hp_addr) (x: obj_addr) (hi: nat)
  (first_blue fb': U64.t) (run_words: nat)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      hd_address x == start /\ is_blue x g0 /\
      (forall (p: hp_addr). U64.v p >= U64.v start /\ U64.v p + U64.v mword <= heap_size ==>
         read_word g p == read_word g0 p) /\
      (forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\
         U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < hi ==> y == x) /\
      (run_words > 0 ==> U64.v first_blue >= U64.v mword) /\
      (run_words > 0 ==>
        (forall (y: obj_addr).
           Seq.mem y (objects zero_addr g) /\ is_white y g /\
           U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
           U64.v (hd_address y) < U64.v start ==> False)) /\
      fb' == (if run_words = 0 then x else first_blue))
    (ensures
      forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_white y g /\
        U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
        U64.v (hd_address y) < hi ==> False)
  = let no_white (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\ is_white y g /\
          U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
          U64.v (hd_address y) < hi)
        (ensures False)
      = if U64.v (hd_address y) < U64.v start then begin
          if run_words = 0 then begin
            assert (fb' == x);
            hd_address_spec x
            // fb' - mword == start here, contradicting hd_address y < start
            // together with hd_address y >= fb' - mword.
          end else ()
          // fb' == first_blue here; hd_address y >= first_blue - mword and
          // < start is exactly the old clause 5, giving False directly.
        end
        else begin
          // start <= hd_address y < hi: `x` is the only such object, so
          // y = x, which is blue in g0 hence blue in g (read agreement at
          // `start`), contradicting is_white y g.
          assert (y == x);
          hd_address_bounds x;
          assert (read_word g start == read_word g0 start);
          header_agree_transfers g0 g x;
          assert (is_blue x g);
          is_blue_iff x g;
          is_white_iff x g
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires no_white)
#pop-options

/// Top-of-heap, `x` blue: the run absorbs `x` and ends exactly at the top of
/// the heap.  `x` is the only object at or above `start` (the walk is a
/// singleton there), so `caw_extend_run_white_free` with `hi = heap_size`
/// gives the "no white in the extended run" fact `flush_white_transfer_at_end`
/// needs.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_top_blue
  (g0 g: heap) (start: hp_addr) (x: obj_addr)
  (first_blue fb': U64.t) (run_words rw': nat) (fp: U64.t)
  : Lemma
    (requires
      rw' > 0 /\
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      hd_address x == start /\ is_blue x g0 /\
      objects start g == Seq.cons x Seq.empty /\
      (forall (p: hp_addr). U64.v p >= U64.v start /\ U64.v p + U64.v mword <= heap_size ==>
         read_word g p == read_word g0 p) /\
      walk_visits g0 zero_addr start /\ walk_visits g zero_addr start /\
      (run_words > 0 ==> U64.v first_blue >= U64.v mword) /\
      (run_words > 0 ==> U64.v first_blue < heap_size) /\
      (run_words > 0 ==>
        (forall (y: obj_addr).
           Seq.mem y (objects zero_addr g) /\ is_white y g /\
           U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
           U64.v (hd_address y) < U64.v start ==> False)) /\
      fb' == (if run_words = 0 then x else first_blue) /\
      U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size)
    (ensures
      (let g1 = fst (flush_blue g fb' rw' fp) in
       forall (y: obj_addr).
         Seq.mem y (objects zero_addr g) /\ is_white y g ==>
         Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
         wosize_of_object y g1 == wosize_of_object y g))
  = run_words_bound_top fb' rw';
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\ U64.v (hd_address y) >= U64.v start)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x Seq.empty
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x heap_size first_blue fb' run_words;
    flush_white_transfer_at_end g fb' rw' fp
#pop-options

/// Top-of-heap, `x` white: flush whatever run was pending (ending exactly at
/// `start`, unaffecting `x` itself, whose header is untouched throughout),
/// then handle `x` -- unaffected by the flush -- and everything below
/// `start` -- carried by clause 4 then `flush_white_transfer` -- separately.
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
private let caw_top_white
  (g0 g g1: heap) (start: hp_addr) (x: obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      (g1, ()) == (fst (flush_blue g first_blue run_words fp), ()) /\
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      hd_address x == start /\ ~(is_blue x g0) /\
      objects start g0 == Seq.cons x Seq.empty /\
      (forall (p: hp_addr). U64.v p >= U64.v start /\ U64.v p + U64.v mword <= heap_size ==>
         read_word g p == read_word g0 p) /\
      walk_visits g0 zero_addr start /\ walk_visits g zero_addr start /\
      run_at first_blue run_words (U64.v start) /\
      (run_words > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword))) /\
      (run_words > 0 ==>
        (forall (y: obj_addr).
           Seq.mem y (objects zero_addr g) /\ is_white y g /\
           U64.v (hd_address y) >= U64.v first_blue - U64.v mword /\
           U64.v (hd_address y) < U64.v start ==> False)) /\
      (forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 /\
         U64.v (hd_address z) < U64.v start ==>
         Seq.mem z (objects zero_addr g) /\ is_white z g /\
         wosize_of_object z g == wosize_of_object z g0))
    (ensures
      forall (z: obj_addr).
        Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
        Seq.mem z (objects zero_addr g1) /\ is_white z g1 /\
        wosize_of_object z g1 == wosize_of_object z g0)
  = flush_preserves_walk g (U64.v start) first_blue run_words fp;
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start
     end);
    objects_agree_above g0 g start (U64.v start);
    objects_split_from g1 zero_addr start;
    eliminate exists (pre1: seq obj_addr).
        objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
        (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      objects_split_from g0 zero_addr start;
      eliminate exists (pre0: seq obj_addr).
          objects zero_addr g0 == Seq.append pre0 (objects start g0) /\
          (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g0) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        let final (z: obj_addr)
          : Lemma
            (requires Seq.mem z (objects zero_addr g0) /\ is_white z g0)
            (ensures
              Seq.mem z (objects zero_addr g1) /\ is_white z g1 /\
              wosize_of_object z g1 == wosize_of_object z g0)
          = mem_append_lemma z pre0 (objects start g0);
            if U64.v (hd_address z) < U64.v start then begin
              // Clause 4 carries z into g.  If a run is pending, clause 5
              // rules out z's header falling inside it (z is white), so z
              // sits strictly below the run's floor and
              // `flush_membership_below` carries it on into g1 untouched.
              if run_words = 0 then ()
              else begin
                assert (U64.v (hd_address z) < U64.v first_blue - U64.v mword);
                objects_addresses_gt_start zero_addr g z;
                hd_address_bounds z;
                hd_address_spec z;
                // z and zero_addr are both mword-aligned and z > zero_addr,
                // so their difference is a positive multiple of mword, hence
                // at least one whole word: zero_addr <= z - mword = hd_address z.
                assert (U64.v z % U64.v mword == 0);
                assert (U64.v zero_addr % U64.v mword == 0);
                FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v z) (U64.v zero_addr) (U64.v mword);
                assert ((U64.v z - U64.v zero_addr) % U64.v mword == 0);
                assert (U64.v z - U64.v zero_addr >= U64.v mword);
                assert (U64.v zero_addr <= U64.v (hd_address z));
                objects_mem_implies_walk_visits g zero_addr z;
                flush_membership_below g first_blue run_words fp zero_addr z;
                flush_blue_preserves_outside g first_blue run_words fp (hd_address z);
                header_agree_transfers g g1 z;
                assert (Seq.mem z (objects zero_addr g1));
                assert (is_white z g1);
                assert (wosize_of_object z g1 == wosize_of_object z g0)
              end
            end
            else begin
              // z = x: not part of any run, its header is untouched all the
              // way from g0 through g to g1.
              mem_cons_lemma z x Seq.empty;
              flush_blue_preserves_outside g first_blue run_words fp start;
              mem_append_lemma x pre1 (objects start g1);
              Seq.cons_head_tail (objects start g1);
              mem_cons_lemma x x (Seq.tail (objects start g1));
              assert (read_word g0 (hd_address z) == read_word g1 (hd_address z));
              header_agree_transfers g0 g1 z;
              assert (Seq.mem z (objects zero_addr g1));
              assert (is_white z g1);
              assert (wosize_of_object z g1 == wosize_of_object z g0)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires final)
      end
    end
#pop-options

/// Clause 4, extended from `start` to `nxt` for the blue-continuing step:
/// below `start` it's the old clause 4 (a direct hypothesis here, not
/// buried in an ambient `white_inv`); at/above `start` and below `nxt`, `x`
/// is the only such object (`objects_cons_step_to`'s cons-shape), and it's
/// blue, so `is_white y g0` can't hold there.  A standalone top-level lemma
/// -- not a closure nested inside the much larger `caw_blue_head` proof --
/// so this gets its own small, focused proof context.  Below `start`, the
/// old clause 4 is extracted from its hypothesis via an explicit `eliminate
/// forall ... with y` rather than a bare `assert`, since automatic
/// E-matching was not firing the pattern reliably here.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_clause4_ext_blue
  (g0 g: heap) (start nxt: hp_addr) (x: obj_addr)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      walk_visits g0 zero_addr start /\
      is_blue x g0 /\
      objects start g0 == Seq.cons x (objects nxt g0) /\
      (forall (w: obj_addr).
         Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
         U64.v (hd_address w) < U64.v start ==>
         Seq.mem w (objects zero_addr g) /\ is_white w g /\
         wosize_of_object w g == wosize_of_object w g0))
    (ensures
      forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
        U64.v (hd_address y) < U64.v nxt ==>
        Seq.mem y (objects zero_addr g) /\ is_white y g /\
        wosize_of_object y g == wosize_of_object y g0)
  = let step (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
          U64.v (hd_address y) < U64.v nxt)
        (ensures
          Seq.mem y (objects zero_addr g) /\ is_white y g /\
          wosize_of_object y g == wosize_of_object y g0)
      = if U64.v (hd_address y) < U64.v start then begin
          is_white_iff y g0; color_of_object_spec y g0;
          eliminate forall (w: obj_addr).
              Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
              U64.v (hd_address w) < U64.v start ==>
              Seq.mem w (objects zero_addr g) /\ is_white w g /\
              wosize_of_object w g == wosize_of_object w g0
          with y;
          is_white_iff y g; color_of_object_spec y g
        end
        else begin
          objects_split_from g0 zero_addr start;
          eliminate exists (pre: seq obj_addr).
              objects zero_addr g0 == Seq.append pre (objects start g0) /\
              (forall (w: obj_addr). Seq.mem w pre ==> U64.v (hd_address w) < U64.v start) /\
              (forall (w: obj_addr). Seq.mem w (objects start g0) ==> U64.v (hd_address w) >= U64.v start)
          with begin
            mem_append_lemma y pre (objects start g0);
            mem_cons_lemma y x (objects nxt g0);
            // Rule out y in objects_nxt_g0: that would give hd_address y
            // >= nxt (mem_cons_lemma's second disjunct plus the shared
            // alignment-gap argument), contradicting hd_address y < nxt.
            // So y = x.
            (if not (y = x) then mem_from_le_hd_address nxt g0 y);
            is_white_iff y g0; is_blue_iff x g0;
            color_of_object_spec y g0; color_of_object_spec x g0
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires step)
#pop-options

/// The white-continuing-step analogue of `caw_clause4_ext_blue`: `x` here is
/// white, not blue, so at/above `start` (forced to equal `x`) the object
/// itself must be shown to survive the flush (its header sits below the
/// write range, untouched), rather than being ruled out by contradiction.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_clause4_ext_white
  (g0 g g1: heap) (start nxt: hp_addr) (x: obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      walk_visits g0 zero_addr start /\ walk_visits g1 zero_addr start /\
      caw_shared_facts g0 g start first_blue run_words /\
      read_word g start == read_word g0 start /\
      (g1, ()) == (fst (flush_blue g first_blue run_words fp), ()) /\
      hd_address x == start /\ ~(is_blue x g0) /\
      objects start g0 == Seq.cons x (objects nxt g0) /\
      objects start g1 == Seq.cons x (objects nxt g1))
    (ensures
      forall (y: obj_addr).
        Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
        U64.v (hd_address y) < U64.v nxt ==>
        Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
        wosize_of_object y g1 == wosize_of_object y g0)
  = // Unpack caw_shared_facts into raw, local facts once: the raw forall
    // form is what `eliminate forall` below needs (it looks for a literal
    // hypothesis of that shape in context, not an opaque named `prop` --
    // that was tried and does not work reliably).
    assert (run_words > 0 ==>
              U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
              U64.v first_blue % U64.v mword == 0 /\
              U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start);
    assert (forall (w: obj_addr).
              Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
              U64.v (hd_address w) < U64.v start ==>
              Seq.mem w (objects zero_addr g) /\ is_white w g /\
              wosize_of_object w g == wosize_of_object w g0);
    assert (run_words > 0 ==>
              (forall (w: obj_addr).
                 Seq.mem w (objects zero_addr g) /\ is_white w g /\
                 U64.v (hd_address w) >= U64.v first_blue - U64.v mword /\
                 U64.v (hd_address w) < U64.v start ==> False));
    let step (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g0) /\ is_white y g0 /\
          U64.v (hd_address y) < U64.v nxt)
        (ensures
          Seq.mem y (objects zero_addr g1) /\ is_white y g1 /\
          wosize_of_object y g1 == wosize_of_object y g0)
      = if U64.v (hd_address y) < U64.v start then begin
          // The old clause 4 (a raw, local hypothesis, just unpacked above)
          // transfers y from g0 into g.
          is_white_iff y g0; color_of_object_spec y g0;
          eliminate forall (w: obj_addr).
              Seq.mem w (objects zero_addr g0) /\ is_white w g0 /\
              U64.v (hd_address w) < U64.v start ==>
              Seq.mem w (objects zero_addr g) /\ is_white w g /\
              wosize_of_object w g == wosize_of_object w g0
          with y;
          is_white_iff y g; color_of_object_spec y g;
          if run_words = 0 then begin
            assert (g1 == g);
            assert (Seq.mem y (objects zero_addr g1));
            assert (is_white y g1);
            assert (wosize_of_object y g1 == wosize_of_object y g0)
          end
          else begin
            assert (Seq.mem y (objects zero_addr g));
            mem_from_le_hd_address zero_addr g y;
            objects_mem_implies_walk_visits g zero_addr y;
            flush_membership_below g first_blue run_words fp zero_addr y;
            flush_blue_preserves_outside g first_blue run_words fp (hd_address y);
            header_agree_transfers g g1 y;
            assert (Seq.mem y (objects zero_addr g1));
            assert (is_white y g1);
            assert (wosize_of_object y g1 == wosize_of_object y g0)
          end
        end else begin
          objects_split_from g0 zero_addr start;
          eliminate exists (pre: seq obj_addr).
              objects zero_addr g0 == Seq.append pre (objects start g0) /\
              (forall (w: obj_addr). Seq.mem w pre ==> U64.v (hd_address w) < U64.v start) /\
              (forall (w: obj_addr). Seq.mem w (objects start g0) ==> U64.v (hd_address w) >= U64.v start)
          with begin
            mem_append_lemma y pre (objects start g0);
            mem_cons_lemma y x (objects nxt g0);
            // Rule out y in objects_nxt_g0: that would give hd_address y
            // >= nxt (mem_cons_lemma's second disjunct plus the shared
            // alignment-gap argument), contradicting hd_address y < nxt.
            // So y = x.
            (if not (y = x) then mem_from_le_hd_address nxt g0 y);
            // y == x: its header (at `start`) is untouched, g0 through g to
            // g1 (clause 1 above start, then the flush leaves start alone).
            assert (read_word g start == read_word g0 start);
            flush_blue_preserves_outside g first_blue run_words fp start;
            header_agree_transfers g0 g y;
            header_agree_transfers g g1 y;
            mem_cons_lemma y x (objects nxt g1);
            // y = x is in objects start g1, a suffix of the walk from
            // zero_addr in g1; bridge it back to global membership.
            objects_split_from g1 zero_addr start;
            eliminate exists (pre1: seq obj_addr).
                objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
                (forall (w: obj_addr). Seq.mem w pre1 ==> U64.v (hd_address w) < U64.v start) /\
                (forall (w: obj_addr). Seq.mem w (objects start g1) ==> U64.v (hd_address w) >= U64.v start)
            with begin
              mem_append_lemma y pre1 (objects start g1)
            end
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires step)
#pop-options

/// Heap-top boundary case: `objs` is non-empty but its head `x` reaches (or
/// overruns) the top of the heap.  Re-derives `x`, its wosize, and the
/// top-of-heap fact from `objs`, then dispatches to the blue/white lemmas
/// above.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let caw_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
         Seq.mem z (objects zero_addr g') /\ is_white z g' /\
         wosize_of_object z g' == wosize_of_object z g0))
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      caw_top_blue g0 g start x first_blue fb' run_words rw' fp;
      let gb = fst (flush_blue g fb' rw' fp) in
      assert (fst (coalesce_aux g0 g objs first_blue run_words fp) == gb);
      let final (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects zero_addr g0) /\ is_white z g0)
          (ensures
            Seq.mem z (objects zero_addr (fst (coalesce_aux g0 g objs first_blue run_words fp))) /\
            is_white z (fst (coalesce_aux g0 g objs first_blue run_words fp)) /\
            wosize_of_object z (fst (coalesce_aux g0 g objs first_blue run_words fp)) ==
              wosize_of_object z g0)
        = if U64.v (hd_address z) < U64.v start then begin
            // Clause 4 carries z from g0 into g; caw_top_blue's own
            // conclusion then carries it on from g into gb.
            assert (Seq.mem z (objects zero_addr g));
            assert (is_white z g);
            assert (wosize_of_object z g == wosize_of_object z g0);
            assert (Seq.mem z (objects zero_addr gb));
            assert (is_white z gb);
            assert (wosize_of_object z gb == wosize_of_object z g0)
          end else begin
            // z would have to be x (the only object of g0 at or above
            // start), but x is blue here, contradicting is_white z g0.
            objects_split_from g0 zero_addr start;
            eliminate exists (pre: seq obj_addr).
                objects zero_addr g0 == Seq.append pre (objects start g0) /\
                (forall (w: obj_addr). Seq.mem w pre ==> U64.v (hd_address w) < U64.v start) /\
                (forall (w: obj_addr). Seq.mem w (objects start g0) ==> U64.v (hd_address w) >= U64.v start)
            with begin
              mem_append_lemma z pre (objects start g0);
              mem_cons_lemma z x Seq.empty;
              is_white_iff z g0; is_blue_iff x g0;
              color_of_object_spec z g0; color_of_object_spec x g0
            end
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires final)
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      assert (fst (coalesce_aux g0 g objs first_blue run_words fp) == g1);
      caw_top_white g0 g g1 start x first_blue run_words fp;
      let final (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects zero_addr g0) /\ is_white z g0)
          (ensures
            Seq.mem z (objects zero_addr (fst (coalesce_aux g0 g objs first_blue run_words fp))) /\
            is_white z (fst (coalesce_aux g0 g objs first_blue run_words fp)) /\
            wosize_of_object z (fst (coalesce_aux g0 g objs first_blue run_words fp)) ==
              wosize_of_object z g0)
        = assert (Seq.mem z (objects zero_addr g1));
          assert (is_white z g1);
          assert (wosize_of_object z g1 == wosize_of_object z g0)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires final)
    end
#pop-options

/// The real induction.  A four-way dispatcher (empty / heap-top / blue head /
/// white head), each case a separately-verified lemma with its own small
/// proof context, rather than one huge recursive body.  The blue/white "head"
/// cases recurse, so they and the dispatcher form one mutual-recursion group
/// with a lexicographic `decreases`: the dispatcher is at phase 1 (so it can
/// call the phase-0 cases at the *same* `objs` length), and the cases
/// recurse back into the dispatcher only at a strictly smaller length.
///
/// "H-reachability" -- `white_inv`'s clause 6 -- is re-established at each
/// step: it's exactly `white_inv`'s own clause 2, evaluated at the moment a
/// run begins (`first_blue` is then `Seq.head objs`, whose header address is
/// `start`, and clause 2 already gives `walk_visits g zero_addr start`) --
/// and carries over unchanged while a run keeps accumulating (`first_blue`
/// doesn't change, and clause 1 gives `g` itself doesn't change in the blue
/// case either); see `caw_blue_head`. It's vacuous once a run flushes and
/// resets to `run_words = 0`; see `caw_white_head`.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_preserves_white_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires white_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x: obj_addr).
         Seq.mem x (objects zero_addr g0) /\ is_white x g0 ==>
         Seq.mem x (objects zero_addr g') /\ is_white x g' /\
         wosize_of_object x g' == wosize_of_object x g0))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_white_head g0 g start objs first_blue run_words fp all_objs
    end

/// Ordinary step, `x` blue, not at the heap top: extend the pending run by
/// one object and recurse.  `objects_cons_step_to` gives the exact structural
/// fact `objects start g == x :: objects nxt g`; `caw_extend_run_white_free`
/// (with `hi = nxt`) carries clause 5 forward to the new cursor for the
/// recursive call's own precondition.
and caw_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
         Seq.mem z (objects zero_addr g') /\ is_white z g' /\
         wosize_of_object z g' == wosize_of_object z g0))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x (objects nxt g);
          if y = x then ()
          else begin
            objects_addresses_gt_start nxt g y;
            hd_address_spec y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    // H-reachability for the new state `(g, nxt, fb', rw')`: if the run is
    // starting now, `fb' = x` and `hd_address x == start`, and clause 2
    // already gives `walk_visits g zero_addr start`; if it was already
    // accumulating, `fb' = first_blue` and `g` is unchanged, so white_inv's
    // own clause 6 at the *current* state carries over unchanged.
    (if run_words = 0 then h_addr_agree fb');
    // Establish white_inv's clauses at the new state one at a time, rather
    // than leaving the recursive call's whole precondition to be discharged
    // as one bundled query.
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_preserves_white_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

/// Ordinary step, `x` white, not at the heap top: flush whatever run was
/// pending (via `flush_white_transfer`/`flush_density_transfer`, unchanged
/// from before), then recurse from `nxt` with a fresh, empty run.
/// `objects_cons_step_to` plus `flush_preserves_walk`'s `objects` agreement
/// (unconditional, at or above `start` in the flushed heap) gives the
/// recursive call's `objects nxt g1 == Seq.tail objs` obligation.
and caw_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      white_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (z: obj_addr).
         Seq.mem z (objects zero_addr g0) /\ is_white z g0 ==>
         Seq.mem z (objects zero_addr g') /\ is_white z g' /\
         wosize_of_object z g' == wosize_of_object z g0))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start
     end);
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    assert (objects nxt g1 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    // Establish white_inv's clauses at the new (reset) state one at a time,
    // rather than leaving the recursive call's whole precondition to be
    // discharged as one bundled query. Clauses 5/6 are vacuous at run_words
    // = 0.
    // Decompose walk_pre's own conjunction, rather than proving it whole.
    assert (Seq.tail objs == objects nxt g0);
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    // Clause 4, extended from `start` to `nxt`: below `start` it's the old
    // clause 4 (ambient, at `start`) carried across the flush (clause 5 at
    // `start` rules out the "inside the run" case); at/above `start` and
    // below `nxt`, `objects_cons_step_to` forces y = x, whose header is
    // untouched by the flush (the write range ends strictly below `start`).
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_preserves_white_aux
      g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

/// `white_inv`'s clause 6 ("H-reachability") closes the gap that otherwise
/// blocks this for `run_words > 0`, so the wrapper is now just the induction
/// directly, for every `run_words`.
let coalesce_aux_preserves_white
      g0 g start objs first_blue run_words fp all_objs =
  coalesce_aux_preserves_white_aux g0 g start objs first_blue run_words fp all_objs

let coalesce_preserves_white g =
  coalesce_aux_preserves_white g g zero_addr (objects zero_addr g) 0UL 0 0UL
                               (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// Whole-size conservation: general helpers
/// ---------------------------------------------------------------------------
///
/// `blue_whsize` is additive over `Seq.append`, and agrees between two heaps
/// that agree at every header of every object in the sequence -- the two
/// facts the flush-conserves-whsize argument below is built from.

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec blue_whsize_append (g: heap) (s1 s2: seq obj_addr)
  : Lemma
    (ensures blue_whsize g (Seq.append s1 s2) == blue_whsize g s1 + blue_whsize g s2)
    (decreases (Seq.length s1))
  = if Seq.length s1 = 0 then
      Seq.lemma_eq_elim (Seq.append s1 s2) s2
    else begin
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      Seq.lemma_append_cons s1 s2;
      Seq.head_cons hd (Seq.append tl s2);
      Seq.lemma_tl hd (Seq.append tl s2);
      blue_whsize_append g tl s2
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec blue_whsize_agree (g g': heap) (s: seq obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      (forall (y: obj_addr). Seq.mem y s ==>
         read_word g (hd_address y) == read_word g' (hd_address y)))
    (ensures blue_whsize g s == blue_whsize g' s)
    (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else begin
      let x = Seq.head s in
      let t = Seq.tail s in
      Seq.cons_head_tail s;
      mem_cons_lemma x x t;
      header_agree_transfers g g' x;
      let mem_t (y: obj_addr)
        : Lemma (requires Seq.mem y t) (ensures Seq.mem y s)
        = mem_cons_lemma y x t
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires mem_t);
      blue_whsize_agree g g' t
    end
#pop-options

/// Prefix version of `objects_split_from`: if two heaps agree at every
/// header strictly below `bound` starting from `s`, and `g`'s walk from `s`
/// reaches `bound`, the segment of objects strictly below `bound` is built
/// identically in both heaps.  Proved by an induction that runs in lockstep
/// with `objects_split_from`'s own, tracking `g` and `g1` simultaneously.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let rec objects_prefix_agree (g g1: heap) (s bound: hp_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g1 == heap_size /\
      walk_visits g s bound /\
      (forall (q: hp_addr). U64.v q >= U64.v s /\ U64.v q + U64.v mword <= U64.v bound ==>
         read_word g1 q == read_word g q))
    (ensures
      (exists (pre: seq obj_addr).
         objects s g == Seq.append pre (objects bound g) /\
         objects s g1 == Seq.append pre (objects bound g1) /\
         (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v bound)))
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v bound then begin
      Seq.lemma_eq_elim (objects s g) (Seq.append Seq.empty (objects bound g));
      Seq.lemma_eq_elim (objects s g1) (Seq.append Seq.empty (objects bound g1));
      FStar.Classical.exists_intro
        (fun (pre: seq obj_addr) ->
           objects s g == Seq.append pre (objects bound g) /\
           objects s g1 == Seq.append pre (objects bound g1) /\
           (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v bound))
        Seq.empty
    end
    else begin
      walk_visits_above g s bound;
      WE.walk_end_step g s;
      WE.walk_head g s;
      WE.walk_end_step g1 s;
      WE.walk_head g1 s;
      f_address_spec s;
      let x : obj_addr = f_address s in
      hd_address_spec x;
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let nxt = mk_hp_addr next_nat in
      assert (read_word g1 s == read_word g s);
      objects_prefix_agree g g1 nxt bound;
      eliminate exists (pre: seq obj_addr).
          objects nxt g == Seq.append pre (objects bound g) /\
          objects nxt g1 == Seq.append pre (objects bound g1) /\
          (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v bound)
      with begin
        let pre' = Seq.cons x pre in
        Seq.lemma_tl x pre;
        Seq.lemma_eq_elim (objects s g) (Seq.cons x (objects nxt g));
        Seq.lemma_eq_elim (objects s g) (Seq.append pre' (objects bound g));
        Seq.lemma_eq_elim (objects s g1) (Seq.cons x (objects nxt g1));
        Seq.lemma_eq_elim (objects s g1) (Seq.append pre' (objects bound g1));
        let below (z: obj_addr)
          : Lemma (Seq.mem z pre' ==> U64.v (hd_address z) < U64.v bound)
          = mem_cons_lemma z x pre
        in
        FStar.Classical.forall_intro below;
        FStar.Classical.exists_intro
          (fun (pre2: seq obj_addr) ->
             objects s g == Seq.append pre2 (objects bound g) /\
             objects s g1 == Seq.append pre2 (objects bound g1) /\
             (forall (z: obj_addr). Seq.mem z pre2 ==> U64.v (hd_address z) < U64.v bound))
          pre'
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Whole-size conservation: the walk invariant
/// ---------------------------------------------------------------------------
///
/// Built on `white_inv` (reusing its H-reachability/density/walk-agreement
/// bookkeeping wholesale) plus exactly the two facts specific to whsize: the
/// running total is unchanged, and the pending run's own blue whsize equals
/// `run_words` (no separate "list of run objects" needed -- just the sum).
let whsize_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  total_blue_whsize g0 == total_blue_whsize g /\
  (run_words > 0 ==>
    blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
      run_words + blue_whsize g objs)

/// A flush conserves the heap's total blue whsize: the run's own objects
/// (summing to `run_words`, by `whsize_inv`'s clause) become one merged
/// object of whsize `run_words`; everything else -- below the run, and from
/// `start` on -- is untouched, so its own contribution is unaffected.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let flush_conserves_whsize
  (g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
        run_words + blue_whsize g (objects start g))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       blue_whsize g1 (objects zero_addr g1) == blue_whsize g (objects zero_addr g)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    // Below `h`: unaffected by the flush -- exactly `flush_blue_preserves_outside`'s
    // own "below" condition, so the same fact both feeds `objects_prefix_agree`
    // (to carry the split witness across to `g1`) and `blue_whsize_agree`.
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      blue_whsize_append g pre (objects h g);
      flush_h_decompose g first_blue run_words fp start;
      flush_preserves_walk g (U64.v start) first_blue run_words fp;
      flush_blue_header_spec g fb run_words fp;
      let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
      makeHeader_getWosize wz_u64 Blue 0UL;
      makeHeader_getColor wz_u64 Blue 0UL;
      wosize_of_object_spec fb g1;
      color_of_object_spec fb g1;
      is_blue_iff fb g1;
      assert (is_blue fb g1);
      assert (wosize_of_object fb g1 == wz_u64);
      assert (whsize g1 fb == run_words);
      // `pre`'s own header words agree between `g` and `g1` (each element's
      // hd_address is < h, hence its whole word is below h).
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      blue_whsize_agree g g1 pre;
      // At or above `start`: unaffected by the flush.
      let above (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects start g))
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = mem_from_le_hd_address start g z;
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires above);
      blue_whsize_agree g g1 (objects start g);
      Seq.head_cons fb (objects start g1);
      Seq.lemma_tl fb (objects start g1);
      blue_whsize_append g1 pre (Seq.cons fb (objects start g1));
      Seq.lemma_eq_elim (objects h g1) (Seq.cons fb (objects start g1))
    end
#pop-options

/// The top-of-heap analogue of `flush_conserves_whsize`: the run ends
/// exactly at `heap_size`, which is not itself a valid `hp_addr`, so there is
/// no "tail" beyond the run at all -- mirrors `flush_white_transfer_at_end`.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let flush_conserves_whsize_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) == run_words)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       blue_whsize g1 (objects zero_addr g1) == blue_whsize g (objects zero_addr g)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    // `h + mword == first_blue < heap_size`, so both `objects h g` and
    // `objects h g1` are nonempty -- nonemptiness of `objects s _` depends
    // only on `s` versus `heap_size`, never on heap content.
    assert (U64.v h + U64.v mword == U64.v first_blue);
    assert (Seq.length (objects h g) > 0);
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      blue_whsize_append g pre (objects h g);
      // `pre`'s own header words agree between `g` and `g1`.
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      blue_whsize_agree g g1 pre;
      // `objects h g1` is the merged block alone: its header gives wosize
      // `run_words - 1`, so its own extent reaches exactly `heap_size`.
      flush_blue_header_spec g fb run_words fp;
      let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
      makeHeader_getWosize wz_u64 Blue 0UL;
      makeHeader_getColor wz_u64 Blue 0UL;
      wosize_of_object_spec fb g1;
      color_of_object_spec fb g1;
      is_blue_iff fb g1;
      assert (is_blue fb g1);
      assert (wosize_of_object fb g1 == wz_u64);
      f_hd_roundtrip fb;
      assert (Seq.length (objects h g1) > 0);
      WE.walk_end_step g1 h;
      Seq.lemma_eq_elim (objects h g1) (Seq.cons fb Seq.empty);
      blue_whsize_append g1 pre (Seq.cons fb Seq.empty)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Whole-size conservation: the induction
/// ---------------------------------------------------------------------------

/// The shared "extend the run by one blue object" whsize step: consuming
/// `x` (blue in `g0`, header at `start`) contributes exactly `wz + 1` to
/// `blue_whsize g objs`, since `objs == Seq.cons x (Seq.tail objs)` and `x`'s
/// header agrees between `g0` and `g`.  Used by both `caw_ws_top` (where
/// `Seq.tail objs` is empty) and `caw_ws_blue_head` (where it isn't) --
/// factored out once it was needed a second time.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let caw_ws_head_whsize
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  : Lemma
    (requires
      Seq.length g0 == heap_size /\ Seq.length g == heap_size /\
      Seq.length objs > 0 /\ hd_address (Seq.head objs) == start /\
      is_blue (Seq.head objs) g0 /\
      read_word g start == read_word g0 start)
    (ensures
      blue_whsize g objs ==
        (U64.v (wosize_of_object (Seq.head objs) g0) + 1) + blue_whsize g (Seq.tail objs))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    header_agree_transfers g0 g x;
    Seq.head_cons x (Seq.tail objs);
    Seq.lemma_tl x (Seq.tail objs)
#pop-options

/// Empty case: flush whatever run is pending, using `flush_conserves_whsize`
/// (vacuous if `run_words = 0`, since the flush is then the identity).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_ws_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      total_blue_whsize g0 == total_blue_whsize (fst (flush_blue g first_blue run_words fp)))
  = if run_words = 0 then ()
    else begin
      run_words_bound first_blue run_words start;
      assert (objects start g == objs);
      assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                run_words + blue_whsize g objs);
      flush_conserves_whsize g start first_blue run_words fp
    end
#pop-options

/// Top-of-heap case: `x` is the last object.  Blue: extend the run and flush
/// it against the top of the heap (`flush_conserves_whsize_at_end`).  White:
/// the pending run (if any) ends exactly at `start` -- an ordinary flush,
/// `x` itself untouched.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let caw_ws_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    assert (objects start g == objs);
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      h_addr_agree fb';
      assert (U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size);
      caw_ws_head_whsize g0 g start objs;
      assert (blue_whsize g objs == (wz + 1) + blue_whsize g (Seq.tail objs));
      assert (blue_whsize g (Seq.tail objs) == 0);
      assert (blue_whsize g objs == wz + 1);
      (if run_words = 0 then begin
         assert (hd_address fb' == start);
         assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) == rw')
       end else begin
         assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                   run_words + blue_whsize g objs);
         assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) == rw')
       end);
      run_words_bound_top fb' rw';
      assert (walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
      flush_conserves_whsize_at_end g fb' rw' fp;
      assert (total_blue_whsize g0 == total_blue_whsize (fst (flush_blue g fb' rw' fp)))
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      if run_words = 0 then ()
      else begin
        run_words_bound first_blue run_words start;
        assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                  run_words + blue_whsize g objs);
        Seq.head_cons x (Seq.tail objs);
        Seq.lemma_tl x (Seq.tail objs);
        is_blue_iff x g0;
        header_agree_transfers g0 g x;
        assert (~(is_blue x g));
        assert (blue_whsize g objs == 0 + blue_whsize g (Seq.tail objs));
        assert (blue_whsize g (Seq.tail objs) == 0);
        assert (blue_whsize g objs == 0);
        assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) == run_words);
        flush_conserves_whsize g start first_blue run_words fp
      end
    end
#pop-options

/// The real induction.  Four-way dispatcher (empty / heap-top / blue head /
/// white head), mirroring `coalesce_aux_preserves_white_aux`'s own structure
/// and reusing its leaf lemmas (`caw_extend_run_white_free`,
/// `caw_clause4_ext_blue`, `caw_clause4_ext_white`) wherever the bookkeeping
/// is identical -- only the whsize-specific facts are new here.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_conserves_whsize_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires whsize_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_ws_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_ws_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_ws_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_ws_white_head g0 g start objs first_blue run_words fp all_objs
    end

and caw_ws_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x (objects nxt g);
          if y = x then ()
          else begin
            objects_addresses_gt_start nxt g y;
            hd_address_spec y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    (if run_words = 0 then h_addr_agree fb');
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    // whsize_inv's own two extra clauses at the new state.
    caw_ws_head_whsize g0 g start objs;
    assert (blue_whsize g objs == (wz + 1) + blue_whsize g (Seq.tail objs));
    (if run_words = 0 then begin
       assert (hd_address fb' == start);
       assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) ==
                 rw' + blue_whsize g (Seq.tail objs))
     end else begin
       assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                 run_words + blue_whsize g objs);
       assert (blue_whsize g (objects (mk_hp_addr (U64.v fb' - U64.v mword)) g) ==
                 rw' + blue_whsize g (Seq.tail objs))
     end);
    assert (total_blue_whsize g0 == total_blue_whsize g);
    assert (whsize_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_conserves_whsize_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

and caw_ws_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      whsize_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      total_blue_whsize g0 ==
        total_blue_whsize (fst (coalesce_aux g0 g objs first_blue run_words fp)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start;
       assert (blue_whsize g (objects (mk_hp_addr (U64.v first_blue - U64.v mword)) g) ==
                 run_words + blue_whsize g objs);
       flush_conserves_whsize g start first_blue run_words fp
     end);
    assert (total_blue_whsize g0 == total_blue_whsize g1);
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    assert (objects nxt g1 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    assert (Seq.tail objs == objects nxt g0);
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    assert (whsize_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_conserves_whsize_aux g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

let coalesce_conserves_whsize g =
  coalesce_aux_conserves_whsize_aux g g zero_addr (objects zero_addr g) 0UL 0 0UL
                                    (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// Blue coverage: general helpers
/// ---------------------------------------------------------------------------
///
/// `blue_covered g p` is existential over `objects zero_addr g`; the two
/// facts the flush-preserves-coverage argument needs are: a header-agreeing
/// witness transfers (the `blue_covered` analogue of `header_agree_transfers`),
/// and no object's extent crosses a walk boundary (a pure structural fact,
/// independent of coalescing, needed to localize which objects can possibly
/// cover a position below/above a given cursor).

/// If `x`'s header agrees between two heaps, `x`'s contribution to
/// `blue_covered` at any position transfers: same colour, same extent.
let blue_covered_by_agree (g g': heap) (x: obj_addr) (p: nat)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      read_word g (hd_address x) == read_word g' (hd_address x))
    (ensures (is_blue x g /\ in_extent g x p) <==> (is_blue x g' /\ in_extent g' x p))
  = header_agree_transfers g g' x

/// No object visited along the walk from `s` to `bound` extends past
/// `bound`: if `x` is on the walk from `s` with `hd_address x < bound`, and
/// the walk from `s` reaches `bound`, `x`'s own extent ends at or before
/// `bound`.  A structural fact about how `objects`/`walk_visits` tile the
/// heap; proved by an induction mirroring `objects_split_from`'s own.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec objects_no_straddle (g: heap) (s bound: hp_addr) (x: obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ walk_visits g s bound /\
      Seq.mem x (objects s g) /\ U64.v (hd_address x) < U64.v bound)
    (ensures next_pos g x <= U64.v bound)
    (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v bound then begin
      objects_addresses_gt_start s g x;
      hd_address_spec x
    end
    else begin
      walk_visits_above g s bound;
      WE.walk_end_step g s;
      WE.walk_head g s;
      f_address_spec s;
      let y : obj_addr = f_address s in
      hd_address_spec y;
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let nxt = mk_hp_addr next_nat in
      assert (walk_visits g nxt bound);
      if x = y then begin
        wosize_of_object_spec x g;
        walk_visits_above g nxt bound
      end else begin
        Seq.cons_head_tail (objects s g);
        mem_cons_lemma x y (objects nxt g);
        objects_no_straddle g nxt bound x
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Blue coverage: the walk invariant
/// ---------------------------------------------------------------------------

let blue_cov_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g p)) /\
  (run_words > 0 ==>
    (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
       blue_covered g p))

/// A flush conserves blue coverage at every position: below the run's
/// floor, the same split witness (`objects_prefix_agree`) plus header
/// agreement carries any covering object across unchanged; inside the run,
/// the merged block itself covers exactly `[h, start)`, matching the
/// invariant's own "run is covered" clause; at or above `start`, no object
/// can straddle the boundary (`objects_no_straddle`), so any covering
/// object is untouched by the flush.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_coverage
  (g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      walk_visits g zero_addr start /\
      (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
         blue_covered g p))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g p <==> blue_covered g1 p)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    flush_reaches_run_end g first_blue run_words fp start;
    flush_h_decompose g first_blue run_words fp start;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == U64.v start);
    objects_split_from g zero_addr start;
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      Seq.head_cons fb (objects start g1);
      Seq.lemma_tl fb (objects start g1);
      assert (objects h g1 == Seq.cons fb (objects start g1));
      eliminate exists (pre2: seq obj_addr).
          objects zero_addr g == Seq.append pre2 (objects start g) /\
          (forall (z: obj_addr). Seq.mem z pre2 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
      with begin
      objects_split_from g1 zero_addr start;
      eliminate exists (pre3: seq obj_addr).
          objects zero_addr g1 == Seq.append pre3 (objects start g1) /\
          (forall (z: obj_addr). Seq.mem z pre3 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        let step (p: nat)
          : Lemma
            (requires p < heap_size)
            (ensures blue_covered g p <==> blue_covered g1 p)
          = if p < U64.v h then begin
              let fwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                    in_extent g witness p)
                  (ensures blue_covered g1 p)
                = mem_append_lemma witness pre (objects h g);
                  (if not (Seq.mem witness pre) then mem_from_le_hd_address h g witness);
                  mem_append_lemma witness pre (objects h g1);
                  blue_covered_by_agree g g1 witness p
              in
              let bwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                    in_extent g1 witness p)
                  (ensures blue_covered g p)
                = mem_append_lemma witness pre (objects h g1);
                  (if not (Seq.mem witness pre) then mem_from_le_hd_address h g1 witness);
                  mem_append_lemma witness pre (objects h g);
                  blue_covered_by_agree g g1 witness p
              in
              (if blue_covered g p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                     in_extent g witness p
                 with begin fwd witness end);
              (if blue_covered g1 p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                     in_extent g1 witness p
                 with begin bwd witness end)
            end
            else if p < U64.v start then begin
              assert (blue_covered g p);
              mem_append_lemma fb pre (objects h g1);
              assert (Seq.mem fb (objects zero_addr g1));
              assert (in_extent g1 fb p);
              assert (blue_covered g1 p)
            end
            else begin
              let fwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                    in_extent g witness p)
                  (ensures blue_covered g1 p)
                = (if U64.v (hd_address witness) < U64.v start then
                     objects_no_straddle g zero_addr start witness);
                  assert (U64.v (hd_address witness) >= U64.v start);
                  mem_append_lemma witness pre2 (objects start g);
                  assert (Seq.mem witness (objects start g));
                  assert (objects start g1 == objects start g);
                  assert (Seq.mem witness (objects start g1));
                  mem_append_lemma witness pre3 (objects start g1);
                  assert (Seq.mem witness (objects zero_addr g1));
                  blue_covered_by_agree g g1 witness p;
                  assert (is_blue witness g1 /\ in_extent g1 witness p);
                  assert (blue_covered g1 p)
              in
              let bwd (witness: obj_addr)
                : Lemma
                  (requires
                    Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                    in_extent g1 witness p)
                  (ensures blue_covered g p)
                = (if U64.v (hd_address witness) < U64.v start then
                     objects_no_straddle g1 zero_addr start witness);
                  assert (U64.v (hd_address witness) >= U64.v start);
                  mem_append_lemma witness pre3 (objects start g1);
                  assert (Seq.mem witness (objects start g1));
                  assert (objects start g1 == objects start g);
                  assert (Seq.mem witness (objects start g));
                  mem_append_lemma witness pre2 (objects start g);
                  assert (Seq.mem witness (objects zero_addr g));
                  blue_covered_by_agree g g1 witness p;
                  assert (is_blue witness g /\ in_extent g witness p);
                  assert (blue_covered g p)
              in
              (if blue_covered g p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                     in_extent g witness p
                 with begin fwd witness end);
              (if blue_covered g1 p then
                 eliminate exists (witness: obj_addr).
                     Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                     in_extent g1 witness p
                 with begin bwd witness end)
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires step)
      end
      end
    end
#pop-options

/// The top-of-heap analogue of `flush_conserves_coverage`: the run ends
/// exactly at `heap_size`, so there is no "at or above `start`" case at all
/// -- every position below `heap_size` is either below the run's floor or
/// inside the run itself.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_coverage_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < heap_size ==>
         blue_covered g p))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g p <==> blue_covered g1 p)))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    assert (U64.v h + U64.v mword == U64.v first_blue);
    // `objects h g` is nonempty: `h` itself is covered (by hypothesis, since
    // `h < heap_size`), and no object visited from `zero_addr` can straddle
    // the walk position `h` (`objects_no_straddle`), so the covering object
    // sits exactly at `h`, giving `objects h g` its head.
    assert (blue_covered g (U64.v h));
    objects_split_from g zero_addr h;
    eliminate exists (pre0: seq obj_addr).
        objects zero_addr g == Seq.append pre0 (objects h g) /\
        (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v h) /\
        (forall (z: obj_addr). Seq.mem z (objects h g) ==> U64.v (hd_address z) >= U64.v h)
    with begin
      let land (x: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x (U64.v h))
          (ensures Seq.mem x (objects h g))
        = (if U64.v (hd_address x) < U64.v h then objects_no_straddle g zero_addr h x);
          assert (U64.v (hd_address x) >= U64.v h);
          mem_append_lemma x pre0 (objects h g)
      in
      eliminate exists (x: obj_addr).
          Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x (U64.v h)
      with begin
        land x;
        assert (Seq.length (objects h g) > 0)
      end
    end;
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == heap_size);
    f_hd_roundtrip fb;
    assert (Seq.length (objects h g1) > 0);
    WE.walk_end_step g1 h;
    Seq.lemma_eq_elim (objects h g1) (Seq.cons fb Seq.empty);
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      let step (p: nat)
        : Lemma
          (requires p < heap_size)
          (ensures blue_covered g p <==> blue_covered g1 p)
        = if p < U64.v h then begin
            let fwd (witness: obj_addr)
              : Lemma
                (requires
                  Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                  in_extent g witness p)
                (ensures blue_covered g1 p)
              = mem_append_lemma witness pre (objects h g);
                (if not (Seq.mem witness pre) then mem_from_le_hd_address h g witness);
                mem_append_lemma witness pre (objects h g1);
                blue_covered_by_agree g g1 witness p
            in
            let bwd (witness: obj_addr)
              : Lemma
                (requires
                  Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                  in_extent g1 witness p)
                (ensures blue_covered g p)
              = mem_append_lemma witness pre (objects h g1);
                (if not (Seq.mem witness pre) then mem_from_le_hd_address h g1 witness);
                mem_append_lemma witness pre (objects h g);
                blue_covered_by_agree g g1 witness p
            in
            (if blue_covered g p then
               eliminate exists (witness: obj_addr).
                   Seq.mem witness (objects zero_addr g) /\ is_blue witness g /\
                   in_extent g witness p
               with begin fwd witness end);
            (if blue_covered g1 p then
               eliminate exists (witness: obj_addr).
                   Seq.mem witness (objects zero_addr g1) /\ is_blue witness g1 /\
                   in_extent g1 witness p
               with begin bwd witness end)
          end
          else begin
            assert (blue_covered g p);
            mem_append_lemma fb pre (objects h g1);
            assert (Seq.mem fb (objects zero_addr g1));
            assert (in_extent g1 fb p);
            assert (blue_covered g1 p)
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires step)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Blue coverage: the induction
/// ---------------------------------------------------------------------------

/// Empty case: flush whatever run is pending, using `flush_conserves_coverage`
/// (vacuous if `run_words = 0`).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let caw_bc_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g1 p)))
  = if run_words = 0 then ()
    else begin
      run_words_bound first_blue run_words start;
      assert (objects start g == objs);
      assert (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
                blue_covered g p);
      flush_conserves_coverage g start first_blue run_words fp
    end
#pop-options

/// Top-of-heap case: `x` is the last object.  Blue: extend the run and
/// flush it against the top of the heap, `x`'s own extent covering exactly
/// `[floor, heap_size)`.  White: the pending run (if any) ends exactly at
/// `start`, an ordinary flush.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
private let caw_bc_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    assert (objects start g == objs);
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      h_addr_agree fb';
      assert (U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size);
      header_agree_transfers g0 g x;
      assert (is_blue x g);
      wosize_of_object_spec x g;
      assert (next_pos g x == heap_size);
      objects_split_from g zero_addr start;
      eliminate exists (pre: seq obj_addr).
          objects zero_addr g == Seq.append pre (objects start g) /\
          (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        mem_append_lemma x pre (objects start g);
        assert (Seq.mem x (objects zero_addr g));
        let cov_run (p: nat)
          : Lemma
            (requires U64.v fb' - U64.v mword <= p /\ p < heap_size)
            (ensures blue_covered g p)
          = if run_words = 0 then begin
              assert (in_extent g x p)
            end
            else if p < U64.v start then ()
            else assert (in_extent g x p)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires cov_run);
        run_words_bound_top fb' rw';
        flush_conserves_coverage_at_end g fb' rw' fp;
        let g1 = fst (flush_blue g fb' rw' fp) in
        assert (forall (p: nat). p < heap_size ==> (blue_covered g p <==> blue_covered g1 p));
        assert (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g1 p))
      end
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      if run_words = 0 then ()
      else begin
        run_words_bound first_blue run_words start;
        assert (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
                  blue_covered g p);
        flush_conserves_coverage g start first_blue run_words fp
      end
    end
#pop-options

/// The real induction.  Four-way dispatcher, mirroring
/// `coalesce_aux_conserves_whsize_aux`'s own structure and reusing the same
/// leaf lemmas (`caw_extend_run_white_free`, `caw_clause4_ext_blue`,
/// `caw_clause4_ext_white`) for the `white_inv` bookkeeping.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_preserves_blue_coverage_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires blue_cov_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_bc_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_bc_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_bc_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_bc_white_head g0 g start objs first_blue run_words fp all_objs
    end

and caw_bc_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          assert (objects zero_addr g == Seq.append pre (objects start g));
          mem_append_lemma y pre (objects start g);
          assert (Seq.mem y pre \/ Seq.mem y (objects start g));
          if Seq.mem y pre then begin
            assert (U64.v (hd_address y) < U64.v start);
            assert (U64.v (hd_address y) >= U64.v start);
            assert (y == x)
          end else begin
            assert (Seq.mem y (objects start g));
            mem_cons_lemma y x (objects nxt g);
            assert (y == x \/ Seq.mem y (objects nxt g));
            if y = x then ()
            else begin
              assert (Seq.mem y (objects nxt g));
              objects_addresses_gt_start nxt g y;
              hd_address_spec y;
              assert (U64.v (hd_address y) >= U64.v nxt);
              assert (U64.v (hd_address y) < U64.v nxt);
              assert (y == x)
            end
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    (if run_words = 0 then h_addr_agree fb');
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    // blue_cov_inv's own two extra clauses at the new state: coverage is a
    // global equivalence unaffected by the blue step (`g` doesn't change),
    // and the extended run's own coverage, mirroring `caw_ws_head_whsize`'s
    // role for whsize but for the "is covered" predicate instead of a sum.
    assert (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g p));
    let cov_run (p: nat)
      : Lemma
        (requires U64.v fb' - U64.v mword <= p /\ p < U64.v nxt)
        (ensures blue_covered g p)
      = if p < U64.v start then ()
        else assert (in_extent g x p)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cov_run);
    assert (blue_cov_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_preserves_blue_coverage_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

and caw_bc_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      blue_cov_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g' p)))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    flush_preserves_walk g (U64.v start) first_blue run_words fp;
    objects_split_from g zero_addr start;
    eliminate exists (pre0: seq obj_addr).
        objects zero_addr g == Seq.append pre0 (objects start g) /\
        (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      Seq.lemma_len_append pre0 (objects start g)
    end;
    assert (Seq.length (objects zero_addr g) > 0);
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_white_transfer g start first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp;
       flush_reaches_run_end g first_blue run_words fp start;
       assert (forall (p: nat). U64.v first_blue - U64.v mword <= p /\ p < U64.v start ==>
                 blue_covered g p);
       flush_conserves_coverage g start first_blue run_words fp
     end);
    assert (forall (p: nat). p < heap_size ==> (blue_covered g0 p <==> blue_covered g1 p));
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    assert (objects nxt g1 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    assert (Seq.tail objs == objects nxt g0);
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    assert (blue_cov_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_preserves_blue_coverage_aux g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

let coalesce_preserves_blue_coverage g =
  coalesce_aux_preserves_blue_coverage_aux g g zero_addr (objects zero_addr g) 0UL 0 0UL
                                           (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// No adjacent blue: general helpers
/// ---------------------------------------------------------------------------
///
/// The invariant tracks two facts about the *already-finalized* region
/// (below the pending run's own floor, or below `start` when no run is
/// pending): no two blue objects there are adjacent, and no blue object
/// there ends exactly at the floor (needed so that, when a fresh run
/// starts, the object immediately preceding it is known not to be blue --
/// otherwise the fresh run and that object would themselves already be an
/// unmerged adjacent pair).

/// If `x` and `y`'s headers both agree between two heaps, the whole
/// "adjacent and both blue" triple transfers -- the `adjacent` analogue of
/// `header_agree_transfers`/`blue_covered_by_agree`.
let adjacent_by_agree (g g': heap) (x y: obj_addr)
  : Lemma
    (requires
      Seq.length g == heap_size /\ Seq.length g' == heap_size /\
      read_word g (hd_address x) == read_word g' (hd_address x) /\
      read_word g (hd_address y) == read_word g' (hd_address y))
    (ensures
      (is_blue x g /\ is_blue y g /\ adjacent g x y) <==>
      (is_blue x g' /\ is_blue y g' /\ adjacent g' x y))
  = header_agree_transfers g g' x;
    header_agree_transfers g g' y

/// A flush conserves "no adjacent blue pair below `start`": below the run's
/// floor `h`, the same split witness plus header agreement carries any
/// pair across unchanged; the merged block itself (occupying `[h, start)`)
/// cannot be the `y` of a violating pair, since whatever would end exactly
/// at `h` (its only possible `x` partner) is ruled out by the "no blue ends
/// at the floor" hypothesis.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_adj_free
  (g: heap) (start: hp_addr) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      (forall (x y: obj_addr).
         Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
         is_blue x g /\ is_blue y g /\ adjacent g x y /\
         U64.v (hd_address y) < U64.v first_blue - U64.v mword ==> False) /\
      (forall (z: obj_addr).
         Seq.mem z (objects zero_addr g) /\ is_blue z g /\
         next_pos g z == U64.v first_blue - U64.v mword ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
          is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
          U64.v (hd_address y) < U64.v start ==> False))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_h_decompose g first_blue run_words fp start;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == U64.v start);
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      Seq.head_cons fb (objects start g1);
      Seq.lemma_tl fb (objects start g1);
      assert (objects h g1 == Seq.cons fb (objects start g1));
      // `pre`'s own header words agree between `g` and `g1`.
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      let step (x y: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
            is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
            U64.v (hd_address y) < U64.v start)
          (ensures False)
        = mem_append_lemma y pre (objects h g1);
          if Seq.mem y pre then begin
            // y < h: x, adjacent to y, has next_pos == hd_address y < h too,
            // so x is also below h, and both transfer to g via `pre_agree`.
            mem_from_le_hd_address zero_addr g1 x;
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x;
               // hd_address x >= h, but adjacent x y gives next_pos g1 x ==
               // hd_address y < h, and next_pos g1 x > hd_address x -- so
               // hd_address x < h, contradiction.
               ()
             end);
            pre_agree x; pre_agree y;
            adjacent_by_agree g g1 x y;
            mem_append_lemma x pre (objects h g);
            mem_append_lemma y pre (objects h g)
          end else begin
            // y not in pre, and y < start, so (via the split) y is in
            // `objects h g1 == cons fb (objects start g1)` with hd_address y
            // < start; the only such element is fb itself.
            assert (Seq.mem y (objects h g1));
            Seq.cons_head_tail (objects h g1);
            mem_cons_lemma y fb (objects start g1);
            (if not (y = fb) then begin
               mem_from_le_hd_address start g1 y
               // hd_address y >= start, contradicting hd_address y < start.
             end);
            assert (y == fb);
            // adjacent x fb: next_pos g1 x == h.  x < h (same argument as
            // above), so x transfers to g via `pre_agree`.
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x
             end);
            pre_agree x;
            header_agree_transfers g g1 x;
            mem_append_lemma x pre (objects h g)
          end
      in
      FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (step x))
    end
#pop-options

/// The top-of-heap analogue of `flush_conserves_adj_free`: the run ends
/// exactly at `heap_size`, so the merged block is the very last object --
/// the ensures is the full, unconditional "no adjacent blue pair anywhere."
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let flush_conserves_adj_free_at_end
  (g: heap) (first_blue: U64.t) (run_words: pos) (fp: U64.t)
  : Lemma
    (requires
      Seq.length g == heap_size /\
      U64.v first_blue >= U64.v mword /\ U64.v first_blue < heap_size /\
      U64.v first_blue % U64.v mword == 0 /\
      run_words - 1 < pow2 54 /\
      U64.v first_blue - U64.v mword + run_words * U64.v mword == heap_size /\
      walk_visits g zero_addr (mk_hp_addr (U64.v first_blue - U64.v mword)) /\
      (forall (x y: obj_addr).
         Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
         is_blue x g /\ is_blue y g /\ adjacent g x y /\
         U64.v (hd_address y) < U64.v first_blue - U64.v mword ==> False) /\
      (forall (z: obj_addr).
         Seq.mem z (objects zero_addr g) /\ is_blue z g /\
         next_pos g z == U64.v first_blue - U64.v mword ==> False))
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
          is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y ==> False))
  = let fb : obj_addr = first_blue in
    let h = hd_address fb in
    hd_address_spec fb;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    let below (q: hp_addr)
      : Lemma
        (requires U64.v q + U64.v mword <= U64.v h)
        (ensures read_word g1 q == read_word g q)
      = flush_blue_preserves_outside g first_blue run_words fp q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires below);
    objects_prefix_agree g g1 zero_addr h;
    flush_blue_header_spec g fb run_words fp;
    let wz_u64 : wosize = U64.uint_to_t (run_words - 1) in
    makeHeader_getWosize wz_u64 Blue 0UL;
    makeHeader_getColor wz_u64 Blue 0UL;
    wosize_of_object_spec fb g1;
    color_of_object_spec fb g1;
    is_blue_iff fb g1;
    assert (is_blue fb g1);
    assert (wosize_of_object fb g1 == wz_u64);
    assert (next_pos g1 fb == heap_size);
    f_hd_roundtrip fb;
    assert (U64.v h + U64.v mword == U64.v first_blue);
    assert (Seq.length (objects h g1) > 0);
    WE.walk_end_step g1 h;
    Seq.lemma_eq_elim (objects h g1) (Seq.cons fb Seq.empty);
    eliminate exists (pre: seq obj_addr).
        objects zero_addr g == Seq.append pre (objects h g) /\
        objects zero_addr g1 == Seq.append pre (objects h g1) /\
        (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v h)
    with begin
      let pre_agree (z: obj_addr)
        : Lemma
          (requires Seq.mem z pre)
          (ensures read_word g (hd_address z) == read_word g1 (hd_address z))
        = hd_address_spec z;
          FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v h) (U64.v (hd_address z)) (U64.v mword);
          assert (U64.v h - U64.v (hd_address z) >= U64.v mword);
          flush_blue_preserves_outside g first_blue run_words fp (hd_address z)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pre_agree);
      let step (x y: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
            is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y)
          (ensures False)
        = mem_append_lemma y pre (objects h g1);
          if Seq.mem y pre then begin
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x
             end);
            pre_agree x; pre_agree y;
            adjacent_by_agree g g1 x y;
            mem_append_lemma x pre (objects h g);
            mem_append_lemma y pre (objects h g)
          end else begin
            assert (Seq.mem y (objects h g1));
            Seq.cons_head_tail (objects h g1);
            mem_cons_lemma y fb Seq.empty;
            assert (y == fb);
            (if not (Seq.mem x pre) then begin
               mem_append_lemma x pre (objects h g1);
               mem_from_le_hd_address h g1 x
             end);
            pre_agree x;
            header_agree_transfers g g1 x;
            mem_append_lemma x pre (objects h g)
          end
      in
      FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (step x))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// No adjacent blue: the walk invariant
/// ---------------------------------------------------------------------------
///
/// Built on `white_inv`, tracking (below the pending run's own floor, or
/// below `start` when no run is pending): no two blue objects are adjacent,
/// and no blue object ends exactly at the floor -- the latter is what makes
/// it safe, when a run later starts fresh right there, to know the object
/// immediately preceding it isn't blue (else that object and the fresh run
/// would already be an unmerged adjacent pair).
let adj_free_inv
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (all_objs: seq obj_addr)
  : prop =
  white_inv g0 g start objs first_blue run_words all_objs /\
  (run_words = 0 ==>
    (forall (x y: obj_addr).
       Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
       is_blue x g /\ is_blue y g /\ adjacent g x y /\
       U64.v (hd_address y) < U64.v start ==> False) /\
    (forall (z: obj_addr).
       Seq.mem z (objects zero_addr g) /\ is_blue z g /\
       next_pos g z == U64.v start ==> False)) /\
  (run_words > 0 ==>
    (forall (x y: obj_addr).
       Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
       is_blue x g /\ is_blue y g /\ adjacent g x y /\
       U64.v (hd_address y) < U64.v first_blue - U64.v mword ==> False) /\
    (forall (z: obj_addr).
       Seq.mem z (objects zero_addr g) /\ is_blue z g /\
       next_pos g z == U64.v first_blue - U64.v mword ==> False))

/// Empty case: flush whatever run is pending, using `flush_conserves_adj_free`
/// (vacuous if `run_words = 0`), then note that with `objs` empty, every
/// object of `g1` genuinely sits below `start` -- so "below `start`"
/// becomes the full, unconditional fact.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
private let caw_adj_empty
  (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs = 0)
    (ensures
      (let g1 = fst (flush_blue g first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
          is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y ==> False))
  = Seq.lemma_eq_elim objs Seq.empty;
    let g1 = fst (flush_blue g first_blue run_words fp) in
    (if run_words = 0 then ()
     else begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_conserves_adj_free g start first_blue run_words fp
     end);
    assert (forall (x y: obj_addr).
              Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
              is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
              U64.v (hd_address y) < U64.v start ==> False);
    (if run_words > 0 then flush_preserves_walk g (U64.v start) first_blue run_words fp);
    assert (objects start g1 == Seq.empty);
    (if run_words > 0 then flush_reaches_run_end g first_blue run_words fp start);
    assert (walk_visits g1 zero_addr start);
    objects_split_from g1 zero_addr start;
    eliminate exists (pre1: seq obj_addr).
        objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
        (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      Seq.lemma_eq_elim (objects zero_addr g1) pre1;
      let final (x y: obj_addr)
        : Lemma
          (requires
            Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
            is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y)
          (ensures False)
        = assert (Seq.mem y pre1)
      in
      FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (final x))
    end
#pop-options

/// Top-of-heap case: `x` is the last object.  Blue: extend the run and
/// flush against the top of the heap -- `flush_conserves_adj_free_at_end`
/// gives the full unconditional fact directly.  White: the pending run (if
/// any) ends exactly at `start`; `x` itself is white, so any pair
/// involving it is automatically not a blue-blue violation.
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
private let caw_adj_top
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
  = let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    let wz = U64.v (wosize_of_object x g0) in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    Seq.lemma_eq_elim (objects start g0) (Seq.cons x Seq.empty);
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty;
    assert (objects start g == objs);
    if is_blue x g0 then begin
      let fb' = if run_words = 0 then x else first_blue in
      let rw' = run_words + wz + 1 in
      coalesce_aux_blue_step g0 g objs first_blue run_words fp;
      coalesce_aux_empty g0 g fb' rw' fp;
      hd_address_spec fb';
      h_addr_agree fb';
      assert (U64.v fb' - U64.v mword + rw' * U64.v mword == heap_size);
      run_words_bound_top fb' rw';
      assert (walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
      flush_conserves_adj_free_at_end g fb' rw' fp
    end else begin
      coalesce_aux_white_step g0 g objs first_blue run_words fp;
      let (g1, fp1) = flush_blue g first_blue run_words fp in
      coalesce_aux_empty g0 g1 0UL 0 fp1;
      (if run_words > 0 then begin
         run_words_bound first_blue run_words start;
         h_addr_agree first_blue;
         flush_preserves_walk g (U64.v start) first_blue run_words fp
       end);
      assert (objects start g1 == Seq.cons x Seq.empty);
      is_white_iff x g0;
      is_blue_iff x g0;
      header_agree_transfers g0 g1 x;
      assert (~(is_blue x g1));
      (if run_words > 0 then flush_reaches_run_end g first_blue run_words fp start);
      assert (walk_visits g1 zero_addr start);
      objects_split_from g1 zero_addr start;
      eliminate exists (pre1: seq obj_addr).
          objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
          (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
          (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
      with begin
        let final (x' y': obj_addr)
          : Lemma
            (requires
              Seq.mem x' (objects zero_addr g1) /\ Seq.mem y' (objects zero_addr g1) /\
              is_blue x' g1 /\ is_blue y' g1 /\ adjacent g1 x' y')
            (ensures False)
          = mem_append_lemma y' pre1 (objects start g1);
            if Seq.mem y' pre1 then begin
              if run_words = 0 then ()
              else begin
                run_words_bound first_blue run_words start;
                h_addr_agree first_blue;
                flush_conserves_adj_free g start first_blue run_words fp;
                eliminate forall (x: obj_addr) (y: obj_addr).
                    Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
                    is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
                    U64.v (hd_address y) < U64.v start ==> False
                with x' y'
              end
            end else begin
              mem_cons_lemma y' x Seq.empty;
              assert (y' == x)
            end
        in
        FStar.Classical.forall_intro_2 (fun x' -> FStar.Classical.move_requires (final x'))
      end
    end
#pop-options

/// The real induction.  Four-way dispatcher, mirroring
/// `coalesce_aux_conserves_whsize_aux`'s own structure and reusing the same
/// leaf lemmas (`caw_extend_run_white_free`, `caw_clause4_ext_blue`,
/// `caw_clause4_ext_white`) for the `white_inv` bookkeeping.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coalesce_aux_no_adjacent_blue_aux
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires adj_free_inv g0 g start objs first_blue run_words all_objs)
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
    (decreases %[Seq.length objs; 1])
  = if Seq.length objs = 0 then
      caw_adj_empty g0 g start objs first_blue run_words fp all_objs
    else begin
      let x = Seq.head objs in
      if U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword >= heap_size then
        caw_adj_top g0 g start objs first_blue run_words fp all_objs
      else if is_blue x g0 then
        caw_adj_blue_head g0 g start objs first_blue run_words fp all_objs
      else
        caw_adj_white_head g0 g start objs first_blue run_words fp all_objs
    end

/// Ordinary step, `x` blue: extend the run and recurse.  The finalized
/// floor is invariant across a blue step (whether starting fresh, where the
/// new floor `hd_address fb'` equals the old `start`, or continuing, where
/// `first_blue` -- and hence the floor -- doesn't change at all, since `g`
/// itself is untouched) -- so `adj_free_inv`'s own two extra clauses just
/// carry over from the old state's matching branch, unlike `white_inv`'s
/// clauses which need re-establishing at the new cursor `nxt`.
and caw_adj_blue_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ is_blue (Seq.head objs) g0 /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    let fb' = if run_words = 0 then x else first_blue in
    let rw' = run_words + wz + 1 in
    coalesce_aux_blue_step g0 g objs first_blue run_words fp;
    assert (read_word g start == read_word g0 start);
    header_agree_transfers g0 g x;
    walk_visits_step g zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    hd_address_spec fb';
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    let only_x (y: obj_addr)
      : Lemma
        (requires
          Seq.mem y (objects zero_addr g) /\
          U64.v (hd_address y) >= U64.v start /\ U64.v (hd_address y) < U64.v nxt)
        (ensures y == x)
      = objects_agree_above g0 g start (U64.v start);
        objects_split_from g zero_addr start;
        eliminate exists (pre: seq obj_addr).
            objects zero_addr g == Seq.append pre (objects start g) /\
            (forall (z: obj_addr). Seq.mem z pre ==> U64.v (hd_address z) < U64.v start) /\
            (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
        with begin
          mem_append_lemma y pre (objects start g);
          mem_cons_lemma y x (objects nxt g);
          if y = x then ()
          else begin
            objects_addresses_gt_start nxt g y;
            hd_address_spec y
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires only_x);
    caw_extend_run_white_free g0 g start x (U64.v nxt) first_blue fb' run_words;
    (if run_words = 0 then h_addr_agree fb' else ());
    assert (walk_pre g0 g nxt (Seq.tail objs) all_objs fb' rw');
    assert (Seq.length g == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g);
    assert (post_sweep_strong g0);
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g p == read_word g0 p);
    assert (walk_visits g zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g == Seq.tail objs);
    caw_clause4_ext_blue g0 g start nxt x;
    assert (rw' > 0 ==>
              (forall (y: obj_addr).
                 Seq.mem y (objects zero_addr g) /\ is_white y g /\
                 U64.v (hd_address y) >= U64.v fb' - U64.v mword /\
                 U64.v (hd_address y) < U64.v nxt ==> False));
    assert (rw' > 0 ==> walk_visits g zero_addr (mk_hp_addr (U64.v fb' - U64.v mword)));
    assert (white_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    // The floor is invariant: `hd_address fb' == (if run_words = 0 then
    // start else first_blue - mword)` -- the *same* floor the old state's
    // matching branch already has facts about, since `g` doesn't change.
    (if run_words = 0 then begin
       assert (U64.v (hd_address fb') == U64.v start);
       assert (forall (x' y': obj_addr).
                 Seq.mem x' (objects zero_addr g) /\ Seq.mem y' (objects zero_addr g) /\
                 is_blue x' g /\ is_blue y' g /\ adjacent g x' y' /\
                 U64.v (hd_address y') < U64.v (hd_address fb') ==> False);
       assert (forall (z: obj_addr).
                 Seq.mem z (objects zero_addr g) /\ is_blue z g /\
                 next_pos g z == U64.v (hd_address fb') ==> False)
     end else begin
       assert (U64.v (hd_address fb') == U64.v first_blue - U64.v mword);
       assert (forall (x' y': obj_addr).
                 Seq.mem x' (objects zero_addr g) /\ Seq.mem y' (objects zero_addr g) /\
                 is_blue x' g /\ is_blue y' g /\ adjacent g x' y' /\
                 U64.v (hd_address y') < U64.v (hd_address fb') ==> False);
       assert (forall (z: obj_addr).
                 Seq.mem z (objects zero_addr g) /\ is_blue z g /\
                 next_pos g z == U64.v (hd_address fb') ==> False)
     end);
    assert (adj_free_inv g0 g nxt (Seq.tail objs) fb' rw' all_objs);
    coalesce_aux_no_adjacent_blue_aux g0 g nxt (Seq.tail objs) fb' rw' fp all_objs

/// Ordinary step, `x` white: flush whatever run was pending, then recurse
/// from `nxt` with a fresh, empty run.  The new floor is `nxt`; below
/// `start` it transfers via `flush_conserves_adj_free` (the merged block,
/// if any, is handled inside that lemma via the "no blue ends at the old
/// floor" hypothesis), and `[start, nxt)` is just `x` itself, white, so
/// contributes no violation; "no blue ends at `nxt`" holds because `x` is
/// the *unique* object whose extent reaches `nxt` (`objects_no_straddle`
/// rules out anything below `start` reaching that far, and anything at or
/// above `nxt` can't have `next_pos == nxt` either), and `x` isn't blue.
and caw_adj_white_head
      (g0 g: heap) (start: hp_addr) (objs: seq obj_addr)
      (first_blue: U64.t) (run_words: nat) (fp: U64.t) (all_objs: seq obj_addr)
  : Lemma
    (requires
      adj_free_inv g0 g start objs first_blue run_words all_objs /\
      Seq.length objs > 0 /\ ~(is_blue (Seq.head objs) g0) /\
      (let x = Seq.head objs in
       U64.v start + (U64.v (wosize_of_object x g0) + 1) * U64.v mword < heap_size))
    (ensures
      (let g' = fst (coalesce_aux g0 g objs first_blue run_words fp) in
       forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False))
    (decreases %[Seq.length objs; 0])
  = caw_unpack_white_inv g0 g start objs first_blue run_words all_objs;
    let x = Seq.head objs in
    Seq.cons_head_tail objs;
    mem_cons_lemma x x (Seq.tail objs);
    assert (Seq.length (objects start g0) > 0);
    WE.walk_end_step g0 start;
    WE.walk_head g0 start;
    f_address_spec start;
    hd_address_spec x;
    wosize_of_object_spec x g0;
    wosize_of_object_spec x g;
    let wz = U64.v (wosize_of_object x g0) in
    let nxt_n = U64.v start + (wz + 1) * U64.v mword in
    aligned_plus_mul8 (U64.v start) (wz + 1);
    assert (Seq.length (objects start g) > 0);
    WE.walk_end_step g start;
    FStar.Math.Lemmas.distributivity_add_left run_words (wz + 1) (U64.v mword);
    let nxt = mk_hp_addr nxt_n in
    coalesce_aux_white_step g0 g objs first_blue run_words fp;
    let (g1, fp1) = flush_blue g first_blue run_words fp in
    objects_split_from g zero_addr start;
    eliminate exists (pre0: seq obj_addr).
        objects zero_addr g == Seq.append pre0 (objects start g) /\
        (forall (z: obj_addr). Seq.mem z pre0 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      Seq.lemma_len_append pre0 (objects start g)
    end;
    assert (Seq.length (objects zero_addr g) > 0);
    (if run_words > 0 then begin
       run_words_bound first_blue run_words start;
       h_addr_agree first_blue;
       flush_preserves_walk g (U64.v start) first_blue run_words fp;
       flush_density_transfer g start first_blue run_words fp
     end);
    assert (read_word g1 start == read_word g start);
    assert (read_word g start == read_word g0 start);
    is_white_iff x g0;
    is_blue_iff x g0;
    header_agree_transfers g0 g1 x;
    assert (~(is_blue x g1));
    (if run_words > 0 then flush_reaches_run_end g first_blue run_words fp start);
    assert (walk_visits g1 zero_addr start);
    objects_cons_step_to start g nxt;
    objects_cons_step_to start g0 nxt;
    assert (objects nxt g0 == Seq.tail objs);
    walk_visits_step g1 zero_addr start nxt;
    walk_visits_step g0 zero_addr start nxt;
    assert (all_objs == objects zero_addr g0);
    assert (Seq.length g0 == heap_size);
    assert (Seq.length g1 == heap_size);
    assert (post_sweep_strong g0);
    assert (post_sweep g0);
    (let subset (o: obj_addr)
       : Lemma (requires Seq.mem o (Seq.tail objs)) (ensures Seq.mem o all_objs)
       = mem_cons_lemma o x (Seq.tail objs)
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires subset));
    assert (forall (p: hp_addr). U64.v p >= U64.v nxt /\ U64.v p + U64.v mword <= heap_size ==>
              read_word g1 p == read_word g0 p);
    (let word_agree (o: obj_addr)
       : Lemma
         (requires Seq.mem o (Seq.tail objs) /\ is_white o g0)
         (ensures read_word g1 (hd_address o) == read_word g0 (hd_address o))
       = assert (Seq.mem o (objects nxt g0));
         mem_from_le_hd_address nxt g0 o;
         hd_address_bounds o
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires word_agree));
    assert (walk_pre g0 g1 nxt (Seq.tail objs) all_objs 0UL 0);
    assert (Seq.length g1 == heap_size);
    assert (Seq.length g0 == heap_size);
    assert (SI.heap_objects_dense g1);
    assert (post_sweep_strong g0);
    assert (walk_visits g1 zero_addr nxt);
    assert (walk_visits g0 zero_addr nxt);
    assert (objects nxt g1 == Seq.tail objs);
    objects_agree_above g g1 start (U64.v start);
    objects_agree_above g g1 nxt (U64.v start);
    assert (objects start g1 == Seq.cons x (objects nxt g1));
    assert (read_word g start == read_word g0 start);
    caw_clause4_ext_white g0 g g1 start nxt x first_blue run_words fp;
    assert (white_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    // adj_free_inv's own extra clauses at the reset state (floor = `nxt`).
    objects_split_from g1 zero_addr start;
    eliminate exists (pre1: seq obj_addr).
        objects zero_addr g1 == Seq.append pre1 (objects start g1) /\
        (forall (z: obj_addr). Seq.mem z pre1 ==> U64.v (hd_address z) < U64.v start) /\
        (forall (z: obj_addr). Seq.mem z (objects start g1) ==> U64.v (hd_address z) >= U64.v start)
    with begin
      let pairwise (x' y': obj_addr)
        : Lemma
          (requires
            Seq.mem x' (objects zero_addr g1) /\ Seq.mem y' (objects zero_addr g1) /\
            is_blue x' g1 /\ is_blue y' g1 /\ adjacent g1 x' y' /\
            U64.v (hd_address y') < U64.v nxt)
          (ensures False)
        = mem_append_lemma y' pre1 (objects start g1);
          if Seq.mem y' pre1 then begin
            if run_words = 0 then ()
            else begin
              run_words_bound first_blue run_words start;
              h_addr_agree first_blue;
              flush_conserves_adj_free g start first_blue run_words fp;
              eliminate forall (x: obj_addr) (y: obj_addr).
                  Seq.mem x (objects zero_addr g1) /\ Seq.mem y (objects zero_addr g1) /\
                  is_blue x g1 /\ is_blue y g1 /\ adjacent g1 x y /\
                  U64.v (hd_address y) < U64.v start ==> False
              with x' y'
            end
          end else begin
            mem_cons_lemma y' x (objects nxt g1);
            (if not (y' = x) then begin
               objects_addresses_gt_start nxt g1 y';
               hd_address_spec y'
             end);
            assert (y' == x)
          end
      in
      FStar.Classical.forall_intro_2 (fun x' -> FStar.Classical.move_requires (pairwise x'));
      let no_blue_ends (z: obj_addr)
        : Lemma
          (requires Seq.mem z (objects zero_addr g1) /\ is_blue z g1 /\ next_pos g1 z == U64.v nxt)
          (ensures False)
        = mem_append_lemma z pre1 (objects start g1);
          if Seq.mem z pre1 then begin
            objects_no_straddle g1 zero_addr start z
            // next_pos g1 z <= start < nxt, contradicting next_pos g1 z == nxt.
          end else begin
            mem_cons_lemma z x (objects nxt g1);
            (if not (z = x) then begin
               objects_addresses_gt_start nxt g1 z;
               hd_address_spec z
               // hd_address z >= nxt, so next_pos g1 z > nxt, contradicting == nxt.
             end);
            assert (z == x)
            // x is white, contradicting is_blue z g1.
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires no_blue_ends)
    end;
    assert (adj_free_inv g0 g1 nxt (Seq.tail objs) 0UL 0 all_objs);
    coalesce_aux_no_adjacent_blue_aux g0 g1 nxt (Seq.tail objs) 0UL 0 fp1 all_objs
#pop-options

let coalesce_no_adjacent_blue g =
  // `adj_free_inv`'s two extra clauses at the top level: vacuous, since no
  // object's header can sit strictly below `zero_addr` (the walk's own
  // start) or have its extent end exactly there.
  let no_pairwise (x y: obj_addr)
    : Lemma
      (requires
        Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
        is_blue x g /\ is_blue y g /\ adjacent g x y /\
        U64.v (hd_address y) < U64.v zero_addr)
      (ensures False)
    = mem_from_le_hd_address zero_addr g y
  in
  FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (no_pairwise x));
  let no_blue_ends (z: obj_addr)
    : Lemma
      (requires
        Seq.mem z (objects zero_addr g) /\ is_blue z g /\
        next_pos g z == U64.v zero_addr)
      (ensures False)
    = mem_from_le_hd_address zero_addr g z
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_blue_ends);
  coalesce_aux_no_adjacent_blue_aux g g zero_addr (objects zero_addr g) 0UL 0 0UL
                                    (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// Top level
/// ---------------------------------------------------------------------------

/// **Coalescing correctness.**
///
/// 3a and 3b together say that each input run becomes exactly one output
/// block: identical blue coverage means no run splits or moves, and
/// non-adjacency means no run stays as two blocks.  Neither needs a
/// definition of "run".
val coalesce_correct (g: heap)
  : Lemma
    (requires post_sweep_strong g /\
              SI.heap_objects_dense g /\
              Seq.length g == heap_size /\
              Seq.length (objects zero_addr g) > 0)
    (ensures
      (let g' = fst (coalesce g) in

       // 2. No free word is gained or lost.
       total_blue_whsize g' == total_blue_whsize g /\

       // 3a. The blue region of the heap is unchanged, word for word.
       (forall (p: nat). p < heap_size ==> (blue_covered g' p <==> blue_covered g p)) /\

       // 3b. No two blue objects of the output are adjacent.
       (forall (x y: obj_addr).
          Seq.mem x (objects zero_addr g') /\ Seq.mem y (objects zero_addr g') /\
          is_blue x g' /\ is_blue y g' /\ adjacent g' x y ==> False) /\

       // White objects are untouched: same object, same size.
       (forall (x: obj_addr).
          Seq.mem x (objects zero_addr g) /\ is_white x g ==>
          Seq.mem x (objects zero_addr g') /\ is_white x g' /\
          wosize_of_object x g' == wosize_of_object x g)))

let coalesce_correct g =
  coalesce_conserves_whsize g;
  coalesce_preserves_blue_coverage g;
  coalesce_no_adjacent_blue g;
  coalesce_preserves_white g
