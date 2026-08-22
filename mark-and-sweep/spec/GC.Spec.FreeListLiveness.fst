module GC.Spec.FreeListLiveness

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Chain
module SpecSweep = GC.Spec.Sweep
module Coalesce  = GC.Spec.Coalesce
module Mark = GC.Spec.Mark
module Correctness = GC.Spec.Correctness

let blue_chain_decreasing = Coalesce.blue_chain_decreasing

let free_list_complete (g: heap) (fp: U64.t) : prop =
  (fp = 0UL /\
   (forall (x: obj_addr).
     Seq.mem x (objects zero_addr g) ==> ~(is_blue x g))) \/
  (U64.v fp >= U64.v mword /\
   U64.v fp < heap_size /\
   U64.v fp % U64.v mword == 0 /\
   Seq.mem (fp <: obj_addr) (objects zero_addr g) /\
   (forall (x: obj_addr).
     Seq.mem x (objects zero_addr g) /\ is_blue x g ==>
     chain_reachable g (fp <: obj_addr) x))

let free_list_liveness (g: heap) (fp: U64.t) : prop =
  blue_chain_decreasing g /\ free_list_complete g fp

val sweep_establishes_complete
  (h: heap) (start: hp_addr) (objs: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      objs == objects start h /\
      (forall (x: obj_addr).
        Seq.mem x (objects zero_addr h) ==>
        U64.v (wosize_of_object x h) >= 1) /\
      free_list_complete h fp /\
      (fp = 0UL \/ is_pointer_field fp) /\
      well_formed_heap h /\
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects zero_addr h)))
    (ensures (let (h', fp') = SpecSweep.sweep_aux h objs fp in
              free_list_complete h' fp'))
    (decreases Seq.length objs)

val coalesce_establishes_decreasing (h: heap)
  : Lemma
    (requires
      Coalesce.post_sweep_strong h /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr h) ==>
        U64.v (wosize_of_object y h) >= 1))
    (ensures blue_chain_decreasing (fst (Coalesce.coalesce h)))

val coalesce_preserves_complete (h: heap) (fp: U64.t)
  : Lemma
    (requires free_list_complete h fp)
    (ensures (let (h', fp') = Coalesce.coalesce h in
              free_list_complete h' fp'))

val gc_free_list_liveness (h_init: heap) (st: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      Correctness.mark_post h_init (Mark.mark h_init st) st fp /\
      (let h_mark = Mark.mark h_init st in
       well_formed_heap h_mark /\
       (forall (x: obj_addr).
         Seq.mem x (objects zero_addr h_mark) ==>
         U64.v (wosize_of_object x h_mark) >= 1) /\
       free_list_complete h_mark fp /\
       (fp = 0UL \/ is_pointer_field fp)))
    (ensures (let h_sweep = fst (SpecSweep.sweep (Mark.mark h_init st) fp) in
              let (h_final, fp_final) = Coalesce.coalesce h_sweep in
              free_list_liveness h_final fp_final))

let walk_next (h: heap) (start: hp_addr) : GTot nat =
  U64.v start + (U64.v (getWosize (read_word h start)) + 1) * U64.v mword

let walk_step_done (h: heap) (start: hp_addr) (objs: seq obj_addr)
  : Lemma
    (requires
      objs == objects start h /\
      Seq.length objs > 0 /\
      walk_next h start >= heap_size)
    (ensures Seq.tail objs == Seq.empty)
  = objects_nonempty_next start h;
    f_address_spec start;
    Seq.lemma_eq_elim (Seq.tail objs) Seq.empty

let walk_step_more (h: heap) (start: hp_addr) (objs: seq obj_addr)
  : Lemma
    (requires
      objs == objects start h /\
      Seq.length objs > 0 /\
      walk_next h start < heap_size)
    (ensures
      (let next : hp_addr = U64.uint_to_t (walk_next h start) in
       Seq.tail objs == objects next h /\
       U64.v next > U64.v start))
  = objects_nonempty_next start h;
    f_address_spec start;
    let next : hp_addr = U64.uint_to_t (walk_next h start) in
    Seq.lemma_tl (f_address start) (objects next h)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let sweep_white_facts (h: heap) (obj: obj_addr) (fp: U64.t)
  : Lemma
    (requires
      well_formed_heap h /\
      Seq.mem obj (objects zero_addr h) /\
      is_white obj h /\
      ~(is_infix obj h) /\
      U64.v (wosize_of_object obj h) >= 1 /\
      SpecSweep.fp_in_heap fp h)
    (ensures (
      let h1 = fst (SpecSweep.sweep_object h obj fp) in
      objects zero_addr h1 == objects zero_addr h /\
      is_blue obj h1 /\
      read_word h1 (obj <: obj_addr) == fp))
  = SpecSweep.sweep_object_preserves_objects h obj fp;
    SpecSweep.sweep_object_resets_self_color h obj fp;
    is_blue_iff obj (fst (SpecSweep.sweep_object h obj fp));
    objects_member_size_bound zero_addr h obj;
    wosize_of_object_spec obj h;
    SpecSweep.sweep_object_white_field0 h obj fp
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1 --split_queries always"
let sweep_white_blue_frame (h: heap) (obj: obj_addr) (fp: U64.t) (b: obj_addr)
  : Lemma
    (requires
      well_formed_heap h /\
      Seq.mem obj (objects zero_addr h) /\
      is_white obj h /\
      SpecSweep.fp_in_heap fp h /\
      Seq.mem b (objects zero_addr h) /\
      U64.v (wosize_of_object b h) >= 1 /\
      is_blue b h)
    (ensures (
      let h1 = fst (SpecSweep.sweep_object h obj fp) in
      is_blue b h1 /\
      read_word h1 (b <: obj_addr) == read_word h (b <: obj_addr)))
  = is_blue_iff obj h;
    is_white_iff obj h;
    is_blue_iff b h;
    assert (obj <> b);
    SpecSweep.sweep_object_color_locality h obj b fp;
    is_blue_iff b (fst (SpecSweep.sweep_object h obj fp));
    wosize_of_object_spec b h;
    SpecSweep.sweep_object_preserves_other_body_read h obj fp b b
#pop-options

val chain_decreasing_gives_all
  (g: heap) (fp: U64.t)
  : Lemma
    (requires
      free_list_complete g fp /\
      (forall (y: obj_addr).
        Seq.mem y (objects zero_addr g) /\ is_blue y g /\
        (fp <> 0UL ==> chain_reachable g (fp <: obj_addr) y) ==>
        (let v = read_word g y in
         v = 0UL \/ (is_pointer_field v /\ U64.v v < U64.v y))))
    (ensures blue_chain_decreasing g)

let chain_decreasing_gives_all g fp =
  let aux (y: obj_addr)
    : Lemma
      (requires Seq.mem y (objects zero_addr g) /\ is_blue y g)
      (ensures
        (let v = read_word g y in
         v = 0UL \/ (is_pointer_field v /\ U64.v v < U64.v y)))
    = ()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#push-options "--z3rlimit 800 --fuel 2 --ifuel 1 --split_queries always"
let rec sweep_establishes_complete h start objs fp =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    let (h1, fp1) = SpecSweep.sweep_object h obj fp in
    objects_nonempty_next start h;
    f_address_spec start;
    assert (obj == f_address start);
    if is_infix obj h then begin
      assert (h1 == h);
      assert (fp1 == fp);
      if walk_next h start >= heap_size then
        walk_step_done h start objs
      else begin
        walk_step_more h start objs;
        let next : hp_addr = U64.uint_to_t (walk_next h start) in
        sweep_establishes_complete h next rest fp
      end
    end
    else if is_white obj h then begin
      sweep_white_facts h obj fp;
      assert (objects zero_addr h1 == objects zero_addr h);
      assert (is_blue obj h1);
      assert (read_word h1 (obj <: obj_addr) == fp);
      let auxf (b: obj_addr)
        : Lemma
          (requires Seq.mem b (objects zero_addr h) /\ is_blue b h)
          (ensures
            is_blue b h1 /\
            read_word h1 (b <: obj_addr) == read_word h (b <: obj_addr))
        = sweep_white_blue_frame h obj fp b
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires auxf);
      let auxc (y: obj_addr{Seq.mem y (objects zero_addr h1)})
        : Lemma
          (requires is_blue y h1)
          (ensures chain_reachable h1 obj y)
        = if y = obj then begin
            let r : chain_reach h1 obj obj = ChainRefl obj in
            FStar.Classical.exists_intro
              (fun (_: chain_reach h1 obj y) -> True) r
          end
          else begin
            SpecSweep.sweep_object_color_locality h obj y fp;
            is_blue_iff y h;
            is_blue_iff y h1;
            assert (is_blue y h);
            sweep_white_blue_frame h obj fp y;
            if fp = 0UL then begin
              assert (is_blue y h);
              assert (Seq.mem y (objects zero_addr h));
              assert False
            end
            else begin
              assert (Seq.mem (fp <: obj_addr) (objects zero_addr h));
              assert (chain_reachable h (fp <: obj_addr) y);
              let aux2 (r0: chain_reach h (fp <: obj_addr) y)
                : Lemma (chain_reachable h1 obj y)
                = chain_reach_frame h h1 (fp <: obj_addr) y r0;
                  let aux3 (r1: chain_reach h1 (fp <: obj_addr) y)
                    : Lemma (chain_reachable h1 obj y)
                    = chain_reach_prepend h1 obj (fp <: obj_addr) y r1
                  in
                  FStar.Classical.exists_elim
                    (chain_reachable h1 obj y)
                    #(chain_reach h1 (fp <: obj_addr) y)
                    #(fun _ -> True)
                    ()
                    (fun r1 -> aux3 r1)
              in
              FStar.Classical.exists_elim
                (chain_reachable h1 obj y)
                #(chain_reach h (fp <: obj_addr) y)
                #(fun _ -> True)
                ()
                (fun r0 -> aux2 r0)
            end
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires auxc);
      if walk_next h start >= heap_size then
        walk_step_done h start objs
      else begin
        walk_step_more h start objs;
        let next : hp_addr = U64.uint_to_t (walk_next h start) in
        assert (rest == objects next h);
        objects_addresses_gt_start zero_addr h obj;
        SpecSweep.sweep_object_preserves_wf h obj fp;
        SpecSweep.sweep_object_preserves_objects_suffix start h fp;
        let auxw (x: obj_addr)
          : Lemma
            (requires Seq.mem x (objects zero_addr h))
            (ensures U64.v (wosize_of_object x h1) >= 1)
          = if x = obj then
              SpecSweep.sweep_object_preserves_self_wosize h obj fp
            else
              SpecSweep.sweep_object_preserves_other_header h obj fp x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires auxw);
        sweep_establishes_complete h1 next rest fp1
      end
    end
    else if is_black obj h then begin
      SpecSweep.sweep_object_preserves_objects h obj fp;
      SpecSweep.sweep_object_preserves_wf h obj fp;
      assert (fp1 == fp);
      assert (objects zero_addr h1 == objects zero_addr h);
      let auxb (b: obj_addr)
        : Lemma
          (requires Seq.mem b (objects zero_addr h) /\ is_blue b h)
          (ensures
            is_blue b h1 /\
            read_word h1 (b <: obj_addr) == read_word h (b <: obj_addr))
        = is_blue_iff b h;
          is_black_iff obj h;
          assert (obj <> b);
          SpecSweep.sweep_object_color_locality h obj b fp;
          is_blue_iff b h1;
          wosize_of_object_spec b h;
          SpecSweep.sweep_object_preserves_other_body_read h obj fp b b
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires auxb);
      if fp = 0UL then begin
        let auxz (y: obj_addr)
          : Lemma
            (requires Seq.mem y (objects zero_addr h1))
            (ensures ~(is_blue y h1))
          = SpecSweep.sweep_object_resets_self_color h obj fp;
            is_white_iff obj h1;
            is_blue_iff y h1;
            if y = obj then ()
            else begin
              SpecSweep.sweep_object_color_locality h obj y fp;
              is_blue_iff y h
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires auxz);
        objects_addresses_gt_start zero_addr h obj;
        SpecSweep.sweep_object_preserves_objects_suffix start h fp;
        let auxw (x: obj_addr)
          : Lemma
            (requires Seq.mem x (objects zero_addr h))
            (ensures U64.v (wosize_of_object x h1) >= 1)
          = if x = obj then
              SpecSweep.sweep_object_preserves_self_wosize h obj fp
            else
              SpecSweep.sweep_object_preserves_other_header h obj fp x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires auxw);
        if walk_next h start >= heap_size then
          walk_step_done h start objs
        else begin
          walk_step_more h start objs;
          let next : hp_addr = U64.uint_to_t (walk_next h start) in
          sweep_establishes_complete h1 next rest fp1
        end
      end
      else begin
        assert (Seq.mem (fp <: obj_addr) (objects zero_addr h1));
        let auxd (y: obj_addr{Seq.mem y (objects zero_addr h1)})
          : Lemma
            (requires is_blue y h1)
            (ensures chain_reachable h1 (fp <: obj_addr) y)
          = SpecSweep.sweep_object_resets_self_color h obj fp;
            is_white_iff obj h1;
            is_blue_iff y h1;
            assert (obj <> y);
            SpecSweep.sweep_object_color_locality h obj y fp;
            is_blue_iff y h;
            assert (is_blue y h);
            assert (chain_reachable h (fp <: obj_addr) y);
            let aux2 (r0: chain_reach h (fp <: obj_addr) y)
              : Lemma (chain_reachable h1 (fp <: obj_addr) y)
              = chain_reach_frame h h1 (fp <: obj_addr) y r0
            in
            FStar.Classical.exists_elim
              (chain_reachable h1 (fp <: obj_addr) y)
              #(chain_reach h (fp <: obj_addr) y)
              #(fun _ -> True)
              ()
              (fun r0 -> aux2 r0)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires auxd);
        objects_addresses_gt_start zero_addr h obj;
        SpecSweep.sweep_object_preserves_objects_suffix start h fp;
        let auxw (x: obj_addr)
          : Lemma
            (requires Seq.mem x (objects zero_addr h))
            (ensures U64.v (wosize_of_object x h1) >= 1)
          = if x = obj then
              SpecSweep.sweep_object_preserves_self_wosize h obj fp
            else
              SpecSweep.sweep_object_preserves_other_header h obj fp x
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires auxw);
        if walk_next h start >= heap_size then
          walk_step_done h start objs
        else begin
          walk_step_more h start objs;
          let next : hp_addr = U64.uint_to_t (walk_next h start) in
          sweep_establishes_complete h1 next rest fp1
        end
      end
    end
    else begin
      assert (h1 == h);
      assert (fp1 == fp);
      if walk_next h start >= heap_size then
        walk_step_done h start objs
      else begin
        walk_step_more h start objs;
        let next : hp_addr = U64.uint_to_t (walk_next h start) in
        sweep_establishes_complete h next rest fp
      end
    end
  end
#pop-options



#push-options "--z3rlimit 200"
let coalesce_establishes_decreasing h =
  let aux (x: obj_addr)
    : Lemma
      (requires Seq.mem x (objects zero_addr (fst (Coalesce.coalesce h))))
      (ensures
        (let g' = fst (Coalesce.coalesce h) in
         is_blue x g' ==>
         (let v = read_word g' x in
          v = 0UL \/
          (is_pointer_field v /\ U64.v v < U64.v x))))
    = Coalesce.coalesce_heap_unfold h h (objects zero_addr h) 0UL 0 0UL;
      admit()
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let coalesce_preserves_complete h fp = admit ()

val sweep_aux_preserves_wosize_member
  (g: heap) (objs: seq obj_addr) (fp: U64.t) (x: obj_addr)
  : Lemma
    (requires
      well_formed_heap g /\
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o (objects zero_addr g)) /\
      SpecSweep.fp_in_heap fp g /\
      Seq.mem x (objects zero_addr g))
    (ensures
      wosize_of_object x (fst (SpecSweep.sweep_aux g objs fp)) ==
      wosize_of_object x g)
    (decreases Seq.length objs)

let rec sweep_aux_preserves_wosize_member g objs fp x =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    let (g1, fp1) = SpecSweep.sweep_object g obj fp in
    if x = obj then
      SpecSweep.sweep_object_preserves_self_wosize g obj fp
    else
    SpecSweep.sweep_object_preserves_other_header g obj fp x;
    SpecSweep.sweep_object_preserves_wf g obj fp;
    SpecSweep.sweep_object_preserves_objects g obj fp;
    sweep_aux_preserves_wosize_member g1 rest fp1 x
  end

val sweep_preserves_wosize_all (g: heap) (fp: U64.t) (x: obj_addr)
  : Lemma
    (requires
      well_formed_heap g /\
      Seq.mem x (objects zero_addr g) /\
      SpecSweep.fp_in_heap fp g)
    (ensures
      wosize_of_object x (fst (SpecSweep.sweep g fp)) == wosize_of_object x g)

let sweep_preserves_wosize_all g fp x =
  sweep_aux_preserves_wosize_member g (objects zero_addr g) fp x

let gc_free_list_liveness h_init st fp =
  let h_mark = Mark.mark h_init st in
  let (h_sweep, fp_sweep) = SpecSweep.sweep h_mark fp in
  Correctness.mark_post_elim_wfh h_init h_mark st fp;
  Correctness.mark_post_elim_no_grey h_init h_mark st fp;
  Correctness.mark_post_elim_fp h_init h_mark st fp;
  sweep_establishes_complete h_mark zero_addr (objects zero_addr h_mark) fp;
  Correctness.sweep_post_sweep_strong_gen h_init h_mark st fp;
  SpecSweep.sweep_preserves_objects h_mark fp;
  let auxw (y: obj_addr)
    : Lemma
      (requires Seq.mem y (objects zero_addr h_mark))
      (ensures U64.v (wosize_of_object y h_sweep) >= 1)
    = sweep_preserves_wosize_all h_mark fp y
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires auxw);
  coalesce_establishes_decreasing h_sweep;
  coalesce_preserves_complete h_sweep fp_sweep