module GC.Spec.FreeListLiveness

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module SpecSweep = GC.Spec.Sweep
module Coalesce  = GC.Spec.Coalesce
module Mark = GC.Spec.Mark

let blue_chain_decreasing (g: heap) : prop =
  forall (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ is_blue x g ==>
    (let v = read_word g x in
     v = 0UL \/
     (is_pointer_field v /\
      U64.v v < U64.v x /\
      Seq.mem (v <: obj_addr) (objects zero_addr g) /\
      is_blue (v <: obj_addr) g))

/// Free-list edge: field 1 of x points to y
let fl_edge (g: heap) (x y: obj_addr) : prop =
  read_word g (x <: obj_addr) == (y <: U64.t)

/// x reaches y by following field-1 pointers.
noeq type chain_reach (g: heap)
  : (x: obj_addr{Seq.mem x (objects zero_addr g)}) ->
    (y: obj_addr{Seq.mem y (objects zero_addr g)}) -> Type =
  | ChainRefl : (x: obj_addr{Seq.mem x (objects zero_addr g)}) ->
                chain_reach g x x
  | ChainStep : (x: obj_addr{Seq.mem x (objects zero_addr g)}) ->
                (y: obj_addr{Seq.mem y (objects zero_addr g)}) ->
                (z: obj_addr{Seq.mem z (objects zero_addr g) /\ fl_edge g y z}) ->
                chain_reach g x y ->
                chain_reach g x z

let chain_reachable (g: heap)
                    (x: obj_addr{Seq.mem x (objects zero_addr g)})
                    (y: obj_addr{Seq.mem y (objects zero_addr g)}) : prop =
  exists (r: chain_reach g x y). True

let free_list_complete (g: heap) (fp: U64.t) : prop =
  fp = 0UL \/
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
  : Lemma (ensures blue_chain_decreasing (fst (Coalesce.coalesce h)))

val coalesce_preserves_complete (h: heap) (fp: U64.t)
  : Lemma
    (requires free_list_complete h fp)
    (ensures (let (h', fp') = Coalesce.coalesce h in
              free_list_complete h' fp'))

val gc_free_list_liveness (h_init: heap) (st: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
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

let rec sweep_establishes_complete h start objs fp =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    let (h1, fp1) = SpecSweep.sweep_object h obj fp in
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
      SpecSweep.sweep_object_preserves_objects h obj fp;
      assert (Seq.mem obj (objects zero_addr h1));
      let r : chain_reach h1 obj obj = ChainRefl obj in
      FStar.Classical.exists_intro (fun (_: chain_reach h1 obj obj) -> True) r;
      objects_member_size_bound zero_addr h obj;
      wosize_of_object_spec obj h;
      SpecSweep.sweep_object_white_field0 h obj fp;
      assert (read_word h1 obj == fp);
      admit ()
    end
    else if is_black obj h then admit ()
    else admit ()
  end

let coalesce_establishes_decreasing h = admit ()
let coalesce_preserves_complete h fp = admit ()

let gc_free_list_liveness h_init st fp =
  let h_mark = Mark.mark h_init st in
  let (h_sweep, fp_sweep) = SpecSweep.sweep h_mark fp in
  sweep_establishes_complete h_mark zero_addr (objects zero_addr h_mark) fp;
  coalesce_establishes_decreasing h_sweep;
  coalesce_preserves_complete h_sweep fp_sweep