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

let rec on_chain (g: heap) (a: U64.t) (x: obj_addr) (n: nat)
  : GTot bool (decreases n) =
  if a = 0UL then false
  else if not (is_pointer_field a) then false
  else if a = (x <: U64.t) then true
  else if n = 0 then false
  else on_chain g (read_word g (a <: obj_addr)) x (n - 1)

let free_list_complete (g: heap) (fp: U64.t) : prop =
  forall (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ is_blue x g ==>
    on_chain g fp x (heap_size / U64.v mword)

let free_list_liveness (g: heap) (fp: U64.t) : prop =
  blue_chain_decreasing g /\ free_list_complete g fp

val sweep_establishes_liveness
  (h: heap) (start: hp_addr) (objs: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      objs == objects start h /\
      (forall (x: obj_addr).
        Seq.mem x (objects zero_addr h) ==>
        U64.v (wosize_of_object x h) >= 1) /\
      free_list_liveness h fp /\
      (fp = 0UL \/ is_pointer_field fp))
    (ensures (let (h', fp') = SpecSweep.sweep_aux h objs fp in
              free_list_liveness h' fp'))
    (decreases Seq.length objs)

val coalesce_preserves_decreasing (h: heap)
  : Lemma (requires blue_chain_decreasing h)
          (ensures blue_chain_decreasing (fst (Coalesce.coalesce h)))

val coalesce_preserves_complete (h: heap) (fp: U64.t)
  : Lemma (requires free_list_liveness h fp)
          (ensures (let (h', fp') = Coalesce.coalesce h in
                    free_list_complete h' fp'))

val gc_free_list_liveness (h_init: heap) (st: seq obj_addr) (fp: U64.t)
  : Lemma
    (requires
      (let h_mark = Mark.mark h_init st in
       (forall (x: obj_addr).
         Seq.mem x (objects zero_addr h_mark) ==>
         U64.v (wosize_of_object x h_mark) >= 1) /\
       free_list_liveness h_mark fp /\
       (fp = 0UL \/ is_pointer_field fp)))
    (ensures (let h_sweep = fst (SpecSweep.sweep (Mark.mark h_init st) fp) in
              let (h_final, fp_final) = Coalesce.coalesce h_sweep in
              free_list_liveness h_final fp_final))

let rec sweep_establishes_liveness h start objs fp =
  if Seq.length objs = 0 then ()
  else begin
    let obj = Seq.head objs in
    let rest = Seq.tail objs in
    let (h1, fp1) = SpecSweep.sweep_object h obj fp in
    admit ()
  end

let coalesce_preserves_decreasing h = admit ()
let coalesce_preserves_complete h fp = admit ()

let gc_free_list_liveness h_init st fp =
  let h_mark = Mark.mark h_init st in
  let (h_sweep, fp_sweep) = SpecSweep.sweep h_mark fp in
  sweep_establishes_liveness h_mark zero_addr (objects zero_addr h_mark) fp;
  coalesce_preserves_decreasing h_sweep;
  coalesce_preserves_complete h_sweep fp_sweep