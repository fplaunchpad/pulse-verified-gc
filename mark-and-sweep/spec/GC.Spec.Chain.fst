module GC.Spec.Chain

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

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
                (y: obj_addr{Seq.mem y (objects zero_addr g) /\ is_blue y g}) ->
                (z: obj_addr{Seq.mem z (objects zero_addr g) /\ fl_edge g y z}) ->
                chain_reach g x y ->
                chain_reach g x z

let chain_reachable (g: heap)
                    (x: obj_addr{Seq.mem x (objects zero_addr g)})
                    (y: obj_addr{Seq.mem y (objects zero_addr g)}) : prop =
  exists (r: chain_reach g x y). True

val chain_reach_frame (g g': heap)
  (x: obj_addr{Seq.mem x (objects zero_addr g)})
  (y: obj_addr{Seq.mem y (objects zero_addr g)})
  (r: chain_reach g x y)
  : Lemma
    (requires
      objects zero_addr g' == objects zero_addr g /\
      (forall (b: obj_addr).
        Seq.mem b (objects zero_addr g) /\ is_blue b g ==>
        read_word g' (b <: obj_addr) == read_word g (b <: obj_addr)) /\
      (forall (b: obj_addr).
        Seq.mem b (objects zero_addr g) /\ is_blue b g ==> is_blue b g'))
    (ensures chain_reachable g' x y)
    (decreases r)

let rec chain_reach_frame g g' x y r =
  match r with
  | ChainRefl _ ->
      let r' : chain_reach g' x x = ChainRefl x in
      FStar.Classical.exists_intro (fun (_: chain_reach g' x y) -> True) r'
  | ChainStep _ w z prev ->
      chain_reach_frame g g' x w prev;
      assert (is_blue w g);
      assert (read_word g' (w <: obj_addr) == read_word g (w <: obj_addr));
      assert (fl_edge g' w z);
      let aux (r0: chain_reach g' x w)
        : Lemma (chain_reachable g' x z)
        = let r1 : chain_reach g' x z = ChainStep x w z r0 in
          FStar.Classical.exists_intro (fun (_: chain_reach g' x z) -> True) r1
      in
      FStar.Classical.exists_elim
        (chain_reachable g' x z)
        #(chain_reach g' x w)
        #(fun _ -> True)
        ()
        (fun r0 -> aux r0)

val chain_reach_prepend (g: heap)
  (w: obj_addr{Seq.mem w (objects zero_addr g) /\ is_blue w g})
  (x: obj_addr{Seq.mem x (objects zero_addr g)})
  (y: obj_addr{Seq.mem y (objects zero_addr g)})
  (r: chain_reach g x y)
  : Lemma
    (requires fl_edge g w x)
    (ensures chain_reachable g w y)
    (decreases r)

let rec chain_reach_prepend g w x y r =
  match r with
  | ChainRefl _ ->
      let r0 : chain_reach g w w = ChainRefl w in
      let r1 : chain_reach g w x = ChainStep w w x r0 in
      FStar.Classical.exists_intro (fun (_: chain_reach g w y) -> True) r1
  | ChainStep _ u z prev ->
      chain_reach_prepend g w x u prev;
      let aux (r0: chain_reach g w u)
        : Lemma (chain_reachable g w z)
        = let r1 : chain_reach g w z = ChainStep w u z r0 in
          FStar.Classical.exists_intro (fun (_: chain_reach g w z) -> True) r1
      in
      FStar.Classical.exists_elim
        (chain_reachable g w z)
        #(chain_reach g w u)
        #(fun _ -> True)
        ()
        (fun r0 -> aux r0)
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