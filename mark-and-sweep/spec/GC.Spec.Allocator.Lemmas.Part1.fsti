(*
   GC.Spec.Allocator.Lemmas.Part1 — Interface for Section P1 proofs.

   alloc_spec / alloc_from_block preserve object membership under
   well_formed_heap_part1 (weaker precondition than well_formed_heap).
*)
module GC.Spec.Allocator.Lemmas.Part1

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Helper: establish all common facts from a split-or-fragment allocation
/// under part1.
///
/// Relaxed from `block_wz - wz >= 2` to `>= 1`.  A split and a one-word
/// leftover write the SAME first two words -- the object header at `hd`,
/// declaring exactly `wz`, and a second header `1 + wz` words above it, of
/// wosize `block_wz - wz - 1` (which is 0 for the one-word leftover: the
/// header-only block).  They differ only in the third write: a split links the
/// remainder into the free list, whereas the fragment has no body word to hold
/// a link, so the block leaves the list and `next_fp` is returned unchanged.
/// Everything up to and including `g2` is therefore shared, and only the
/// `>= 2` conjunct mentions `rem_obj`.
val alloc_split_facts_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 1))
        (ensures (let hd = hd_address obj in
                  let hdr = read_word g hd in
                  let block_wz = U64.v (getWosize hdr) in
                  let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                  let next_hd_nat = U64.v hd + (block_wz + 1) * 8 in
                  let rem_wz = block_wz - wz - 1 in
                  rem_hd_nat >= 8 /\
                  rem_hd_nat < heap_size /\
                  next_hd_nat <= heap_size /\
                  next_hd_nat % 8 == 0 /\
                  rem_hd_nat % 8 == 0 /\
                  rem_hd_nat < pow2 64 /\
                  next_hd_nat < pow2 64 /\
                  wz < pow2 54 /\
                  rem_wz < pow2 54 /\
                  getWosize (make_header (U64.uint_to_t wz) white_bits 0UL) == U64.uint_to_t wz /\
                  getWosize (make_header (U64.uint_to_t rem_wz) blue_bits 0UL) == U64.uint_to_t rem_wz /\
                  (let alloc_hdr = make_header (U64.uint_to_t wz) white_bits 0UL in
                   let g1 = write_word g hd alloc_hdr in
                   let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
                   let rem_hdr = make_header (U64.uint_to_t rem_wz) blue_bits 0UL in
                   let g2 = write_word g1 rem_hd rem_hdr in
                   Seq.length g2 == Seq.length g /\
                   read_word g2 hd == alloc_hdr /\
                   read_word g2 rem_hd == rem_hdr /\
                   getWosize (read_word g2 hd) == U64.uint_to_t wz /\
                   getWosize (read_word g2 rem_hd) == U64.uint_to_t rem_wz /\
                   // One-word leftover: two writes, and the block leaves the list.
                   (block_wz - wz == 1 ==>
                     (alloc_from_block g obj wz next_fp == (g2, next_fp) /\
                      (next_hd_nat < heap_size ==>
                        objects (U64.uint_to_t next_hd_nat <: hp_addr) g2 ==
                        objects (U64.uint_to_t next_hd_nat <: hp_addr) g))) /\
                   // Split: a third write links the remainder, which becomes fp.
                   (block_wz - wz >= 2 ==>
                     (let rem_obj_nat = rem_hd_nat + 8 in
                      rem_obj_nat >= 16 /\
                      rem_obj_nat < heap_size /\
                      rem_obj_nat % 8 == 0 /\
                      rem_obj_nat < pow2 64 /\
                      (let rem_obj : hp_addr = U64.uint_to_t rem_obj_nat in
                       let g3 = write_word g2 rem_obj next_fp in
                       alloc_from_block g obj wz next_fp == (g3, rem_obj) /\
                       Seq.length g3 == Seq.length g /\
                       read_word g3 hd == alloc_hdr /\
                       read_word g3 rem_hd == rem_hdr /\
                       getWosize (read_word g3 hd) == U64.uint_to_t wz /\
                       getWosize (read_word g3 rem_hd) == U64.uint_to_t rem_wz /\
                       (next_hd_nat < heap_size ==>
                         objects (U64.uint_to_t next_hd_nat <: hp_addr) g3 ==
                         objects (U64.uint_to_t next_hd_nat <: hp_addr) g)))))))

/// Helper: the output heap agrees with g at non-write positions under part1.
///
/// Relaxed to `block_wz - wz >= 1`.  The third address, `rem_obj`, is only
/// written on a split, so at a one-word leftover the caller need not exclude
/// it -- but excluding it is harmless and keeps every existing call site
/// unchanged.
val alloc_split_g3_agrees_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (p: hp_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hd = hd_address obj in
                   let hdr = read_word g hd in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 1 /\
                   (let rem_hd_nat = U64.v hd + (1 + wz) * 8 in
                    let rem_obj_nat = rem_hd_nat + 8 in
                    U64.v p <> U64.v hd /\
                    U64.v p <> rem_hd_nat /\
                    (block_wz - wz >= 2 ==> U64.v p <> rem_obj_nat))))
        (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                  read_word g3 p == read_word g p))

/// Old objects are in new objects after split (part1 variant)
val alloc_split_old_in_new_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (h: obj_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let block_wz = U64.v (getWosize hdr) in
                   block_wz >= wz /\ block_wz - wz >= 1) /\
                  Seq.mem h (objects zero_addr g))
        (ensures (let (g3, _) = alloc_from_block g obj wz next_fp in
                  Seq.mem h (objects zero_addr g3)))

/// alloc_from_block preserves objects membership under part1
val alloc_from_block_objects_facts_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))

/// Writing within an object body preserves the objects enumeration
val write_body_preserves_objects_local :
  (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (requires
      Seq.mem obj (objects start g) /\
      U64.v addr >= U64.v obj /\
      U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
      U64.v addr % 8 = 0)
    (ensures objects start (write_word g addr v) == objects start g)
    (decreases (Seq.length g - U64.v start))

/// **Theorem**: alloc_from_block preserves object membership under just
/// well_formed_heap_part1. (Public wrapper for internal part1 proof.)
val alloc_from_block_preserves_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))

/// **Theorem**: In the split case (block_wz - wz >= 2), the remainder fp
/// returned by alloc_from_block is a valid pointer AND is in objects of
/// the output heap. Requires only well_formed_heap_part1.
/// **Theorem**: the header-only fragment created at a one-word leftover is an
/// object of the output heap.
///
/// Needs room for its (empty) object address: `hd + (bwz + 1) * 8 < heap_size`.
/// When that fails the fragment header is the heap's last word and `objects`
/// stops before it -- correctly, since a header with no room for a field is
/// not a block.
val alloc_from_block_frag_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hd = hd_address obj in
                   let bwz = U64.v (getWosize (read_word g hd)) in
                   bwz >= wz /\ bwz - wz == 1 /\
                   U64.v hd + (bwz + 1) * 8 < heap_size))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  let hd = hd_address obj in
                  let fhn = U64.v hd + (1 + wz) * 8 in
                  fhn < heap_size /\ fhn % 8 == 0 /\
                  (let fh : hp_addr = U64.uint_to_t fhn in
                   U64.v (f_address fh) < heap_size /\
                   Seq.mem (f_address fh) (objects zero_addr g'))))

val alloc_from_block_rem_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ bwz - wz >= 2))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  is_pointer_field rem_fp /\
                  Seq.mem rem_fp (objects zero_addr g')))
