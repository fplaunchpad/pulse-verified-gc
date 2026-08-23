(*
   Pulse GC - Closure Module Interface

   Handles OCaml closure and infix objects during GC.
*)

module GC.Impl.Closure

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Fields
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object


/// ---------------------------------------------------------------------------
/// Ghost specification of infix resolution
/// ---------------------------------------------------------------------------

/// What `parent_closure_of_infix_opt` computes: the *header* address of the parent
/// closure of the infix sub-object whose header sits at `infix_addr`, or None when the
/// offset stored in that header does not land on a valid object address.
///
/// `GC.Spec.Object.parent_closure_addr_nat` reads the offset body-to-body, which is
/// OCaml's convention (`mlvalues.h` `Infix_offset_hd`, `major_gc.c:288`
/// `v -= Infix_offset_val(v)`), and is what this function has always computed:
/// `(infix_hdr + 8) - offset * 8`. The spec definition agreed only after commit
/// `02d1743`; before that it subtracted an extra word and this postcondition would
/// have been unprovable.
let parent_closure_of_infix_spec
      (s: heap_state) (infix_addr: hp_addr{U64.v infix_addr + U64.v mword < heap_size})
  : GTot (option hp_addr)
  = let x = SpecHeap.f_address infix_addr in
    let pn = SpecObject.parent_closure_addr_nat x s in
    if pn >= U64.v mword && pn < heap_size && pn % U64.v mword = 0
    then Some (SpecHeap.hd_address (U64.uint_to_t pn))
    else None

/// Read closure info value (field 2 of closure)
fn closinfo_val (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's **
           pure (spec_field_address (U64.v h_addr) 2 < heap_size)
  returns v: U64.t
  ensures is_heap heap 's

/// Extract start_env from closinfo
fn start_env_from_closinfo (closinfo: U64.t)
  requires emp
  returns start_env: U64.t
  ensures emp

/// Check if object is an infix object
fn is_infix_object (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's **
          pure (b == SpecObject.is_infix (SpecHeap.f_address h_addr) 's)

/// Check if object is a closure
fn is_closure_object (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's

/// Get parent closure of infix object (returns None if offset invalid)
fn parent_closure_of_infix_opt
      (heap: heap_t) (infix_addr: hp_addr{U64.v infix_addr + U64.v mword < heap_size})
  requires is_heap heap 's
  returns parent_opt: option hp_addr
  ensures is_heap heap 's **
          pure (parent_opt == parent_closure_of_infix_spec 's infix_addr)

/// Get parent closure of infix object (falls back to infix_addr)
fn parent_closure_of_infix
      (heap: heap_t) (infix_addr: hp_addr{U64.v infix_addr + U64.v mword < heap_size})
  requires is_heap heap 's
  returns parent: hp_addr
  ensures is_heap heap 's **
          pure (parent == (match parent_closure_of_infix_spec 's infix_addr with
                           | Some p -> p
                           | None -> infix_addr))

/// Resolve object: if infix, return parent closure; otherwise return as-is.
///
/// The functional postcondition is what makes this usable by the major mark phase:
/// it says the runtime computation agrees with the ghost `resolve_object`, over which
/// `GC.Spec.Mark.push_children` and the tri-colour invariant are already stated.
/// Without it -- as this function stood until now -- a disagreement with the ghost
/// definition is invisible, which is exactly how the body-to-header confusion fixed in
/// `02d1743` survived so long.
fn resolve_object (heap: heap_t) (obj: hp_addr{U64.v obj + U64.v mword < heap_size})
  requires is_heap heap 's
  returns resolved: hp_addr
  ensures is_heap heap 's **
          pure (resolved ==
                SpecHeap.hd_address (SpecObject.resolve_object (SpecHeap.f_address obj) 's))

/// Scan closure environment, calling callback for each pointer field
fn scan_closure_env (heap: heap_t) (h_addr: hp_addr) (wz: wosize)
                     (callback: U64.t -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's **
           pure (spec_field_address (U64.v h_addr) 2 < heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz) < heap_size /\
                 U64.v wz >= 1 /\ U64.v wz <= pow2 54 - 1)
  ensures is_heap heap 's

/// Check if object has tag >= no_scan_tag
fn is_no_scan (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's
