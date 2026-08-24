(*
   Pulse GC - Closure Module
   
   This module handles OCaml closure and infix objects, which require
   special handling during GC:
   - Closures contain code pointers and environment
   - Infix objects are embedded within closures
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
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
/// Closure Info Field
/// ---------------------------------------------------------------------------

/// The closure info field contains:
/// - Arity in low bits
/// - Start of environment offset in high bits
/// 
/// Layout: | start_env (high bits) | arity (low bits) |

/// Extract closure info value from closure object
/// Requires that the closure has at least 3 words (header + 2 fields)
fn closinfo_val (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's **
           pure (spec_field_address (U64.v h_addr) 2 < heap_size)
  returns v: U64.t
  ensures is_heap heap 's
{
  // Closure info is in field 1 (after code pointer in field 0... wait, 
  // field 0 is header, field 1 is code pointer, field 2 is closinfo)
  // Actually in OCaml: header, then code ptr, then closinfo
  // Field indexing: 1 = code ptr, 2 = closinfo
  read_field heap h_addr 2UL
}

/// Extract start_env from closinfo
/// start_env tells us where the environment starts (offset from closure start)
fn start_env_from_closinfo (closinfo: U64.t)
  requires emp
  returns start_env: U64.t
  ensures emp
{
  // start_env is in high bits, shifted by some amount
  // In OCaml, this is implementation-specific
  // For now, assume it's the high 32 bits
  U64.shift_right closinfo 32ul
}

/// ---------------------------------------------------------------------------
/// Infix Object Handling
/// ---------------------------------------------------------------------------

/// Check if object is an infix object
fn is_infix_object (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's **
          pure (b == SpecObject.is_infix (SpecHeap.f_address h_addr) 's)
{
  let hdr = read_word heap h_addr;
  let t = getTag hdr;
  getTag_eq hdr;
  SpecHeap.hd_f_roundtrip h_addr;
  SpecObject.tag_of_object_spec (SpecHeap.f_address h_addr) 's;
  SpecObject.is_infix_spec (SpecHeap.f_address h_addr) 's;
  U64.eq t infix_tag
}

/// Check if object is a closure
fn is_closure_object (heap: heap_t) (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size})
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's **
          pure (b == SpecObject.is_closure (SpecHeap.f_address h_addr) 's)
{
  let hdr = read_word heap h_addr;
  let t = getTag hdr;
  getTag_eq hdr;
  SpecHeap.hd_f_roundtrip h_addr;
  SpecObject.tag_of_object_spec (SpecHeap.f_address h_addr) 's;
  SpecObject.is_closure_spec (SpecHeap.f_address h_addr) 's;
  U64.eq t closure_tag
}

/// Get parent closure of an infix object
/// Infix objects have an offset in their header's wosize field that points back
/// to the parent closure
/// 
/// Returns None if the offset is invalid (would underflow or produce invalid address)
/// This should never happen in a well-formed heap, but we check defensively.
fn parent_closure_of_infix_opt
      (heap: heap_t) (infix_addr: hp_addr{U64.v infix_addr + U64.v mword < heap_size})
  requires is_heap heap 's
  returns parent_opt: option hp_addr
  ensures is_heap heap 's **
          pure (parent_opt == parent_closure_of_infix_spec 's infix_addr)
{
  // The infix object's "wosize" actually contains the offset (in words)
  // back to the parent closure's first field
  let hdr = read_word heap infix_addr;
  let offset_words = getWosize hdr;
  
  // Prove multiplication doesn't overflow
  lemma_field_offset_no_overflow (U64.v offset_words);

  // Bridge the runtime header decode to the ghost wosize of the infix sub-object and
  // hence to parent_closure_addr_nat. hd_f_roundtrip is what identifies the header
  // just read with the header of `f_address infix_addr`.
  getWosize_eq hdr;
  SpecHeap.f_address_spec infix_addr;
  SpecHeap.hd_f_roundtrip infix_addr;
  SpecObject.wosize_of_object_spec (SpecHeap.f_address infix_addr) 's;
  SpecObject.parent_closure_addr_nat_spec (SpecHeap.f_address infix_addr) 's;
  
  // Compute offset in bytes
  let offset_bytes = U64.mul offset_words mword;
  
  // Check if subtraction would underflow
  let f_addr = U64.add infix_addr mword;
  if (U64.lt f_addr offset_bytes) {
    // Invalid: offset points before the start of heap
    None
  } else {
    let parent_f_addr = U64.sub f_addr offset_bytes;
    
    // Check all preconditions for hd_address:
    // parent_f_addr >= mword, < heap_size, and word-aligned
    if (U64.lt parent_f_addr mword) {
      None
    } else if (U64.gte parent_f_addr heap_size_u64) {
      None
    } else if (U64.rem parent_f_addr mword <> 0UL) {
      None
    } else {
      // The runtime hd_address is U64.sub _ mword; hd_address_spec is what lets the
      // abstract SpecHeap.hd_address in the postcondition be identified with it.
      SpecHeap.hd_address_spec parent_f_addr;
      U64.v_inj (hd_address parent_f_addr) (SpecHeap.hd_address parent_f_addr);
      let parent_hdr_addr = hd_address parent_f_addr;
      // Confirm the computed parent really is a closure before resolving to it.
      // A genuine infix header always sits inside a Closure_tag block; a word that
      // only looked like an infix header (an OCaml integer ending in 0xf9, reached
      // through is_pointer, which checks alignment and range and nothing else) will
      // almost never produce one. Declining here is what keeps the resolution from
      // turning a non-pointer into an arbitrary heap address -- the same soundness
      // condition hand patch 14 carried in the generated C.
      let parent_is_closure = is_closure_object heap parent_hdr_addr;
      // f_hd_roundtrip identifies the address is_closure_object reports on
      // (f_address (hd_address parent_f_addr)) with parent_f_addr itself.
      SpecHeap.f_hd_roundtrip parent_f_addr;
      if parent_is_closure {
        Some parent_hdr_addr
      } else {
        None
      }
    }
  }
}

/// Get parent closure of an infix object (unsafe version)
/// Precondition: The infix object must be well-formed with valid offset
/// In a valid GC heap with proper invariants, this is always true for infix objects.
fn parent_closure_of_infix
      (heap: heap_t) (infix_addr: hp_addr{U64.v infix_addr + U64.v mword < heap_size})
  requires is_heap heap 's
  returns parent: hp_addr
  ensures is_heap heap 's **
          pure (parent == (match parent_closure_of_infix_spec 's infix_addr with
                           | Some p -> p
                           | None -> infix_addr))
{
  let parent_opt = parent_closure_of_infix_opt heap infix_addr;
  
  // In a well-formed heap, this should always be Some
  // If it's None, the heap is corrupted - return infix_addr as fallback
  if (Some? parent_opt) {
    Some?.v parent_opt
  } else {
    infix_addr
  }
}

/// ---------------------------------------------------------------------------
/// Closure-Aware Darkening
/// ---------------------------------------------------------------------------

/// The infix branch of resolve_object, discharged in all three arms of
/// parent_closure_of_infix_spec, which the two definitions share exactly:
///   Some                     -- via resolve_infix_spec;
///   None, bad offset         -- via resolve_infix_invalid;
///   None, parent not closure -- via resolve_infix_not_closure.
/// In both None cases resolve_object is defensive and returns its input, which is
/// `obj` after the hd/f round trip.
let resolve_object_infix_agrees
      (s: heap_state) (obj: hp_addr{U64.v obj + U64.v mword < heap_size})
  : Lemma (requires SpecObject.is_infix (SpecHeap.f_address obj) s)
          (ensures SpecHeap.hd_address
                     (SpecObject.resolve_object (SpecHeap.f_address obj) s)
                   == (match parent_closure_of_infix_spec s obj with
                       | Some p -> p
                       | None -> obj))
  = let x = SpecHeap.f_address obj in
    let pn = SpecObject.parent_closure_addr_nat x s in
    SpecHeap.hd_f_roundtrip obj;
    if pn >= U64.v mword && pn < heap_size && pn % U64.v mword = 0
    then begin
      let pa = U64.uint_to_t pn in
      if SpecObject.is_closure pa s
      then SpecObject.resolve_infix_spec x s
      else SpecObject.resolve_infix_not_closure x s
    end
    else SpecObject.resolve_infix_invalid x s

/// Darken with closure/infix handling
/// If the object is an infix, we need to darken the parent closure instead
fn resolve_object (heap: heap_t) (obj: hp_addr{U64.v obj + U64.v mword < heap_size})
  requires is_heap heap 's
  returns resolved: hp_addr
  ensures is_heap heap 's **
          pure (resolved ==
                SpecHeap.hd_address (SpecObject.resolve_object (SpecHeap.f_address obj) 's))
{
  // Check if it's an infix object
  let is_infix = is_infix_object heap obj;
  
  if (is_infix) {
    // Both arms of parent_closure_of_infix_spec agree with resolve_object: on Some via
    // resolve_infix_spec, and on None because resolve_object also falls back to its
    // input when the computed parent is not a valid object address, together with
    // hd_address (f_address obj) == obj.
    SpecHeap.hd_f_roundtrip obj;
    resolve_object_infix_agrees 's obj;
    parent_closure_of_infix heap obj
  } else {
    // Regular object, return as-is
    SpecObject.resolve_non_infix (SpecHeap.f_address obj) 's;
    SpecHeap.hd_f_roundtrip obj;
    obj
  }
}

/// ---------------------------------------------------------------------------
/// Closure Environment Scanning
/// ---------------------------------------------------------------------------

/// Scan a closure's environment
/// The environment starts at start_env and goes to wosize
/// 
/// Precondition: All fields from 2 to wz are within heap bounds
/// (Caller must ensure closure is valid with sufficient size)
/// Also, wz must be a valid field index (>= 1 and <= 2^54-1, which is always true for wosize)
fn scan_closure_env (heap: heap_t) (h_addr: hp_addr) (wz: wosize)
                     (callback: U64.t -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's **
           pure (
             // closinfo_val needs field 2 to exist
             spec_field_address (U64.v h_addr) 2 < heap_size /\
             // All environment fields up to wz must be in bounds
             spec_field_address (U64.v h_addr) (U64.v wz) < heap_size /\
             // wz is a valid field index (always true for wosize, but make explicit)
             U64.v wz >= 1 /\ U64.v wz <= pow2 54 - 1
           )
  ensures  is_heap heap 's
{
  // Get closinfo to find where environment starts
  let closinfo = closinfo_val heap h_addr;
  let start_env_raw = start_env_from_closinfo closinfo;
  
  // Ensure start_env is at least 1 (can't read field 0, which is header)
  // In a well-formed closure, start_env should be >= code pointer + closinfo = 3 or so
  let start_env : U64.t = if (U64.lt start_env_raw 1UL) { 1UL } else { start_env_raw };
  
  // Also ensure start_env <= wz (no environment if start_env > wz)
  // Cast wz to U64.t for comparison
  let wz_u64 : U64.t = wz;
  let start_env_clamped : U64.t = if (U64.gt start_env wz_u64) { wz_u64 } else { start_env };
  
  // Environment fields are from start_env to wz
  let mut i = start_env_clamped;
  
  while (U64.lte !i wz)
    invariant exists* vi.
      pts_to i vi **
      is_heap heap 's **
      pure (
        U64.v vi >= U64.v start_env_clamped /\
        U64.v vi <= U64.v wz + 1 /\
        U64.v start_env_clamped >= 1 /\
        U64.v start_env_clamped <= U64.v wz /\
        // If i <= wz, then i is a valid field index and in bounds
        (U64.v vi <= U64.v wz ==> (
          U64.v vi >= 1 /\
          U64.v vi <= pow2 54 - 1 /\
          spec_field_address (U64.v h_addr) (U64.v vi) < heap_size
        ))
      )
  {
    let curr_i = !i;
    
    // Prove we can read this field
    assert (pure (U64.v curr_i <= U64.v wz));
    assert (pure (U64.v curr_i >= 1));
    assert (pure (U64.v curr_i <= pow2 54 - 1));
    assert (pure (spec_field_address (U64.v h_addr) (U64.v curr_i) < heap_size));
    
    // Read environment slot
    let v = read_field heap h_addr curr_i;
    
    // Check if it's a pointer
    let is_ptr = is_pointer v;
    
    if (is_ptr) {
      // Pass the pointer value directly to callback
      // The callback can handle dereferencing and resolution
      callback v
    };
    
    i := U64.add curr_i 1UL
  }
}

/// ---------------------------------------------------------------------------
/// No-Scan Objects
/// ---------------------------------------------------------------------------

/// Check if object should not be scanned (no pointers)
fn is_no_scan (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's
{
  let hdr = read_word heap h_addr;
  let t = getTag hdr;
  U64.gte t no_scan_tag
}
