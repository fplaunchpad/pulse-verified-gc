# Hand Patches: _extract/ → ocaml-integration/verified_gc/

Every difference between the KaRaMeL extraction output (`_extract/`) and the
copy used in the OCaml runtime integration (`ocaml-integration/verified_gc/`)
represents **unverified code**.  This document catalogues each patch, explains
why it was needed, and gives a plan to eliminate it by fixing the verified
F\*/Pulse source so the extraction is usable directly.

---

## Current Status (updated 2025-06-14)

### Extraction Patches (GC_Gen_Impl.c)

| # | Patch | Status | Notes |
|---|-------|--------|-------|
| 5  | No-scan skip in update_all | ✅ **DONE** | Verified `is_no_scan_eq` + `getTag` check in `UpdatePtrs.fst` |
| 7  | darken non-static | ✅ **DONE** | `GC.Impl.MarkBounded` added to API bundle in Makefile |
| 10 | Tag preservation in promote | ✅ **DONE** | `Impl.Promote.fst` reads minor tag, uses `Obj.makeHeader` (clean extraction) |
| 6  | rescan_heap_impl start | ✅ **DONE** | Impl now starts at `zero_addr` (= 0UL in spec) |
| 11 | `is_pointer` lower bound | ✅ **ELIMINATED** | Verified code uses `U64.add zero_addr mword`, extracts as `zero_addr + 8ULL` |
| 12 | `is_valid_fp` lower bound | ✅ **ELIMINATED** | Verified code uses `U64.add zero_addr mword`, extracts as `zero_addr + 8ULL` |
| 13 | krmlinit | ✅ Minimal | Only sets `queue_size_sz` and `minor_heap_size_sz` |
| B13 | compat.c extern primitives | ✅ **DONE** | Implements `read_u64_le`/`write_u64_le` + provides `zero_addr`/`heap_size_u64` storage |
| B14b | fwd_array_size alias | ✅ **DONE** | Bridge uses `queue_size_sz` directly |
| 8  | update_all_objects start | ✅ **DONE** | Impl now starts at `zero_addr` instead of `0UL` |
| 1  | zero_addr non-static | ✅ **ELIMINATED** | `zero_addr` is now `extern` from `GC.Spec.ZeroAddr.fsti`; defined in `compat.c` |
| 2  | Configurable heap_size | ✅ **ELIMINATED** | `heap_size_u64` is now `extern` from `GC.Spec.ZeroAddr.fsti`; defined in `compat.c` |
| 3,4 | Scan range / HWM | ✅ **ELIMINATED** | Bridge now walks fwd_arr + calls `update_one_object`; `update_all_objects` reverted to clean extraction |
| 9  | Infix forwarding | ✅ **DONE** | Phased calls + infix fwd fixup in bridge |
| 14 | Infix-aware `check_and_darken_bounded` | ✅ **DONE** | Generated from verified source. `GC.Impl.MarkBounded.check_and_darken_bounded` calls `GC.Impl.Closure.resolve_object`, whose postcondition ties it to the ghost `GC.Spec.Object.resolve_object` the mark spec was always stated over. Caveat below. |
| 15 | Guard the infix tag test with `Closure_tag` | ⚠️ **HAND PATCH — UNVERIFIED** | See below. Same file, same caveat. Exposed only after 14. |

### Extern Configuration (GC.Spec.ZeroAddr + GC.Gen.Base)

`GC.Spec.ZeroAddr.fsti` is an interface-only module declaring two extern
constants:

```c
extern uint64_t zero_addr;       /* heap base address */
extern uint64_t heap_size_u64;   /* heap upper bound (= base + size) */
```

`GC.Gen.Base.fsti` declares `minor_base_addr` as an abstract constant
(concrete value `0UL` in the `.fst`, hidden by the interface).  KaRaMeL
extracts it as a global variable:

```c
uint64_t minor_base_addr = 0ULL;   /* set at runtime to minor heap base */
```

The bridge (`alloc_gen.c`) sets `minor_base_addr` at runtime:
```c
minor_base_addr = (uint64_t)(uintptr_t)minor_data;
```

The verified `to_minor_offset_u64` function translates absolute minor
addresses to 0-based offsets inline, using modular subtraction:
```c
uint64_t off = v - minor_base_addr;
if (off < minor_heap_size_u64 && v % 8 == 0) return off; else return v;
```
This is called in `scan_loop`, `update_one_object`, and `rewrite_heap_slots`,
eliminating the need for a separate `translate_minor_fields` pass.

### Phase 4 Optimization: Inline Address Translation

**BRIDGE PATCH B7 (`translate_minor_fields`):** ✅ **ELIMINATED** by Phase 4.
Previously, a separate O(minor_heap_size) `translate_minor_fields` pass
converted all absolute minor addresses to offsets before Cheney promotion.
Now the verified `to_minor_offset_u64` performs this translation inline in
`cheney_forward_fields` (scan_loop), `update_object_pointers`, and
`rewrite_heap_slots`.  The `translate_minor_fields` function still exists
in the extracted code but is dead (never called).

**Performance impact:** binarytrees 14: 3.71s → 3.37s (9% improvement).
Eliminates 11.4% of GC time spent in the translate pass, with additional
cache efficiency gains in the Cheney phase.

KaRaMeL extracts these as extern declarations (no `static`, no initial value).
`compat.c` provides the storage, and the bridge (`alloc_gen.c`) sets them to
the actual mmap'd heap base and upper bound before calling `krmlinit_globals()`.

This replaces the old approach where `zero_addr` was a `static uint64_t` in
`GC_Gen_Impl.c` (requiring a manual `static` removal patch) and `heap_size_u64`
was a compiled constant in `GC_Gen_Base_*.c`.

**PATCHES 3,4 (scan range): ✅ ELIMINATED.** Previously the bridge narrowed
`update_all_objects` to scan only newly-promoted objects via `update_scan_base`
and `major_alloc_hwm` globals. This was INCORRECT for a free-list allocator
(promoted objects can land anywhere in the heap, not just at the end) and caused
heap corruption at binarytrees depth ≥14. The fix: the bridge now walks the
`fwd_arr` to find all promoted objects and calls the verified `update_one_object`
on each. The `update_all_objects` function has been reverted to its clean
extraction form (full heap scan from `zero_addr`). It is no longer called during
minor collection — only the fwd_arr walk + `update_one_object` is used.

**PATCH 9 (infix objects):** OCaml infix objects (tag=249) require special
forwarding during promotion. The verified spec's `well_formed_heap_part4`
currently assumes no infix objects. Supporting them requires modeling the
infix parent relationship in the formal heap model.

### Bridge Code (alloc_gen.c — 479 lines)

| # | Bridge | Status | Notes |
|---|--------|--------|-------|
| B1  | Heap init | — Keep as-is | OCaml mmap integration, inherently unverified |
| B2,4,5 | Address translation | — Simplified | Phase 4: no longer pre-translates ref_table values; `to_minor_offset_u64` handles inline |
| B3,10 | Root scan/writeback | — Keep as-is | OCaml stack layout, inherently specific |
| B6  | Infix parent injection | ✅ **DONE** | Verified `find_infix_parents` replaces 43-line C loop |
| B6b | Infix fwd synthesis | ✅ **DONE** | Verified `synthesize_infix_forwarding` replaces 57-line C loop |
| B7  | Minor field abs→offset | ✅ **ELIMINATED** | Phase 4: verified `to_minor_offset_u64` handles inline; `translate_minor_fields` no longer called |
| B8  | Scan base setup | ✅ **ELIMINATED** | Removed with PATCHES 3,4; fwd_arr walk replaces scan-range |
| B9  | Ref_table fwd rewriting | ✅ **DONE** | Verified `rewrite_heap_slots` replaces manual loop |
| B11 | Full GC wrapper | — Keep as-is | 46 lines, orchestrates major GC |
| B12 | Allocation entry point | — Keep as-is | 56 lines, hot path |
| B15 | **Inline bytecode allocation fast path** | ⚠️ **UNVERIFIED — hot path** | `Alloc_small_aux` in `runtime/caml/memory.h` reimplements bump allocation in C rather than calling verified `minor_alloc()`. See below. |
| B13 | compat.c stub | ✅ **DONE** | Empty — no more externs needed |
| B14 | verified_do_minor_gc | — Keep as-is | 5 lines, inherently OCaml-specific |

### Verification Status

| Item | Status |
|------|--------|
| `assume (no_scan_invariant)` in Correctness.fst | ✅ **Eliminated** — proved via `promote_all_preserves_no_scan_invariant` |
| All 152 generational modules verify | ✅ Clean build (`make -j4`) |
| Zero admits/assumes in spec | ✅ Confirmed |
| Extraction compiles without KaRaMeL warnings | ✅ Zero warnings |
| All 8 OCaml benchmarks pass | ✅ binarytrees (depth 14, 16), fasta, quicksort, fannkuchredux, count_change, nbodies, spectralnorm, mandelbrot. Fixed `max_young_wosize_u64` heap corruption (commit `37431eb`). |
| Header file matches exactly | ✅ `diff GC_Gen_Impl.h` = empty |
| krmlinit matches exactly | ✅ `diff krmlinit.c` = empty |

### Remaining extraction diff: 0 lines

The `verified_gc/` directory **no longer maintains copies** of extracted files.
Its Makefile uses `VPATH = ../../snapshot` to compile directly from the
snapshot sources. After `make snapshot` in `generational/`, a `make clean && make`
in `verified_gc/` picks up any changes automatically — no manual copy step.

Both `zero_addr` and `heap_size_u64` are extracted as `extern` declarations
(from `GC.Spec.ZeroAddr.fsti`), eliminating the last manual patch (previously:
`static` removal on `zero_addr`).

The extern primitives (`read_u64_le`, `write_u64_le`) are left as KaRaMeL
declared them (`extern`) and implemented in `compat.c`, which also provides
storage for `zero_addr` and `heap_size_u64`.  These are linked into
`libvergc_gen.a`.  The extracted `read_word`, `write_word`, `minor_read`,
`minor_write` call through to these externs — no inlining patches.

`is_pointer` and `is_valid_fp` lower-bound patches are **eliminated** — the
verified Pulse code now uses `U64.add zero_addr mword` which extracts as
`zero_addr + 8ULL`, matching deployment needs directly.

Scan-range patches (PATCHES 3,4: `major_alloc_hwm`, `update_scan_base`) are
**eliminated** — the bridge now walks `fwd_arr` and calls the verified
`update_one_object` per promoted object. `update_all_objects` is reverted
to its clean extraction form.

---

## Cosmetic / naming diffs — ✅ RESOLVED

The old snapshot used prefixed names (`GC_Lib_Header_White`, `GC_Lib_Header_color_sem`)
from an older extraction. The current extraction strips all prefixes via `-no-prefix`
flags, producing clean `White`, `Gray`, `Blue`, `Black`, `color_sem` names.
This is now resolved — the snapshot uses the current extraction output directly.

---

## PATCH 1 — `zero_addr` non-static + configurable heap base

**File**: `GC_Gen_Impl.c`, line 12

**What changed**:
```c
// Extracted (verified):
static uint64_t zero_addr = 0ULL;

// Patched:
uint64_t zero_addr = 0ULL;   // non-static, set by bridge
```

**Why**: The verified code assumes `zero_addr = 0`, i.e., the heap starts at
byte 0.  The OCaml integration uses the "NULL-base trick": `major.data = NULL`
so that byte offsets become absolute virtual addresses.  The bridge sets
`zero_addr` to the actual `mmap`'d base address so that `is_pointer`,
`is_valid_fp`, sweep, etc. all compute correctly against absolute addresses.

**Downstream effects**: Every function that compares against `0ULL` or
`heap_size_u64` as a bound is affected (is_pointer, is_valid_fp,
update_all_objects start position, rescan_heap start position).

**Plan to eliminate**:
1. In `GC.Spec.Base` (or a new `GC.Gen.Base`), add a configurable `zero_addr`
   parameter instead of hardcoding 0.  All address predicates (`hp_addr`,
   `obj_addr`, `is_pointer`, `is_valid_fp`) should be parameterised by
   `zero_addr`.
2. In the Pulse impl, `zero_addr` becomes a runtime-settable global
   (a `Box` or `ref`), read at function entry.
3. Re-extract: the C global will naturally be non-static and settable.

---

## PATCH 2 — `heap_size_u64` non-static + configurable

**File**: `GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c`, line 10

**What changed**:
```c
// Extracted:
uint64_t heap_size_u64 = 1024ULL;

// Patched:
uint64_t GC_Spec_Base_heap_size_u64 = 0ULL;  // set by bridge
```

**Why**: The verified code uses a compile-time constant (`1024` words = 8 KiB
test heap).  The OCaml integration needs a runtime-configurable heap size
(typically 256 MiB).

**Plan to eliminate**:
1. Make `heap_size` in `GC.Spec.Base` a runtime parameter (a `ref U64.t` or
   a top-level mutable global via `Box`).
2. Alternatively, keep it as a compile-time constant but set to a realistic
   value and pass it via `GC.Gen.Base.minor_heap_size` / `heap_size` parameters.
3. At minimum, change the constant from 1024 to a realistic default and ensure
   it is non-static in extraction.

---

## PATCH 3 — `major_alloc_hwm` and `update_scan_base` globals

**File**: `GC_Gen_Impl.c`, lines 14–25

**What changed**: Two new globals added that do not exist in verified code:
```c
uint64_t major_alloc_hwm = 0ULL;     // high-water mark
uint64_t update_scan_base = 0ULL;    // scan start for update_all_objects
```

**Why**: Performance optimisation.  Without these, `update_all_objects` scans
the entire major heap (O(heap_size)) on every minor collection.  With them,
only newly-promoted objects are scanned (O(promoted)).  The bridge sets
`update_scan_base = fp_pre - 8` before calling `minor_collect`, and
`major_alloc_hwm` tracks how far the allocator has advanced.

**Plan to eliminate**:
1. Add `update_scan_base` and `scan_limit` as parameters to
   `update_all_objects` in `GC.Gen.Impl.UpdatePtrs.fst`.
2. The caller (`minor_collect` in `GC.Gen.Impl.fst`) passes the pre-promotion
   free-pointer as the scan base and post-promotion free-pointer as the limit.
3. `major_alloc_hwm` can be tracked as a ghost or concrete field of the
   `gc_gen_heap` record, updated by `allocate` and `minor_collect`.
4. Verify that the restricted scan range produces the same result as the full
   scan (the pre-existing objects have no minor pointers to rewrite).

---

## PATCH 4 — `update_all_objects` scan range restriction

**File**: `GC_Gen_Impl.c`, lines 248–302

**What changed**:
```c
// Extracted:
uint64_t pos = 0ULL;
bool done = false;
...
done = next_pos + 8ULL >= heap_size_u64;

// Patched:
uint64_t pos = (update_scan_base > 0) ? update_scan_base : zero_addr;
uint64_t scan_limit = major_alloc_hwm > 0 ? major_alloc_hwm : heap_size_u64;
bool done = (pos + 8ULL >= scan_limit);
...
done = next_pos + 8ULL >= scan_limit;
```

**Why**: Same as PATCH 3 — restricts scanning to newly-promoted region.

**Plan to eliminate**: Same as PATCH 3 — parameterise the function.

---

## PATCH 5 — No-scan tag skip in `update_all_objects` — ✅ DONE

**File**: `GC_Gen_Impl.c`, lines 273–300

**What changed**: Added a tag check inside the scan loop:
```c
uint64_t tag_val = hdr & 0xFFULL;
if (tag_val < 251ULL) {
    // ... scan fields ...
}
```

**Why**: Objects with `tag >= no_scan_tag (251)` contain raw data (strings,
bigarrays, custom blocks), not pointers.  Without this guard, the field
scanner interprets raw bytes as pointers and corrupts data (e.g., OCaml
bytecode stored in Code_val strings).

**Plan to eliminate**: ✅ **DONE**.  The verified `update_all_objects` in
`GC.Gen.Impl.UpdatePtrs.fst` now includes an `is_no_scan` check using
`GC.Impl.Object.getTag` compared against `no_scan_tag`.  A bridging lemma
`is_no_scan_eq` connects the runtime tag comparison to the spec predicate.
When `tag >= no_scan_tag`, the field-rewriting loop is skipped.  This matches
the hand patch and is fully verified.

---

## PATCH 6 — `is_pointer` lower-bound check — ✅ ELIMINATED

**File**: `GC_Gen_Impl.c` (`is_pointer` function)

**Original issue**: The extracted code checked `v == 0ULL` or `v < 8ULL`, which
with the NULL-base trick misclassified low addresses as pointers. The deployment
needed `v < zero_addr + 8ULL`.

**Resolution**: ✅ **ELIMINATED**.  The verified Pulse source (`GC.Impl.Fields.fst`)
now uses `U64.add zero_addr mword` instead of `mword` for the lower bound.
KaRaMeL extracts this as `zero_addr + 8ULL`, matching deployment needs directly.
The extraction introduces a `let lo = zero_addr + 8ULL` local — trivially
equivalent to the inline form in the deployment copy.

---

## PATCH 7 — `darken_if_white_bounded` non-static — ✅ DONE

**File**: `GC_Gen_Impl.c`, line 550

**What changed**:
```c
// Extracted:
static void darken_if_white_bounded(...)

// Patched:
void darken_if_white_bounded(...)
```

**Why**: The bridge (`alloc_gen.c`) calls `darken_if_white_bounded` to gray
GC roots during the mark phase.  The extracted version is `static`
(file-internal) because KaRaMeL only exports functions listed in the API
bundle.

**Plan to eliminate**: ✅ **DONE**.  `GC.Impl.MarkBounded` is now listed in the
API bundle modules in the Makefile (`-bundle 'GC.Gen.Impl+...+GC.Impl.MarkBounded=...'`).
This makes `darken_if_white_bounded` non-static in the extracted C output.

---

## PATCH 8 — `is_valid_fp` uses `zero_addr` — ✅ ELIMINATED

**File**: `GC_Gen_Impl.c` (`is_valid_fp` function)

**Original issue**: The extracted code checked `v >= 8ULL` which doesn't account
for the NULL-base trick where the heap starts at `zero_addr`.

**Resolution**: ✅ **ELIMINATED**.  The verified Pulse source (`GC.Impl.Allocator.fst`)
now uses `U64.add zero_addr mword` instead of `mword`. KaRaMeL extracts this as
`v >= zero_addr + 8ULL`, matching deployment needs directly.

---

## PATCH 9 — `rescan_heap_impl` starts at `zero_addr`

**File**: `GC_Gen_Impl.c`, line 687

**What changed**:
```c
// Extracted:
uint64_t current = 0ULL;

// Patched:
uint64_t current = zero_addr;
```

**Why**: Sweep must start scanning at the actual heap base, not byte 0.

**Plan to eliminate**: Same as PATCH 1.

---

## PATCH 10 — Tag patching after Cheney promotion — ✅ DONE

**File**: `GC_Gen_Impl.c`, lines 871–886

**What changed**: ~15 lines of new C code inserted into `minor_collect`,
after `cheney_promote_phase` and before `update_all_objects`:
```c
for (i = 1; i < fwd_array_size; i++) {
    if (fwd_arr[i] != 0) {
        uint8_t orig_tag = minor_data[i * 8 - 8];
        uint8_t *major_hdr = (uint8_t *)(uintptr_t)(major_obj - 8);
        major_hdr[0] = orig_tag;
    }
}
```

**Why**: `allocate_part1` (the Cheney promotion allocator) hardcodes `tag = 0`
in promoted headers.  This loses the original tag, which matters for:
- No-scan objects (tag ≥ 251): their fields would be wrongly scanned
- Closures (tag = 247) and infix objects (tag = 249): require special handling

**Plan to eliminate**: ✅ **DONE**.  `GC.Gen.Impl.Promote.fst` now reads the
minor heap header via `Obj.getTag minor_hdr`, rebuilds the promoted header with
`makeHeader wz_read Header.White tag`, and writes it via `set_promoted_tag`.
A bridging lemma `minor_tag_bound` connects the impl tag to the spec `minor_tag`.
The hand-patched tag-fixup loop in the snapshot is no longer needed — the
extraction now produces correct tag preservation natively.
(Landed in commits `d73649a`, `527a7c2`.)

---

## PATCH 11 — Infix closure synthetic forwarding

**File**: `GC_Gen_Impl.c`, lines 888–935

**What changed**: ~47 lines of new C code that walks the minor heap looking
for `Closure_tag (247)` blocks, finds embedded `Infix_tag (249)` headers
within them, and creates synthetic forwarding entries:
```c
fwd_arr[infix_idx] = parent_fwd + byte_dist;
```

**Why**: OCaml closures can contain embedded "infix" sub-objects (tag 249).
When the parent closure is promoted to the major heap, infix pointers must
be rewritten to point into the promoted copy at the correct byte offset.
Without synthetic forwarding entries, `update_all_objects` can't find where
infix objects were promoted to.

**Plan to eliminate**:
1. This is the most complex patch. Two approaches:
   - **A (preferred)**: Handle infix objects in `cheney_promote_phase`.  When
     promoting a closure, also create forwarding entries for any embedded infix
     headers.  This keeps the logic in one place.
   - **B**: Add a post-promotion pass in `GC.Gen.Impl.fst` that walks
     `fwd_arr` and patches infix entries.
2. The spec currently assumes "no infix objects" (`well_formed_heap_part4`),
   which is why the impl doesn't handle them.  To support real OCaml code,
   either:
   - Relax the `well_formed_heap_part4` assumption and prove correctness with
     infix objects, or
   - Prove that the synthetic forwarding produces the same result as if infix
     objects were promoted individually.

---

## PATCH 12 — HWM update before `update_all_objects`

**File**: `GC_Gen_Impl.c`, lines 937–941

**What changed**:
```c
uint64_t fp_now = *gh.fp_ref;
if (fp_now > major_alloc_hwm)
    major_alloc_hwm = fp_now;
```

**Why**: After Cheney promotion, the free pointer has advanced past promoted
objects.  `major_alloc_hwm` must be updated before `update_all_objects` so the
scan limit covers the newly promoted region.

**Plan to eliminate**: Same as PATCH 3 — make HWM a field of `gc_gen_heap`,
updated by `cheney_promote_phase`.

---

## PATCH 13 — `krmlinit.c` hand-replaced

**File**: `krmlinit.c` (entire file replaced)

**What changed**: The KaRaMeL-generated `krmlinit.c` uses helper functions
(`Prims_op_Division`, `FStar_SizeT_uint_to_t`) that require linking against
Prims/FStar stub libraries.  The patched version uses plain C:
```c
fwd_array_size = minor_heap_size / 8;
queue_size_sz  = (size_t)fwd_array_size;
minor_heap_size_sz = (size_t)minor_heap_size;
```

**Why**: Avoids dependency on `Prims.h` / FStar runtime stubs.

**Plan to eliminate**:
1. Make `fwd_array_size`, `queue_size_sz`, and `minor_heap_size_sz`
   `inline_for_extraction` definitions in `GC.Gen.Base` or
   `GC.Gen.Impl.UpdatePtrs` so KaRaMeL inlines the computation.
2. Or: define them as `let` bindings (not top-level `val`) so they become
   C local initialisers rather than globals requiring `krmlinit`.
3. Goal: `krmlinit_globals()` becomes empty (or the file is not generated).

---

# Part 2: Bridge Code (`alloc_gen.c`)

`alloc_gen.c` (528 lines) is entirely hand-written C that bridges the OCaml 4.14
runtime with the verified GC.  None of it is extracted from verified code.  Every
line is in the TCB.  This section catalogues each functional block, classifies
what it does, and gives a plan to either verify it or shrink it to a thin,
obviously-correct shim.

---

## PATCH 14 — Infix-aware `check_and_darken_bounded` — ✅ RETIRED INTO VERIFIED SOURCE

**Was**: a hand edit in `snapshot/GC_Gen_Impl.c` inside `check_and_darken_bounded`,
reproducing stock `caml_darken`'s `v -= Infix_offset_val(v)`.

**Why it mattered**: an infix pointer aims at an `Infix_tag`(249) header *inside* a
closure, not at the closure's own header. Darkening `v - 8` recolours that inner header
and leaves the enclosing closure white, so a closure reachable only through infix
pointers is swept while live. Measured, not hypothetical: 219 live infix pointers at the
failing collection, one full GC freed **53 still-referenced objects**, and the program
later jumped through a NULL code pointer.

**Now generated from**:

| layer | what changed |
|---|---|
| `GC.Impl.MarkBounded.check_and_darken_bounded` (`.fst`/`.fsti`) | calls `Closure.resolve_object` and darkens the result; the bounded *spec* darkens `hd_address (resolve_object v g)` |
| `GC.Impl.Closure.resolve_object` | gained a functional postcondition tying it to the ghost `GC.Spec.Object.resolve_object` — it previously promised only `is_heap`, which is how its disagreement with the ghost definition went unnoticed |
| `GC.Impl.Closure.parent_closure_of_infix_opt` | confirms the computed parent's header is `Closure_tag`, matching what the hand patch checked |
| `GC.Spec.Object.resolve_object` | its guard gained that same `is_closure` condition, plus `resolve_infix_not_closure` for the new rejection case |
| `GC.Impl.MarkBounded.root_resolves_to_itself` | exported: on an enumerated object resolution is the identity, which is what lets the pre-existing proofs go through unchanged |

Generated C (`snapshot/GC_Gen_Impl.c`, `resolve_object` → `parent_closure_of_infix` →
`parent_closure_of_infix_opt`) checks everything the hand patch checked — tag 249, no
underflow, parent `>= 8`, `< heap_size`, parent tag 247 — **plus** 8-byte alignment of
the computed parent, which the hand patch did not.

**Runtime evidence**: `make coldstart` passes. With `resolve_object` neutered to return
its input, the same tree fails at `camlinternalFormat.cmo` with a segmentation fault —
the original failure. So the generated resolution is doing the work.

**Caveat — what the theorem does *not* say.** `well_formed_heap_part4` keeps infix
blocks out of the `objects` enumeration, so `infix_wf` is vacuous and every proof about
resolution is discharged on the branch where resolution is the identity. What is
verified is that the implementation agrees with the ghost `resolve_object` in *every*
branch, including the infix ones, and that the mark phase darkens what that function
returns. Extending `well_formed_heap` to heaps that genuinely contain infix pointers is
separate, larger work — the same work that would let `no_scan_invariant` be deleted.

## BRIDGE 1 — Heap initialisation (`ensure_heap`, lines 74–169)

**What it does** (96 lines):
- Allocates major heap via `calloc`, reads `MIN_EXPANSION_WORDSIZE` env var
- Sets `zero_addr` and `heap_size_u64` for the NULL-base trick
- Initialises major free list (writes one big blue header)
- Allocates `fp_ref`
- Allocates minor heap via `calloc`, reads `MINOR_HEAP_WORDS` env var
- Overrides `minor_heap_size`, `minor_heap_size_u64`, `max_young_wosize_u64`
- Calls `krmlinit_globals()` to re-derive constants
- Allocates forwarding array
- Registers minor heap with `Caml_state->_young_*`
- Registers major heap in OCaml's page table (`caml_page_table_add`)

**Why unverified**: The verified code uses a compile-time heap model.
Initialisation is inherently platform-specific (mmap, env vars, page tables).

**Plan to eliminate/shrink**:
1. **Verified init function**: Add an `init_gc_gen` Pulse function that takes
   pre-allocated buffers (major data, minor data, fwd array) and sizes as
   parameters, constructs the `gen_heap_t`, writes the initial blue block,
   and returns a well-formed heap.  This verifies the free-list setup and
   constant derivation.
2. **Thin C shim**: The bridge reduces to: `calloc` the buffers, call
   `init_gc_gen(buffers, sizes)`, then register with OCaml's page table
   and domain state (irreducibly OCaml-specific, ~20 lines).
3. **Eliminates**: manual blue-header construction (bug-prone), manual
   constant overrides (`krmlinit_globals`), `fp_ref` setup.
4. **Performance note**: None — init runs once.

---

## BRIDGE 2 — Address translation helpers (lines 172–184)

**What it does** (12 lines):
```c
is_minor_absolute(v)       // is v in [minor_base, minor_base + size)?
abs_to_minor_offset(v)     // v - minor_base
minor_offset_to_abs(off)   // minor_base + off
```

**Why unverified**: The verified code uses 0-based minor offsets.  OCaml uses
absolute addresses.  The bridge translates between the two address spaces.

**Plan to eliminate**:
1. **Verified minor heap with absolute addressing**: Change `minor_state` to
   use an absolute base address (like the NULL-base trick for major).  Then
   minor offsets are already absolute and no translation is needed.
2. **Or**: Thread `minor_base` as a parameter into the verified code, add
   `inline_for_extraction` wrappers that do the translation.
3. **Performance note**: These are hot-path inlines.  Eliminating translation
   entirely (option 1) saves cycles on every allocation and root scan.

---

## BRIDGE 3 — Root scanning (`scan_minor_root`, lines 188–206)

**What it does** (18 lines):
- Callback passed to `caml_do_roots` — OCaml's root enumerator
- Filters: only block values with wosize > 0
- Translates minor absolute → offset, passes major through unchanged
- Collects into parallel arrays `root_values[]` / `root_locs[]`

**Why unverified**: The verified `minor_collect` takes a flat `uint64_t`
array of root values.  The bridge must interface with OCaml's callback-based
root scanning API and do address translation.

**Plan to eliminate/shrink**:
1. The filtering logic (`Is_block`, `Wosize_val > 0`) is safety-relevant.
   A verified `translate_root` function can encapsulate the address
   translation + bounds checking.
2. The callback shape (`caml_do_roots`) is OCaml-specific and stays in C.
3. With BRIDGE 2 eliminated (absolute minor addressing), the translation
   in this callback disappears — it just stores `(uint64_t)(uintptr_t)root`.
4. **`MAX_ROOTS` (256K) static array**: Replace with a dynamically-sized
   `Vec` allocated in the verified code.  The fixed bound is a latent bug
   (silently drops roots if exceeded).
5. **Performance note**: Root scanning is O(roots) per GC — moderate.

---

## BRIDGE 4 — Ref_table translation (step 2, lines 218–228)

**What it does** (10 lines):
- Iterates `caml_ref_table` (inter-generational pointer records)
- For each entry whose value is a minor absolute address, rewrites the
  stored value in-place from absolute to minor offset

**Why unverified**: Same address-space mismatch as BRIDGE 2.

**Plan to eliminate**: With absolute minor addressing (BRIDGE 2 plan),
this step disappears entirely — ref_table values are already in the
right address space.

**Performance note**: O(ref_table_size) per minor GC.

---

## BRIDGE 5 — Ref_table as additional roots (step 3, lines 230–244)

**What it does** (14 lines):
- Adds ref_table values as extra Cheney roots so that objects pointed to
  by inter-generational pointers get promoted

**Why unverified**: The verified `minor_collect` takes a single root array.
This logic adds ref_table entries to that array.

**Plan to eliminate**:
1. Add a second parameter to `minor_collect`: `ref_table_roots` (or merge
   them into the main roots array inside the verified code).
2. Or: have the verified entry point accept two arrays (stack roots +
   ref_table roots) and merge them internally.
3. **Performance note**: O(ref_table_size), minor.

---

## BRIDGE 6 — Infix parent root injection (step 4.1, lines 249–299)

**What it does** (50 lines):
- Walks minor heap looking for `Closure_tag (247)` objects
- For each, scans fields for embedded `Infix_tag (249)` headers
- Adds the parent closure as an additional Cheney root

**Why unverified**: The verified code has `well_formed_heap_part4` which
assumes no infix objects.  This is a workaround for that gap.

**Plan to eliminate**: Same as PATCH 11 — handle infix objects in the
verified Cheney phase.  Once the verified code promotes parent closures
when it encounters infix pointers, this entire block disappears.

**Performance note**: O(minor_heap_used), walks every minor object.
This is a **significant overhead** — adds a full minor heap scan per
collection even though infix closures are rare.

---

## BRIDGE 7 — Minor field translation abs→offset (step 4.5, lines 301–341)

**What it does** (40 lines):
- Walks every minor heap object
- For pointer-containing objects (tag < 251), rewrites each field from
  absolute minor address to minor offset
- Skips no-scan objects

**Why unverified**: The verified Cheney BFS works with 0-based minor offsets.
OCaml writes absolute addresses into object fields.  Without translation,
Cheney can't follow inter-minor pointers.

**Plan to eliminate**: With absolute minor addressing (BRIDGE 2 plan),
this **entire 40-line scan disappears**.  This is the single biggest
performance win from eliminating the bridge, as it is O(minor_heap_used)
and scans every field of every minor object.

**Performance note**: **Hot path**.  O(minor_heap_used × avg_fields).
This is likely a **major source of the remaining overhead** vs stock OCaml.

---

## BRIDGE 8 — Scan base setup (step 4.6, lines 343–353)

**What it does** (10 lines):
- Reads `fp_pre = *gc_gen_heap.fp_ref`
- Sets `update_scan_base = fp_pre - 8` (header address)

**Why unverified**: Corresponds to PATCHES 3/4 above.

**Plan to eliminate**: Same as PATCHES 3/4 — parameterise
`update_all_objects`.

---

## BRIDGE 9 — Ref_table fwd_arr rewriting (step 5.5, lines 361–378)

**What it does** (17 lines):
- After `minor_collect`, iterates ref_table entries
- For each entry still holding a minor offset, looks up `fwd_arr` and
  rewrites to the forwarded major address

**Why unverified**: Complements the scan-range optimisation (PATCHES 3/4).
Pre-existing major objects that point to minor objects via ref_table need
their pointers rewritten, but `update_all_objects` only scans newly-promoted
objects.

**Plan to eliminate**:
1. If `update_all_objects` is parameterised to accept the ref_table as input,
   it can rewrite ref_table-tracked fields as part of its verified scan.
2. Or: add a second verified function `rewrite_ref_table_entries(fwd_arr,
   ref_table)` that does this lookup loop with a spec proving it rewrites
   all forwarded pointers.
3. **Performance note**: O(ref_table_size), efficient.

---

## BRIDGE 10 — Root writeback (step 6, lines 383–394)

**What it does** (11 lines):
- After minor_collect rewrites `root_values[]`, writes the rewritten
  addresses back to OCaml's root locations (`root_locs[]`)

**Why unverified**: The verified `minor_collect` rewrites a flat array of
root values in-place (proven to produce valid major addresses).  The bridge
must scatter these back to OCaml's actual root locations (stack slots,
global roots, etc.).

**Plan to eliminate**:
1. This is inherently a bridge concern — the verified code doesn't know
   about OCaml's root storage layout.
2. It can be shrunk to a trivial memcpy-equivalent if the verified code
   returns a new root array.  The loop is simple enough to audit.
3. **Performance note**: O(roots), minor.

---

## BRIDGE 11 — Full GC (`do_full_gc`, lines 402–448)

**What it does** (46 lines):
- Calls `do_minor_gc()` first
- Allocates gray stack via `calloc`
- Scans roots again via `caml_do_roots`
- Calls `darken_if_white_bounded` on each major root
- Calls verified `collect(heap, stack, fp)` — mark-and-sweep
- Frees gray stack

**Why unverified**: The root darkening loop and gray stack allocation are
bridge concerns.  The core `collect()` call is verified.

**Plan to eliminate/shrink**:
1. Add a verified `full_collect` entry point that takes the heap, a root
   array, and performs: allocate gray stack, darken roots, mark, sweep.
   This moves root darkening into verified code.
2. The bridge reduces to: call `caml_do_roots`, collect root values into
   an array, call `full_collect(heap, roots)`.
3. Gray stack allocation can be verified (Pulse `Vec` or similar).
4. **Performance note**: O(heap) for mark-and-sweep — the `collect()` call
   dominates; bridge overhead is negligible here.

---

## BRIDGE 12 — Allocation entry point (`verified_allocate`, lines 452–508)

**What it does** (56 lines):
- Checks if minor heap needs GC before allocating
- Calls verified `gen_alloc(heap, wosize, tag)`
- On failure: minor GC → retry → full GC → retry → fatal error
- Translates return value: minor offset → absolute HP, major → absolute HP
- Patches tag byte into major allocations (gen_alloc hardcodes tag=0)
- Tracks `major_alloc_hwm`

**Why unverified**: Allocation policy (when to trigger GC) and address
translation are bridge concerns.  Tag patching is a workaround for PATCH 10.

**Plan to eliminate/shrink**:
1. **Tag patching** disappears with PATCH 10 (fix `allocate_part1`).
2. **HWM tracking** disappears with PATCHES 3/4 (verified HWM).
3. **Address translation** disappears with absolute minor addressing
   (BRIDGE 2 plan).
4. **GC triggering policy**: Add a verified `gen_alloc_or_collect` that
   checks minor capacity, triggers minor GC if needed, then allocates.
   The retry-on-failure logic can also be verified.
5. **Remaining bridge**: Return the raw address to OCaml (~5 lines).

**Performance note**: **Hot path** — called on every OCaml allocation.
The pre-allocation minor-heap-capacity check (lines 460–466) adds a
branch + memory read on every alloc.  Integrating this into verified
`gen_alloc` eliminates one function-call boundary.

---

## BRIDGE 13 — `compat.c` (11 lines)

**What it does**: Provides `FStar_UInt64_ne` — a missing krmllib primitive.

**Plan to eliminate**: Add `FStar.UInt64.ne` to the extraction bundle or
use `<>` which KaRaMeL translates to `!=` directly.  Trivial fix.

---

## BRIDGE 14 — `verified_do_minor_gc` (lines 523–528)

**What it does** (5 lines):
- Called by OCaml's `caml_minor_collection()` when C primitives force a
  minor collection (e.g., `caml_make_vect` for large arrays)
- Guards: only runs if minor bump > 0

**Why unverified**: Thin wrapper, obviously correct.

**Plan**: Keep as-is — it's 5 lines and inherently OCaml-specific.

---

# Part 3: Performance Impact of Bridge Code

The bridge adds **three O(minor_heap_used) scans** per minor collection
that stock OCaml does not have:

| Scan | Lines | Cost | Status |
|------|-------|------|--------|
| BRIDGE 6: infix parent scan | — | O(minor_used) | ✅ **Verified** (`find_infix_parents`) |
| BRIDGE 6b: infix fwd synth | — | O(minor_used) | ✅ **Verified** (`synthesize_infix_forwarding`) |
| BRIDGE 7: field abs→offset | — | O(minor_used × fields) | ✅ **Verified** (`translate_minor_fields`) |
| BRIDGE 4: ref_table translation | 218–228 | O(ref_table) | Eliminable (abs minor addr) |

**BRIDGE 7 is almost certainly the dominant overhead source.**  It touches
every field of every minor object, with pointer arithmetic and conditional
branches per field.  Stock OCaml's Cheney works directly on absolute
addresses with no translation.

Eliminating the address-space mismatch (making minor use absolute addresses
like major does with the NULL-base trick) would remove BRIDGES 2, 4, and 7
entirely, and simplify BRIDGES 3, 5, and 12.  This is the single highest-
leverage change for closing the performance gap with stock OCaml.

---

## Summary: Priority Order

### Extraction Patches (Part 1)

| # | Patch | Severity | Status |
|---|-------|----------|--------|
| 10 | Tag preservation in promote | **Critical** — data corruption | ✅ DONE |
| 5  | No-scan skip in update_all | **Critical** — data corruption | ✅ DONE |
| 7  | darken non-static | **Low** — bundle config fix | ✅ DONE |
| 6  | rescan_heap_impl start | **Medium** — consistency | ✅ DONE |
| 8  | update_all_objects start | **Medium** — consistency | ✅ DONE |
| 11 | `is_pointer` lower bound | **Medium** — consistency | ✅ **ELIMINATED** — verified with `U64.add zero_addr mword` |
| 12 | `is_valid_fp` lower bound | **Medium** — already correct | ✅ **ELIMINATED** — verified with `U64.add zero_addr mword` |
| B13 | compat.c / U64.ne extern | **Trivial** | ✅ DONE |
| B14b | fwd_array_size alias | **Trivial** | ✅ DONE |
| 13 | krmlinit | **Low** — link convenience | ✅ Minimal (only 2 derived constants) |
| 9  | Infix forwarding | **Critical** — crashes on closures | ✅ **DONE** (phased calls + bridge fixup) |
| 1  | zero_addr non-static | **High** — blocks clean extraction | ⚠️ Irreducible (1-word bridge patch) |
| 2  | Configurable heap_size | **High** — blocks clean extraction | ⚠️ Irreducible (link-time settable) |
| 3,4 | Scan range / HWM | **Medium** — performance only | ⚠️ Irreducible (needs scan-range proof) |

### Bridge Code (Part 2)

| # | Bridge | Severity | Effort | Status |
|---|--------|----------|--------|--------|
| B13 | compat.c stub | **Trivial** | Trivial | ✅ DONE — empty |
| B7  | Minor field abs→offset | **Critical** — perf bottleneck | Medium | ✅ **DONE** |
| B6  | Infix parent injection | **Critical** — correctness | High | ✅ **DONE** |
| B6b | Infix fwd synthesis | **Critical** — correctness | High | ✅ **DONE** |
| B12 | Allocation entry point | **High** — hot path | Medium | — Keep as-is |
| B1  | Heap init | **High** — complex TCB | Medium | — Keep as-is |
| B2,4,5 | Address translation | **High** — systemic | Medium | — Keep as-is |
| B9  | Ref_table fwd rewriting | **Medium** — correctness | Low | ✅ **DONE** |
| B11 | Full GC wrapper | **Medium** — unverified roots | Medium | — Keep as-is |
| B8  | Scan base setup | **Low** — tied to PATCH 3/4 | Low | — Tied to PATCHES 3,4 |
| B3,10 | Root scan/writeback | **Low** — inherently OCaml | Low | — Keep as-is |
| B14 | verified_do_minor_gc | **Trivial** | None | — Keep as-is |

### Scorecard

| Category | Done | Irreducible/Deferred | Total |
|----------|------|---------------------|-------|
| Extraction patches | 11 (+2 eliminated) | 1 | 14 |
| Bridge code items | 7 | 6 | 13 |
| Extraction diff lines | — | ~12 | — |
| alloc_gen.c lines | — | 479 | — |

### Future work (remaining items, in priority order)

1. **Scan range** (PATCHES 3,4, B8) — parameterise `update_all_objects` with
   `[start, limit)` range, prove objects outside range have no minor pointers
2. **Absolute minor addressing** (B2,4) — eliminate O(minor×fields) bridge
   scans by making minor heap use absolute addresses (NULL-base trick)
3. **Infix model** — model OCaml infix objects in `well_formed_heap_part4` and
   add semantic correctness proofs for `find_infix_parents` and
   `synthesize_infix_forwarding` (currently verified for memory safety only)
4. **zero_addr non-static** (PATCH 1) — create thin `GC.Impl.Config` module
   or accept as 1-word bridge patch
5. **Verified alloc/init** (B1, B12) — move heap init and retry loop into
   verified Pulse code

---

## How the snapshot hand patches survive regeneration

`make -C generational snapshot` overwrites `snapshot/` with a plain `cp` from
`_extract/`, so hand edits to the extracted C were silently lost on every
regeneration. They are now kept as patch files and re-applied automatically:

```
generational/patches/snapshot/*.patch      the hand patches
make -C generational snapshot              extract -> cp -> apply-snapshot-patches
make -C generational apply-snapshot-patches  idempotent; hard error if a patch no
                                             longer applies (that means the
                                             extraction changed underneath it)
make -C generational verify-snapshot-patches assert the tree carries them (CI)
```

This keeps the committed snapshot equal to "extraction + documented hand
patches", so the `git diff --quiet -- generational/snapshot/` check in
`.github/workflows/verify.yml` stays meaningful instead of flagging the patches
as drift. `.github/workflows/testsuite.yml` runs `verify-snapshot-patches` as a
cheap early step. Neither target pulls in F* (the `-include .depend` is guarded),
so they work in a CI job with only a C toolchain.

The mechanism is deliberately noisy on conflict: if re-extraction changes the
surrounding code, the build stops rather than producing a snapshot that quietly
lacks a soundness fix.

---

## Patch 14 — infix-aware darkening in the major mark phase (OPEN)

**Status: hand patch applied to `snapshot/GC_Gen_Impl.c`. Unverified, and
lost on the next `make snapshot`.** This is the highest-priority item in this
document: it is a *soundness* patch, not a plumbing one.

### The bug

`check_and_darken_bounded` darkens the block whose header is at `v - 8`:

```c
uint64_t target_hdr_raw = v - 8ULL;
darken_if_white_bounded(heap, st, target_hdr_raw);
```

For an **infix pointer** — a pointer to a mutually-recursive function, aimed
at an `Infix_tag` (249) header *inside* an enclosing closure — `v - 8` is that
inner infix header, not the closure's own header. Two consequences:

1. The enclosing closure is never darkened, so if it is reachable only via
   infix pointers it stays white and the sweep frees it while live.
2. The recolouring is applied to the infix header instead.

Stock OCaml's `caml_darken` (`runtime/major_gc.c`) handles this explicitly:

```c
if (t == Infix_tag) { v -= Infix_offset_val(v); h = Hd_val(v); t = Tag_hd(h); }
```

Patch 9 fixed the analogous problem for the **minor** collector's forwarding
path. The **major** mark phase never got the same treatment.

### Impact

This is what broke `make coldstart`; see `ocaml-integration/NATIVE_INTEGRATION.md`.
`camlinternalFormat.ml` is dense with mutually recursive functions, so the
compiler's heap carries hundreds of live infix pointers (219 measured at the
failing collection). One full GC freed 53 still-referenced objects; the
program later loaded a closure whose code pointer had been overwritten and
jumped to NULL.

**`mark-and-sweep/` shares this code and therefore has the same bug** — the
extraction bundles `GC.Impl.MarkBounded` for both collectors.

### The applied patch

```c
uint64_t ih = read_word(heap, target_hdr_raw);
if ((ih & 0xFFULL) == 249ULL)
  target_hdr = (v - ((ih >> 10U) * 8ULL)) - 8ULL;   /* wosize field = offset in words */
```

### Plan to eliminate

Fix the verified source, in `mark-and-sweep/impl/GC.Impl.MarkBounded.fst`:

- extend `check_and_darken_bounded_spec` to normalise an infix pointer to its
  enclosing closure before darkening;
- the existing lemma `check_and_darken_bounded_preserves_inv` (and the
  `SpecMark.check_and_darken_field_preserves_wf` / `SpecObject.makeGray_eq`
  steps it relies on) will need the infix case;
- the larger part of the work: **`well_formed_heap` explicitly excludes infix
  blocks.**

  *This gap was already known and recorded in this document* — see PATCH 9
  ("the verified spec's `well_formed_heap_part4` currently assumes no infix
  objects"), PATCH 11's elimination plan ("relax the `well_formed_heap_part4`
  assumption and prove correctness with infix objects"), and BRIDGE 6, which
  is an unverified bridge workaround for exactly this gap on the *minor* side.
  What patch 14 adds is that the **major** collector needs the same treatment,
  which none of those entries covers: they are all about Cheney promotion.

  For reference, the conjunct in question, `common/spec/GC.Spec.Fields.fst:694-719`:

  ```fstar
  let well_formed_heap_part2 (g: heap) : prop =
    (forall (src dst: obj_addr).
      (Seq.mem src (objects zero_addr g) /\ ...
       exists_field_pointing_to_unchecked g src wz dst)) ==>
      Seq.mem dst (objects zero_addr g))        // every target is an object START

  let well_formed_heap_part3 (g: heap) : prop =
    GC.Spec.Object.infix_wf g (objects zero_addr g)

  let well_formed_heap_part4 (g: heap) : prop =
    (forall (obj: obj_addr). Seq.mem obj (objects zero_addr g) ==>
       ~(GC.Spec.Object.is_infix obj g))        // NO OBJECT IS INFIX

  let well_formed_heap (g: heap) : prop =
    part1 /\ part2 /\ part3 /\ part4
  ```

  with `is_infix h g = (tag_of_object h g = infix_tag)`
  (`GC.Spec.Object.fst:447`).

  **Part 4 says the heap contains no tag-249 object.** Every OCaml program with
  mutually recursive functions violates it. Part 2 excludes the same thing from
  the other direction: every pointer field must target a member of `objects`,
  i.e. a block *start*, so an interior pointer is ruled out twice over.

  Consequences worth being precise about:

  - The proofs are **sound**, and `GC.Spec.Mark.fsti:636
    pointer_field_resolve_identity` (resolving a pointer field is the identity)
    is a *theorem* under parts 2+4, not a mistake. It is the lemma
    `GC.Impl.MarkBounded.fst:975` uses to justify darkening `v - 8` directly —
    correct under the hypotheses, false in a real OCaml heap.
  - The infix vocabulary is present and **correct**: `is_infix`,
    `parent_closure_addr_nat`, and `infix_wf` (`GC.Spec.Object.fst:963`) with
    proper elim/intro lemmas. Part 3 states exactly the right invariant — an
    infix object's parent is in `objects` and satisfies `is_closure`. Part 4
    then makes part 3 vacuous, which is what the proofs report:
    `GC.Spec.Allocator.Lemmas.Split.fst:116` "infix_wf (vacuous: no infix
    objects exist)", `:1422`, `GC.Spec.Coalesce.fst:2830`.
  - So this is a **known, deliberate simplifying assumption** with the
    machinery already staged for lifting it. The minor side has a bridge-level
    workaround (BRIDGE 6 injects parent closures as extra Cheney roots); the
    major side has none, which is what patch 14 supplies — and it supplies it
    in the extracted C rather than the bridge, which is worse, because the
    bridge is at least an acknowledged unverified layer.

  **The defect is therefore in the join, not the proof.** `well_formed_heap` is
  a precondition and nothing checks it where the bridge calls into the
  extracted code, so a hypothesis that is false at runtime degraded into silent
  heap corruption instead of a failed proof or an assertion. That is the same
  shape as the bridge bugs in `ocaml-integration/NATIVE_INTEGRATION.md`, one
  level up: an assumption satisfied on paper and by nothing in particular at
  run time.

  Lifting part 4 is not local. Everything currently discharging the infix cases
  as vacuous must be re-proved for real (`Allocator.Lemmas.Split`, `Coalesce`,
  `Sweep`), and part 2 has to be weakened at the same time to admit
  interior-pointing fields — which touches every lemma concluding "target is in
  `objects`".

  Note the **minor** collector does model infix properly
  (`GC.Gen.CheneyPreservation.Forwarding.fst` and friends,
  `forward_if_minor_infix`). The asymmetry is the bug.

Until that lands, re-apply this patch by hand after any `make snapshot`.

---

## Patch 15 — the infix tag test is unsound (OPEN)

**Status: hand patch in `snapshot/GC_Gen_Impl.c`. Unverified; reverted by
`make snapshot`.** Three sites in the Cheney minor collector (`tag == 249ULL`
at what were lines 750, 921, 1122).

### The bug

```c
uint64_t hdr = minor_read(minor, addr - 8ULL);
uint64_t tag = hdr & 0xFFULL;
if (tag == 249ULL) { parent = addr - (hdr >> 10U) * 8ULL; ... }
```

This decides "the word at `addr - 8` is an `Infix_tag` header" from its low
byte alone, on a word that is **not known to be a header**. `Infix_tag` is 249
= `0xf9`, which is odd — deliberately, so a scanner treating it as a value sees
an integer (`mlvalues.h`: *"Infix_tag must be odd so that the infix header is
scanned as an integer"*). The converse is the problem: an OCaml **integer**
whose low byte is `0xf9` is indistinguishable from an infix header by this test.

Measured at the failure — minor heap dump around the false positive:

```
off 6120 : 0x8f8  -> wosize=2, tag=248 (Object_tag)   <- real block header
off 6128 : pointer                                     <- field 0 (class)
off 6136 : 0xdf9  -> read as "wosize=3, tag=249"       <- taken for infix header
off 6144 : 0x400                                       <- "child"
```

`0xdf9` == 3577 == `Val_long(1788)` — the object id in field 1 of an
`Object_tag` block. The collector then computed `parent = child - 3*8`, landed
mid-object, read a pointer word as a header, and requested a `wosize` of
136,625,216,709 (≈1 TB). `allocate_part1` failed, and the caller reported that
as `promotion failed — major heap full`, which is why it looked like a
heap-sizing problem and was immune to raising `MIN_EXPANSION_WORDSIZE`.

### The applied patch

Uses OCaml's own invariant (`mlvalues.h:224`: *"infix headers can only occur in
blocks with tag Closure_tag"*):

```c
if (tag == 249ULL &&
    (minor_read(minor, (addr - (hdr >> 10U) * 8ULL) - 8ULL) & 0xFFULL) == 247ULL)
```

### Two things this does NOT fix

1. ~~**Why was `child` scanned as an object address at all?**~~ **Answered by
   patch 16 below.** Something upstream produced a pointer that does not point
   at an object: the minor BFS scanned the raw payload of `Custom_tag` blocks as
   if it were a value field, so a boxed `Int64` whose payload happened to look
   like a nursery offset was enqueued as an "object". Patch 15 makes the
   consequence harmless; patch 16 removes the cause.
2. **`new_parent_addr == 0` conflates three conditions** — real allocator
   exhaustion, a zero wosize, and a nonsense size request — and reports all of
   them as "major heap full". That misdiagnosis cost three full builds. Worth
   separating regardless.

### Note: this is a *different* problem from `well_formed_heap_part4`

PATCH 9 / PATCH 11 / BRIDGE 6 all concern the spec **assuming infix objects do
not exist**. Patch 15 is orthogonal: even with full infix support, deciding
"this word is an infix header" from `tag == 249` alone is unsound, because an
OCaml integer can have low byte `0xf9`. Lifting `well_formed_heap_part4` would
not fix it; the test needs the `Closure_tag` side condition regardless.

### Plan to eliminate

Same shape as patch 14: the fix belongs in the verified source. The minor
collector's infix handling lives in `generational/impl/GC.Gen.Impl.Cheney.fst`
and `GC.Gen.Impl.MinorHeap.fst`, with the spec in
`generational/spec/GC.Gen.Cheney*.fst*` — that side *does* model infix (unlike
the major collector, see patch 14), so the work here is establishing that a
candidate infix header is only trusted when the implied parent is a
`Closure_tag` block, rather than making the test soundness-critical on a raw
tag comparison.

---

## Patch 15b — the infix parent read was unbounded (OPEN)

**Status: hand patch in `snapshot/GC_Gen_Impl.c`. Unverified; reverted by
`make snapshot`.** Same three sites as patch 15.

Patch 15 added a `Closure_tag` side condition, but the read that *tests* it was
itself unbounded:

```c
if (tag == 249ULL &&
    (minor_read(minor, (addr - (hdr >> 10U) * 8ULL) - 8ULL) & 0xFFULL) == 247ULL)
```

If the word at `addr - 8` is not a header, `hdr >> 10` is not an offset — it is
whatever the upper 54 bits of an unrelated value happen to be. Measured at the
crash: `hdr == 0x7a6500f9`, so `hdr >> 10 == 2005312` words == 15.3 MiB, against
a 2 MiB nursery. `minor_read` then read 15.3 MiB below the mapping and the
process died with `SIGSEGV` at `scan_loop+572`.

Note the ordering hazard: the guard patch 15 introduced could not run, because
computing its own operand crashed first. A soundness test that dereferences
unvalidated arithmetic is not a guard.

The patch bounds the offset before dereferencing. All three sites already
establish `addr >= 8`, `addr < minor_heap_size_u64` and `addr % 8 == 0`, so:

```c
if (tag == 249ULL &&
    (hdr >> 10U) >= 1ULL && (hdr >> 10U) <= (addr - 8ULL) / 8ULL &&
    (minor_read(minor, (addr - (hdr >> 10U) * 8ULL) - 8ULL) & 0xFFULL) == 247ULL)
```

which keeps `parent - 8` inside `[0, addr)`. A genuine infix header always
satisfies this — its parent closure lies at a lower offset in the same block —
so the bound never rejects a legitimate case. It is defence in depth: with
patch 16 applied, the garbage words that reached here should no longer exist.

---

## Patch 16 — the minor BFS scans no-scan blocks — ✅ RETIRED

**Status: no longer a hand patch.** The guard is now generated from verified source
and the hunk has been removed from `patches/snapshot/0001-infix-handling.patch`
(commit `8fbdbdd`). What follows is kept as the record of the bug, because it is the
only one of these four whose root cause was a defect in the *specification* rather
than something the specification could not express.

**This was the root cause of the intermittent compiler segfault** that made
`make world.opt` fail roughly once per 2000 `ocamlopt` invocations, on both flavours
and both CI and local machines.

### How it was retired

Guarding `cheney_scan` alone is not provable: the loop's invariant
`scanned_prefix_closed` is stated over `minor_successors`, which walked every field
regardless of tag, so a no-scan payload word that numerically named a live object
counted as a genuine successor and skipping the entry left a *false* obligation. The
guard therefore had to go into the model of reachability:

| definition | file |
|---|---|
| `minor_successors` | `spec/GC.Gen.Reachability.fst` |
| `minor_object_edges` | `spec/GC.Gen.CombinedGraph.fst` |
| `cheney_scan` | `spec/GC.Gen.Cheney.fst` |

plus `minor_is_no_scan` (`spec/GC.Gen.MinorHeap.fsti`), a new
`scanned_prefix_step_no_scan` in `CheneyBFS`, 27 preservation-proof repairs, and one
arm in the Pulse `scan_loop`. 23 files, +444/−126. The major side has had the
equivalent guard on `major_object_edges` since that module was written, so each
minor-side repair had a working template.

### One difference from the hand patch, deliberately accepted

The hand patch skipped a queue entry when `tag >= 251` **or** `tag == 249`. The
generated guard skips only `tag >= 251`. The infix conjunct is dead code: queue
entries come from `minor_objects`, and `minor_objects_not_infix` says those never
carry `Infix_tag`. It was defence-in-depth against fabricated entries — which is
exactly the class of bug this patch's retirement removes the cause of. Recorded
rather than silently dropped.

### Detail kept for the record

### The bug

`cheney_scan_step` (`spec/GC.Gen.Cheney.fsti`) scans every field of every
queued object, with no reference to its tag:

```
let obj = Seq.index cs.cs_queue scan in
let wz = minor_wosize minor obj in
let cs' = cheney_forward_fields minor cs obj 0 wz in
```

But the payload of a `Custom_tag`, `String_tag` or `Double_array_tag` block is
raw data, not values. This is **a bug in the specification**, not something lost
in extraction — the implementation faithfully implements what the spec says. The
major side already gets this right: `update_promoted_objects` tests
`is_scannable = tag < 251 && tag != 249` before touching fields. The minor BFS
was the only field scan in the collector that lacked the test.

### The failure chain, from the core dump

A boxed `Int64` is a `Custom_tag` block: `header | &caml_int64_ops | payload`.

1. `scan_loop` reads the payload word as if it were a value.
2. `scan_loop` accepts a word as a nursery address when it is 8-aligned and in
   `[8, minor_heap_size)`. An `Int64` payload of, say, `0xcd180` satisfies that,
   so the payload is **enqueued as an object**.
3. The scanner later reads that "object's" header from `payload - 8` — which is
   the `&caml_int64_ops` pointer, `0x44ede0`. Decoded as a header that is
   tag 224, **wosize 4411**, and it passes the existing bounds checks.
4. So `scan_loop` over-scans ~35 KB of unrelated nursery. Somewhere in there it
   read `0x7a6500f9` — an *odd* word, hence an OCaml integer (1026201724), whose
   low byte is nonetheless `0xf9` — patch 15 fired, and patch 15b's missing
   bound turned it into a wild read. `SIGSEGV`.

Evidence, from `coredumpctl` cores of two real build failures:

| observation | value |
|---|---|
| faulting instruction, bytecode `ocamlrun` | `scan_loop+572` (`+0x265c`) |
| faulting instruction, native `ocamlopt.opt` | `+0xb25c` — **same** `+0x25c` offset |
| nursery | base `0x7f0b73e47010`, size 2 MiB, `bump` `0x1fffd0` |
| faulting address | `0x7f0b72efa680` — 15.3 MiB *below* the nursery |
| nursery object chain | **clean**: 90578 objects walked to `bump` |
| roots | **clean**: 588, none bogus |
| invalid queue entries | 8 of 35806 |
| traced to `field#1` of a wosize-2 `Custom_tag` block | **7 of 8** |

So neither the allocator nor the root scanner was at fault: the nursery and the
root set were both well-formed, and the only bad addresses in the system were
manufactured by the scan itself.

### The applied patch

```c
else if (!((hdr & 0xFFULL) < 251ULL && (hdr & 0xFFULL) != 249ULL))
  scan = s + (size_t)1U;
```

placed after the existing `wosize` bounds checks in `scan_loop`, mirroring the
major side's `is_scannable`.

### Why it took so long to find

The rate is what made this hard. Instrumenting the guard while compiling
`middle_end/flambda/inline_and_simplify.ml` — one of the units that crashed —
gives:

```
[vergc] no-scan objects skipped=31370  bogus children prevented=3028
```

3028 bogus enqueues in a *single* compilation, yet the crash needs one of them
to also land on a `0xf9` low byte *and* produce an offset that leaves the
mapping. Almost all of them over-scan harmlessly, so the observable failure rate
collapses to ~1 in 2000 invocations: enough to fail a 900-invocation build often,
never enough to reproduce on a fixed input (0/30, 0/20, 0/25 attempts). Two
wrong conclusions came out of that — blaming CI's environment, then blaming
commit `e0aecc7` — both from treating single runs as measurements.

### Confirmation

A targeted reproducer (`ocaml-integration/tests/noscan_stress.ml`) allocates
boxed `Int64`s whose payloads are 8-aligned values inside `[8, 2 MiB)` and keeps
them live across minor collections:

| runtime | runs | segfaults |
|---|---|---|
| pre-fix | 40 | **40** |
| post-fix | 40 | **0** |

The pre-fix crash is at `+0x265c`, the same instruction as the real build
failures. It runs in `make test` and `make test-native` via `test-regression`.

### Caveat: this was not only a crash

An over-scan reads unrelated words and forwards any that look like minor
pointers, writing rewritten addresses back. Silent heap corruption was therefore
possible, not merely a segfault, and a build that *succeeded* under the old code
is not proof that it was uncorrupted. Anything built before this fix — including
the bootstrap fixpoint and the testsuite baselines in `ci/expected-failures.txt`
— is worth re-establishing.

### Plan to eliminate

The fix belongs in `cheney_scan_step` and `cheney_forward_fields` in
`spec/GC.Gen.Cheney.fsti`: field scanning should be conditioned on
`tag < no_scan_tag`, with the BFS preservation lemmas in
`spec/GC.Gen.CheneyPreservation.*` following. Note that
`well_formed_heap_part2` requires pointer fields to target objects, which a real
OCaml heap containing `Custom_tag` blocks does **not** satisfy under the current
"every field is a value" reading — so the spec's notion of a well-formed heap
needs the no-scan distinction regardless of this crash.

---

## BRIDGE 15 — the inline bytecode allocation fast path (OPEN)

**Status: unverified, and on the hot path.** Not previously catalogued here,
which is itself the problem — the whole point of this document is that every
difference from the extraction is recorded as unverified code, and this one is
executed more often than anything else in the system.

### What it is

The bytecode branch of `Alloc_small_aux` (`runtime/caml/memory.h`) does not call
the verified allocator. It open-codes bump allocation:

```c
if (vergc_minor_bump_ref != NULL && vergc_minor_base != NULL) {
  uint64_t vergc_bump = *vergc_minor_bump_ref;
  if (vergc_bump <= vergc_minor_size &&
      vergc_needed <= vergc_minor_size - vergc_bump) {
    vergc_alloc_hp = (value)(vergc_minor_base + vergc_bump);   /* address    */
    *vergc_minor_bump_ref = vergc_bump + vergc_needed;         /* bump       */
    vergc_fast_alloc = 1;
  }
}
...
if (VERGC_SHOULD_WRITE_SMALL_HEADER(vergc_fast_alloc, vergc_alloc_hp))
  Hd_hp (vergc_alloc_hp) = Make_header_with_profinfo(...);     /* header     */
```

Bounds check, address computation, bump, and header write — all hand-written,
sharing only the `bump_ref`/`base`/`size` variables with the verified allocator.
`verified_allocate_minor()` (which does reach the verified `minor_alloc()`) is
called only when the fast path declines, i.e. when the nursery is full.

### Why it matters

The fast path is taken for essentially **every** bytecode allocation; the
verified `minor_alloc()` runs roughly **once per nursery-full event**. So the
claim "bytecode runs on the verified allocator" is false as usually stated. The
verified code owns *collection*; allocation in the common case does not go
through it.

Combined with the native side — where `minor_alloc()` is never called at all,
because native allocates inline against `young_ptr` (see
`ocaml-integration/NATIVE_INTEGRATION.md` §2.4) — the honest summary is that the
verified minor **allocator** is exercised only on the bytecode slow path, in
both flavours the verified minor and major **collectors** do the real work, and
allocation is bridge code.

### Plan to eliminate

Simply calling `minor_alloc()` per allocation is not a serious option and should
not be presented as one. It is not "a call instead of inline code" in the
abstract: it is a call that cannot be inlined across the extraction boundary,
forcing spills of exactly the registers the interpreter keeps hot (`pc`, `sp`,
`accu`), at a site executed on a large fraction of bytecode instructions. The
fast path exists for a reason.

**Preferred: make the extraction emit an inlinable allocator**
(`inline_for_extraction` on `minor_alloc`, or a small `minor_alloc_fast`
carrying just the bounds test / address / bump / header write), so the fast path
*is* the verified code rather than a hand-written twin of it. This eliminates the
patch instead of documenting it.

Note this buys **bytecode only**. Native's allocation is emitted by `ocamlopt`'s
amd64 backend for `Ialloc` — subtract from `%r15`, compare against
`young_limit`, branch to `caml_call_gc`, write the header inline — and enters
runtime code only on the trap. It cannot call an inlinable allocator, or any
allocator. Verifying it would mean verifying OCaml's code generator, which is a
different project (cf. CakeML). Native allocation is therefore permanently
outside this proof effort, and should be described that way rather than as
"unverified" — the latter implies it is on a list of things to get to.

**Second: prove the existing inline form equivalent** to `minor_alloc()` — same
bounds condition, same resulting address, same post-state for `bump_ref`, same
header. A small, self-contained obligation, but it leaves two copies of the logic
that must be kept in step by hand, which is how this kind of drift starts.

### Related: flipping the verified allocator to end→start

Worth sequencing before either option. The verified minor heap currently grows
**upward** — `GC.Gen.MinorHeap.fsti` states it outright:

```
///   [obj1_hdr][obj1_fields...][obj2_hdr][obj2_fields...]...[free space...]
///    ^                                                       ^
///    0 (start)                                               bump_ptr
```

Native grows **downward** from `young_alloc_end`. That mismatch is the sole
reason `vergc_sync_bump_from_young_ptr()` exists, and it is what produced the
worst bug in the integration (a count published as its complement; see
`ocaml-integration/NATIVE_INTEGRATION.md` §3). If the verified frontier descended
from `size` instead, `bump_ref` would simply *be* `young_ptr - minor_base`: the
translation disappears, and that bug class becomes unrepresentable rather than
fixed-and-commented.

It would also let one inlinable allocator serve both flavours, since the
bytecode fast path and native's emitted sequence would finally have the same
shape — which makes the preferred option above a one-time job rather than a
per-flavour one.

**Scope: not confined to the minor-heap module.** A first pass counted `bump`
references — 319 in `spec/GC.Gen.MinorHeap.fst`, 0 in `Cheney.fst`,
`CheneyPreservation.fst` and `CheneyBFS.fst` — and concluded the collector was
independent of the direction. That conclusion was wrong. Cheney does
`open GC.Gen.MinorHeap`, so it uses those names *unqualified*; never spelling
`bump` proves nothing.

Comparing MinorHeap's 54 exported names against the 26 Cheney spec files, Cheney
references 26 of them, including:

| name | references in Cheney |
|---|---|
| `minor_state` | 515 |
| `minor_objects` | 197 |
| `minor_wf` | 114 |

and those *are* the layout:

```fstar
let minor_wf (ms: minor_state) : prop =
  U64.v ms.bump % 8 == 0 /\
  U64.v ms.bump <= minor_heap_size /\
  minor_chain_valid    ms.data 0 (U64.v ms.bump) == true /\
  minor_chain_no_infix ms.data 0 (U64.v ms.bump) == true
```

`minor_wf` is a chain walk **from 0 to bump**; `minor_objects` is the sequence
that walk yields. Cheney's specification is written over both, plus
`minor_objects_valid`, `minor_objects_body_bound`, `minor_objects_not_infix` and
`infix_parent_in_minor_objects`. Flipping the direction changes what those
predicates mean, so every lemma quantified over `minor_objects` or requiring
`minor_wf` needs re-checking — even though none mentions `bump`.

**But the shape of the work may still be small, and there is a cheap test.**
`minor_wf` and `minor_objects` are `val`-declared in the `.fsti`, i.e. abstract
to Cheney. If the flip preserves their *meaning* — "the live objects in the
nursery, in walk order" — and changes only their definition (walk from `bump` up
to `size` rather than 0 up to `bump`), Cheney's proofs may go through unchanged,
because they were written against the abstraction rather than the
representation. Establish that before committing to the work: change
`minor_wf`, `minor_objects`, `minor_alloc` and `minor_heap_reset`, and see what
breaks in `Cheney*`. If the abstraction holds, the blast radius really is one
module; if Cheney's proofs reach through to the ordering, it is not.

Cheney promotion being a root-driven BFS that classifies pointers by a window
test (the property that made patch 14 a one-line fix) is what makes the
abstraction plausible — but it is not the same claim as "the proofs do not
depend on the layout", and the two should not be conflated again.

Until one of these lands, the unverified status of the fast path should be
stated explicitly wherever the project describes what is verified.
