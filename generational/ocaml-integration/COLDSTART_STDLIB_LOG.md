# `make coldstart` — stdlib build segfault under the verified GC

Investigation log. Companion to `NATIVE_MINOR_GC_LOG.md`, which covers the
native side; everything here is the **bytecode** runtime (`runtime/ocamlrun`
linked against `libvergc_gen.a`), which `coldstart` uses to run `boot/ocamlc`
while compiling the stdlib.

**Status: FIXED, through `make world.opt`.** Five bugs found and fixed. Two of
the fixes (bugs 4 and 5) are **unverified hand patches to extracted verified
code** and are reverted by `make snapshot` — see `../PATCHES.md` patches 14
and 15. Four bugs total; the
last one is a **soundness patch to extracted verified code** that is currently
a hand edit and will be reverted by `make snapshot` — see Bug 4 and
`../PATCHES.md` patch 14.

---

## The failure

```
make -C stdlib OCAMLRUN='$(ROOTDIR)/runtime/ocamlrun' CAMLC='$(BOOT_OCAMLC) ...' all
../runtime/ocamlrun ../boot/ocamlc ... -c camlinternalFormat.ml
make[1]: *** [Makefile:222: camlinternalFormat.cmo] Segmentation fault (core dumped)
make: *** [Makefile:166: coldstart] Error 2
```

34 stdlib modules compile fine first; `camlinternalFormat.ml` is where it dies.

### Reproduce standalone

```sh
R=.../ocaml-4.14-verified-gen
cd $R/stdlib
$R/runtime/ocamlrun $R/boot/ocamlc -use-prims $R/runtime/primitives \
  -strict-sequence -absname -w +a-4-9-41-42-44-45-48-70 -g -warn-error +A \
  -bin-annot -nostdlib -principal -safe-string -strict-formats \
  -w +A -w -fragile-match -c camlinternalFormat.ml
# exit 139 (SIGSEGV)
```

Requires `camlinternalFormat.cmi` to exist (built from the `.mli` earlier in
the stdlib Makefile). If you delete it, the compile fails early with
"Could not find the .cmi file" and never reaches the crash — that produced a
misleading "a bigger heap fixes it" result during this investigation.

### Control

The **stock** `ocamlrun` compiles the identical file with the identical
`boot/ocamlc` and flags, exit 0. So this is our GC, not the environment,
the bootstrap compiler, or the source file.

---

## Bug 1 — `bump_ref` translation inverted (native only)

Found first, before this investigation; recorded here because the fix is in
the same file. `vergc_native_run_minor_collection()` set

```c
*bump_ref = minor_heap_size_u64 - used_bytes;   /* free space */
```

but every consumer reads `bump_ref` as **bytes used** (`do_minor_gc()`:
`if (bump == 0) return; /* nothing to collect */`). The trap fires when the
nursery is full, so the collector was told it was nearly empty. When
`used == size` exactly, `bump` became exactly 0, `do_minor_gc()` returned
immediately, `young_ptr` was reset to the top anyway, and the whole young
generation was discarded. Whether you hit exactly-full depends on the
allocation offsets, which depend on the exe-path and argv string lengths —
that was the "spectralnorm fails depending on its filename" symptom.

**Fix:** `vergc_sync_bump_from_young_ptr()` — the count carries over
unchanged (it is not a complement), clamped for the speculative-decrement
case, plus the same sync at the top of `do_full_gc()`.

Note `spike_young_ptr_invariant.c` cannot catch this: its only assertion on
the value is `bump_ref <= HEAP_SIZE` (true either way) and its stand-in
collector never reads `bump_ref`. Its header comment ("starts at 0, grows
toward minor_heap_size") contradicts line 82 of the same file.

## Bug 2 — stale `young_trigger` / `caml_memprof_young_trigger` in bytecode

Surfaced immediately under the debug runtime:

```
file signals.c; line 232 ### Assertion failed:
  Caml_state->young_alloc_start <= caml_memprof_young_trigger &&
  caml_memprof_young_trigger <= Caml_state->young_alloc_end
```

`ensure_heap()` repoints `young_alloc_start`/`young_alloc_end` at our buffer
but never re-derived the two trigger fields, so both still pointed into the
stock buffer `caml_init_gc()` allocated. `caml_update_young_limit()` takes
the max of them, and `caml_do_pending_actions_exn()` calls it on every
pending-action poll — so anything running long enough to poll trips it. Short
benchmarks never did; compiling the stdlib does.

This is the same bug the native path already fixed (`alloc_gen.c`, the
`caml_memprof_renew_minor_sample()` call); it was simply never applied to
bytecode.

**Fix:** moved into `ensure_heap()` so both flavors get it, and removed the
native duplicate — which also had the calls in the wrong order
(`caml_update_young_limit()` before `caml_memprof_renew_minor_sample()`,
deriving `young_limit` from a stale trigger; a debug native build would have
tripped the same assertion).

## Bug 3 — `caml_minor_collection()` was a no-op stub

```c
CAMLexport void caml_minor_collection (void)
{
  /* Disabled: we use our own verified GC.
     Keep the function body empty so callers don't crash. */
}
```

This was flagged as an open follow-up in `NATIVE_MINOR_GC_LOG.md` Phase 1
("`caml_minor_collection`/`caml_check_urgent_gc` need the same kind of
native/bytecode split `Alloc_small_aux` just got — noting this explicitly so
it isn't dropped"). It was dropped.

It is not merely incomplete, it is **silently wrong**, because `caml_make_vect`
depends on it actually running (`runtime/array.c`):

```c
if (Is_block(init) && Is_young(init)) {
    caml_minor_collection ();          /* promote init out of the nursery */
}
CAMLassert(!(Is_block(init) && Is_young(init)));
res = caml_alloc_shr(size, 0);
/* We now know that [init] is not in the minor heap, so there is
   no need to call [caml_initialize]. */
```

With the stub, `init` stayed young and the array was then filled with plain
stores — no `caml_initialize`, therefore **no ref_table entries**. Nothing
promoted the targets, nothing rewrote the fields, and `minor_heap_reset()`
zeroed what they pointed at. Any `Array.make`/`Array.init` larger than
`Max_young_wosize` with a boxed initial value produced an array of dangling
pointers.

Measured on the reproducer below: 20000 array fields pointing into the
nursery, with **17** ref_table slots.

The same gap applies to `caml_empty_minor_heap()`, whose redirect to our
collector was `#ifdef NATIVE_CODE`. In bytecode it ran stock's body — which
*looks* harmless but is worse: its `young_ptr != young_alloc_end` guard reads
"already empty", because bytecode parks `young_ptr` at `young_alloc_end` and
keeps the real state in `bump_ref`. So every bytecode caller asking for a
drained nursery (`Gc.full_major`, `Gc.compact`, `caml_gc_dispatch`,
`caml_set_minor_heap_size`, memprof) silently got nothing.

**Fix:** new flavor-independent `vergc_run_minor_collection()` in
`alloc_gen.c`; `caml_minor_collection()` and `caml_empty_minor_heap()` both
route through it. Stock's semispace body is now `#if 0`'d rather than
`#else`'d, so no caller can reach it.

`caml_check_urgent_gc()` is **still a stub** — deliberately left alone for
now (it would introduce new collection points; our allocation path already
collects when the nursery fills). Worth revisiting.

### Effect

| reproducer | before | after |
|---|---|---|
| `a_noclos` (major array of tuples + churn) | SIGSEGV | ok |
| `i_onegc` (one `Gc.full_major`) | SIGSEGV | ok |
| `g_smallarray` | `Invalid_argument("index out of bounds")` | ok |
| `infix`, `ctrl`, `b_simpleclos`, `h_list`, `j_weak` | SIGSEGV / OOM | ok |

All 11 reproducers now produce the same values as stock. Both existing
suites pass: `make test` exit 0, `make test-native` exit 0, zero fatals.

---

## Bug 4 — infix pointers are not normalised when darkening (the last one)

`check_and_darken_bounded` (extracted, `snapshot/GC_Gen_Impl.c`) darkens the
block whose header is at `v - 8`. For an **infix pointer** — a reference to
one of a set of mutually recursive functions, pointing at an `Infix_tag`
(249) header *inside* an enclosing closure — `v - 8` is that inner header, not
the closure's. So the closure is never darkened, and if it is reachable only
through infix pointers the sweep frees it while live. Stock's `caml_darken`
does `v -= Infix_offset_val(v)` first; we didn't.

Patch 9 in `PATCHES.md` fixed the analogous problem in the **minor**
collector's forwarding path. The **major** mark phase never got it.

`camlinternalFormat.ml` is dense with mutually recursive functions, which is
why it is the file that dies: 219 live infix pointers were measured in the
compiler's heap at the failing collection.

### How it was finally caught

Three earlier checks all reported the post-GC heap clean, and all three were
wrong in the same way — they asked "is the target's header blue?". Once a
swept block is **coalesced** into a larger free block, its old address is
interior to that block, so the word at `target - 8` is stale data (observed:
`0x0`), not a blue header. The check that works builds a bitmap of live block
*starts* from the linear walk and requires every pointer to hit one:

```
[pt] after FULL #1: obj 0x...adf0 (wz=6 tag=0) field[3] -> 0x...e1f0
     | hdr@v-8=0x0 | enclosing 0x...e1a0 wz=161 tag=0 col=2 [FREE] | off=80
[pt] after FULL #1: heap ptrs checked=523123 bad_fields=53 bad_roots=0
```

53 fields of live objects pointing into freed, coalesced blocks. The same
check must special-case infix pointers or it produces false positives — the
first run flagged 40 "dangling" roots that were all legitimate infix
pointers into live closures (`tag=247`, interior at offsets 56/32/344).

### Verification

With the patch applied: `bad_fields=0 bad_roots=0` across both full GCs of
the compile, and the resulting `camlinternalFormat.cmo` is **byte-identical**
to the one stock `ocamlrun` produces. `make coldstart` exits 0. Both suites
still pass; all 12 reproducers still pass.

### Caveats — read before relying on this

- The patch edits **extracted verified code**. It is not covered by any
  proof. Recorded as patch 14 in `../PATCHES.md` with a plan for fixing
  `GC.Impl.MarkBounded.fst` properly.
- `make snapshot` overwrites `snapshot/GC_Gen_Impl.c` by plain `cp`, so it
  **silently reverts this fix**. Re-apply by hand until the F* source is
  fixed.
- **`mark-and-sweep/` has the same bug** — the extraction bundles
  `GC.Impl.MarkBounded` for both collectors. Not tested there.

### Earlier false leads (all measured, all negative)

- Gray-stack overflow: the stack grows **downward** (`top` starts at `cap`,
  `push` decrements, `is_full` is `top == 0`), so `gray_top = gray_cap` is
  correct.
- Extraction name collision on `zero_addr1` / `heap_size_u640`:
  `krmlinit_globals()` copies them from `zero_addr` / `heap_size_u64` and
  `ensure_heap()` calls it after setting those.
- `rewrite_roots_impl` mangling non-minor roots — it passes them through.
- Stale `extern_sp`: bytecode's `Alloc_small_aux` does wrap the slow path in
  `Setup_for_gc`.
- Free list corrupt / overlapping live data: measured exact partition,
  `live 10834560 B + free 257600896 B = 268435456 B`, free list == the blue
  set, zero entries inside live data.
- Promoted objects being coloured black (which would stop the mark phase
  traversing into them): cheney writes them `White`.
- Ephemerons / weak refs / custom blocks — see below; measured absent.

## Ephemerons / weak refs: measured, NOT involved

The bridge processes `ref_table` only, never `ephe_ref_table`,
`custom_table`, or `caml_final_update_minor_roots()`. A real gap, but not
this bug. Instrumented over all 65 collections of the failing run:

```
[aux] minor #1:  ephe_ref_table=0 custom_table=5  ephe_list_len=0
[aux] FULL  #65: ephe_ref_table=0 custom_table=10 ephe_list_len=0
```

`ephe_list_len = 0` throughout: `boot/ocamlc` never allocates a weak array or
ephemeron during this compile. `custom_table` holds 5–10 entries (channels).

Where it *will* matter: a weak array is `Abstract_tag` >= `no_scan_tag`, so we
neither trace nor **clear** it. Stock's major GC clears weak pointers whose
target died; we sweep the target and leave the array pointing at a freed
block, so `Weak.get` returns `Some <dangling>`. Affects `Weak`, `Ephemeron`,
weak `Hashtbl`, and `Gc.finalise`. The `j_weak` reproducer passes only because
every target is also strongly held, so it never exercises clearing.

Not measured: `finalisable_first`/`finalisable_last` are file-static in
`finalise.c`, so `Gc.finalise` registrations were not counted.

## Bootstrap status (after the four fixes)

The whole bytecode bootstrap now runs on the verified GC. `Makefile.common`
defaults `OCAMLRUN ?= $(ROOTDIR)/boot/ocamlrun`, and `coldstart` copies
`runtime/ocamlrun` (verified GC) over `boot/ocamlrun`, so every compiler
invocation below is executing under it.

| step | what it does | result |
|---|---|---|
| `make coldstart` | `boot/ocamlc` builds the stdlib | exit 0 |
| `make core` | builds `ocamlc`, ocamllex, tools, library | exit 0, 854 steps, 0 faults |
| `make opt-core` | builds `ocamlopt` + native stdlib | exit 0, 65 `.cmx`, `stdlib.cmxa` |
| `make world.opt` | builds `ocamlc.opt`/`ocamlopt.opt` (native compilers) | exit 0, 2496 steps, 0 faults |

`ocamlc.opt` and `ocamlopt.opt` are native ELF binaries carrying 9
`vergc_`/`verified_allocate` symbols each — so the native compilers *run on*
the verified GC rather than merely emitting code for it.

### Verified from clean, not incrementally

The first passing `world.opt` coasted on artifacts from three earlier attempts
(only 300 compiler invocations). Redone properly with `make clean` first:

```
MAKE_EXIT=0   4820 log lines   0 faults
  535 ocamlc invocations       under our runtime
  268 ocamlopt invocations     under our runtime
  125 ocamlopt.opt invocations
```

`make clean` also wipes the runtime, so `libasmrun.a`, `ocamlrun` and both
verified-GC archives were rebuilt from source — confirming patches 14/15 are
in the tracked sources and not surviving only in stale objects. Both suites
pass against the freshly built runtime, and `ocamlopt.opt` still compiles and
runs a test using mutually recursive closures, a 5000-entry `Hashtbl` and a
3000-element boxed array.

### Compilation output is bit-identical to stock

The strongest correctness evidence available short of a proof. Eight of the
compiler's own modules recompiled with the same `boot/ocamlc` under our
runtime versus stock `ocamlrun`, outputs compared byte-for-byte:

| module | result |
|---|---|
| `parsing/parser.ml`, `typing/typecore.ml`, `typing/typemod.ml`, `typing/btype.ml` | identical |
| `lambda/matching.ml`, `lambda/translcore.ml`, `bytecomp/bytegen.ml`, `driver/optmain.ml` | identical |

8 byte-identical, 0 differing. (These *are* whole-file comparisons of `.cmo`
output — no stripdebug involved — so "byte-identical" is literal here.)

### `make bootstrap`: fixpoint reached

The strongest end-to-end check available. `coreboot` promotes our built
compiler over `boot/ocamlc`, rebuilds the compiler with it, promotes again
(including `runtime/ocamlrun` -> `boot/ocamlrun`), rebuilds the core system,
and then requires generation N and N+1 to agree.

```
Fixpoint reached, bootstrap succeeded.
MAKE_EXIT=0   3739 log lines   0 faults   841 ocamlc invocations   2 promote steps
```

Confirmed by an independent re-run: `make compare` exits 0, and both
underlying checks pass (`cmpbyt boot/ocamlc ocamlc` and
`cmpbyt boot/ocamllex lex/ocamllex`).

**Precisely what "fixpoint" means here.** `cmpbyt` compares bytecode
*sections* (CODE, DATA, PRIM, ...), not whole files. The files themselves
differ:

```
f2b9d3a0c96e734847865c1852fe4208  boot/ocamlc   (promoted, debug stripped)
374a3f6556de7d3b8d5ea3c2d2e41463  ocamlc        (rebuilt, debug retained)
```

That difference is expected and explained by the Makefile: `promote` copies
through `tools/stripdebug`. So the correct claim is that the *compiled code
and data* are identical across generations, not that the containers are
byte-identical. That is still the property that matters — a compiler compiled
by itself, under the verified GC, emitting identical code across three
self-hosting generations, where any GC-induced perturbation would compound
into a section diff rather than cancelling out.

`boot/ocamlc` and `boot/ocamllex` are now our builds (git-tracked, so
`git status` shows them modified; restore with `git checkout -- boot/`).
`boot/ocamlrun` is unchanged because `coldstart` had already installed our
runtime there. Original checksums, for reference:

```
436c3b2135d7c7bdb7970c39103eb7a2  boot/ocamlc     (upstream)
ce66a819c101bd18ef627bce0799cac3  boot/ocamllex   (upstream)
27889b4fb6201b590a3e850aeb898832  boot/ocamlrun   (already ours)
```

### Before the bootstrap, plain `make compare` failed — as it does upstream

```
ours:      Files boot/ocamlc and ocamlc differ: section CODE, offset 100612
unchanged: Files boot/ocamlc and ocamlc differ: section CODE, offset 332556
```

Both trees missed the fixpoint against the *upstream-shipped* `boot/ocamlc`,
which was never built from exactly this tree; the target's own message says
"try one more bootstrapping cycle". `make bootstrap` then reached it on the
first pass (above), which settles the question.

End-to-end check: the freshly built `ocamlopt` (itself a bytecode program
running on the verified GC) compiles a native test program, and the resulting
binary links `stdlib/libasmrun.a` — which contains `alloc_gen.n.o`,
`GC_Gen_Impl.n.o`, i.e. the verified GC — with 9 `vergc_`/`verified_allocate`
symbols in the executable. It runs and prints the correct answers.

So the loop closes: verified GC hosts the compiler that builds the compiler
that emits native code running on the verified GC.

Caveat: this is `opt-core`, not a full `make world.opt` or a bootstrap
fixpoint check (`make compare`). otherlibraries, ocamldoc and the native
toplevel are untested.

## Bug 5 — unsound infix tag test in the minor collector (was: "garbage wosize")

`make world.opt` fails. It builds `ocamlc.opt`/`ocamlopt.opt`, i.e. the
compilers compiled to native code, so it is a much heavier workload than
`opt-core`.

**Symptom.** Compiling `lambda/translattribute.ml` (a ~150-line file) dies
with:

```
verified gen GC: promotion failed — major heap full (256 MB)
  Set MIN_EXPANSION_WORDSIZE=67108864 (or larger) to increase heap.
```

The advice does not help: it fails identically at 256 MB, 1 GB and 2 GB.
Deterministic at all three.

**It is not an out-of-memory condition.** Instrumented at the failure:

```
[occ] PROMOTION FAILED: live=332100 objs 9 MB | free=1 blocks 246 MB
[occ]    free block #0: wosize=32275741 (246 MB) <== fp points HERE
```

9 MB live, 246 MB free in a *single* block, and `fp` points exactly at it.
The real cause, from tagging all seven `*oom_ref = true` sites:

```
[oom1193] allocate_part1 FAILED wosize=137067261005 (1045740 MB) fp=0x7fa7626a5db0
```

The promoter asks for a **1 TB** object. `137067261005 << 10` is `0x7fa76…`,
i.e. the "header" it read was a **pointer word**, not a header. So it read a
header from the wrong address and then reported the resulting absurd
allocation request as OOM.

**Where.** `GC_Gen_Impl.c` ~line 1160, inside the Cheney BFS's *infix* case:

```c
uint64_t parent = addr - wosize * 8ULL;      /* wosize from the infix header */
...
uint64_t wosize2 = minor_read(minor, parent - 8ULL) >> 10;
if (wosize2 == 0ULL) new_parent_addr = 0ULL;       /* also reported as OOM */
else { ... allocate_part1(major, fp, wosize2) ... }
if (new_parent_addr == 0ULL) *oom_ref = true;
```

Cheney works in 0-based minor *offsets*, so if `wosize` is wrong,
`addr - wosize * 8` underflows past 0, wraps to a huge `uint64`, and
`minor_read` then reads far outside the intended object.

**Root cause: a non-infix value was being taken for an infix header.** Minor
heap dump at the false positive:

```
off 6120 : 0x8f8  -> wosize=2, tag=248 (Object_tag)   <- real block header
off 6128 : pointer                                     <- field 0 (class)
off 6136 : 0xdf9  -> read as "wosize=3, tag=249"       <- taken for infix header
off 6144 : 0x400                                       <- "child"
```

`0xdf9` == 3577 == `Val_long(1788)`: the object id in field 1 of an
`Object_tag` block. `Infix_tag` (249 = `0xf9`) is odd *by design* so that a
scanner reading the header as a value sees an integer; the converse is that an
OCaml integer with low byte `0xf9` passes a bare `tag == 249` test. Fixed by
requiring the implied parent to be a `Closure_tag(247)` block — patch 15.

**Two further defects, still open:**

1. Why `child` was scanned as an object address at all: per the linear parse
   6144 is the *header* word of the next block. The guard makes the
   consequence harmless without explaining the cause.
2. `new_parent_addr == 0` conflates three different conditions — genuine
   allocator exhaustion, a zero wosize, and a nonsense size request — and
   reports all of them as "major heap full". That is why the error message
   sent us chasing heap sizes. Worth separating regardless of (1).

**Also observed:** the first `world.opt` run segfaulted at
`parsing/ast_helper.cmx` instead, and that one is *not* reproducible
standalone (0/8). A second run got much further and hit the deterministic
failure above. So there is at least one intermittent failure in this area
too, distinct from the deterministic one.

**Relationship to bug 4: MEASURED — bug 4 was masking bug 5.**

Compiling `lambda/translattribute.ml` with the artifacts already on disk,
varying only patch 14:

| patch 14 | result |
|---|---|
| reverted (pristine extraction) | 3/3 **pass** |
| applied | 3/3 **fail** (the 1 TB wosize above) |

To be explicit about what this does and does not mean: the closures patch 14
keeps alive are *live*. Freeing them was the bug, and patch 14 mirrors stock
`caml_darken` exactly, so it cannot retain anything stock would not — there is
no over-retention or leak. What changes is only the *shape of the heap at
later collections*: once closures actually survive a major GC, the Cheney
minor collector finally has to promote infix structure it never used to see,
and its own infix parent-address computation is wrong.

So both bugs are in infix handling, on opposite sides:

- **bug 4** — major *darken* did not resolve infix → live closures swept.
- **bug 5** — minor *promote* miscomputes the infix parent → garbage wosize.

Bug 4 destroyed the evidence bug 5 needed. Fixing bug 4 is a prerequisite for
even observing bug 5; the pre-patch-14 "pass" above is not evidence of
correctness, it is the earlier corruption happening to be survivable for this
particular compile.

## Reproducers

Self-contained; compile with the **stock** `ocamlc`, run under both runtimes.
Run with `MIN_EXPANSION_WORDSIZE=33554432` (our major heap is fixed-size, so
a small heap gives a legitimate "promotion failed — major heap full", which
is a clean error, not a bug).

```ocaml
(* a_noclos.ml — the minimal Bug 3 reproducer: no closures involved *)
let () =
  let keep = Array.init 20000 (fun i -> (i, i+1, string_of_int i)) in
  for _ = 1 to 300 do ignore (Array.make 20000 0) done;
  let acc = ref 0 in
  Array.iter (fun (a,b,s) -> acc := !acc + a + b + String.length s) keep;
  Printf.printf "ok %d\n" !acc
```

```ocaml
(* i_onegc.ml — one explicit full GC is enough *)
let () =
  let keep = Array.init 1000 (fun i -> (i, string_of_int i)) in
  Gc.full_major ();
  let acc = ref 0 in
  Array.iter (fun (i, s) -> acc := !acc + i + String.length s) keep;
  Printf.printf "ok one-gc %d\n" !acc
```

```ocaml
(* f_intarray.ml — control: immediates, no pointer children. Always passed. *)
let () =
  let keep = Array.init 20000 (fun i -> i) in
  for _ = 1 to 300 do ignore (Array.make 20000 0) done;
  let acc = ref 0 in Array.iter (fun i -> acc := !acc + i) keep;
  Printf.printf "ok int-array %d\n" !acc
```

The discriminating triple: `f_intarray` (immediates) always passed,
`d_churnonly` (churn, no live data) always passed, `e_nouse` (live data never
read back) always passed — only reading pointer children back crashed. That
is what localised Bug 3 to unrecorded major→minor pointers.

---

## Files touched

- `verified_gc/alloc_gen.c` — Bugs 1, 2, 3 (`vergc_sync_bump_from_young_ptr`,
  trigger re-derivation in `ensure_heap`, `vergc_run_minor_collection`).
- `ocaml-4.14-verified-gen/runtime/minor_gc.c` — `caml_minor_collection()`
  implemented; `caml_empty_minor_heap()` redirected for both flavors, stock
  body `#if 0`'d.
- `ocaml-4.14-verified-gen/runtime/caml/memory.h` — declares
  `vergc_run_minor_collection`.
- **`../snapshot/GC_Gen_Impl.c` — Bug 4** (infix-aware
  `check_and_darken_bounded`). Extracted verified code; unverified hand edit;
  reverted by `make snapshot`. Catalogued as patch 14 in `../PATCHES.md`.
- **`../PATCHES.md`** — patch 14 entry plus the plan to fix
  `GC.Impl.MarkBounded.fst`.
- **`patches/runtime_gen.patch` — regenerated.** `ocaml-4.14-verified-gen/`
  is gitignored and `setup.sh` rebuilds it with `git checkout -- .` followed
  by `git apply ../patches/runtime_gen.patch`, so edits made directly in that
  tree are discarded on the next setup. The two runtime edits above are now
  folded into the patch (verified: it applies cleanly to a fresh checkout via
  a throwaway `git worktree`). The previous patch is backed up alongside this
  log's scratch data but not in the repo; `git diff patches/runtime_gen.patch`
  shows exactly what was added.

Known cosmetic fallout: `clear_table` (minor_gc.c) and `expand_heap`
(memory.c) now warn as defined-but-unused, since their only callers were in
stock's disabled body.
