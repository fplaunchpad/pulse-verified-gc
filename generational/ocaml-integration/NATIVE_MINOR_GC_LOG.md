# Native minor-heap integration — implementation log

Working log for wiring OCaml native (`ocamlopt`) minor-heap allocation to
the verified GC via nursery-aliasing. Plan: see the conversation history /
`what-needs-to-be-snazzy-dusk.md` plan file for the full design rationale.
This file records what was actually done, in order, for later walkthrough.

Scope: minor heap only. Major heap integration for native is a separate,
later effort.

**Status at end of this session:** Phases 1-4 implemented and verified
working end to end against real native binaries, not just compiled --
`hello.ml` runs correctly with GC stats matching stock exactly
(`minor_words: 53, minor_collections: 0`), and a heavier allocation test
produces correct results across 4,762 real collections run through our
verified minor collector, matching stock's output exactly. Six real bugs
were found by testing and fixed this session (listed in each phase below),
the last and most significant being a domain-state struct layout mismatch
between the (unmodified) native compiler and this project's patched
runtime -- this was the actual root cause of every remaining crash/
corruption symptom, including the previously-separately-tracked stdout
channel corruption (task #7, now resolved). `patches/runtime_gen.patch` is
up to date with every change described here — regenerated via
`git -C ocaml-4.14-verified-gen diff` after each phase, so `setup.sh`
reproduces this state from scratch.

**Still open:** Make's dependency tracking doesn't know `amd64.o` needs
rebuilding when `domain_state.tbl` changes (worth a proper Makefile fix,
not just remembering to `rm` it by hand); the same offset-computation
pattern in the other architecture `.S` files was left unfixed (out of
scope, amd64-only project); root-scanning composition with `roots_nat.c`
and the write-barrier/`Is_young` native-inlining question from the
original plan's Phase 5 haven't been explicitly re-checked against this
fix, though the allocation-heavy test's correct results across thousands
of collections are strong indirect evidence they're fine.

---

## Phase 1 — Build plumbing

**Goal:** get a native OCaml runtime archive (`libasmrun.a`) that actually
links the verified GC's bridge code in, before any of the real trap/startup
logic exists. Just prove the build machinery works.

**Files changed (all inside `ocaml-4.14-verified-gen/`, the live patched
clone — see below for how this becomes a real patch):**

- `verified_gc/Makefile`: added `%.n.o: %.c` pattern rule (compiles the
  bridge + F*-extracted sources with `-DNATIVE_CODE -DTARGET_amd64`) and a
  `libvergc_gen_native.a` target, alongside the existing bytecode build.
  Compiled cleanly with no changes needed to any of the F*-extracted
  sources (`GC_Gen_Impl.c` etc.) — they don't branch on `NATIVE_CODE` at
  all, so the exact same logic just gets a second, separately-compiled
  object.
- `ocaml-4.14-verified-gen/runtime/Makefile`: added a `libvergc_gen_native.a`
  phony rule (mirrors the existing `libvergc_gen.a` one), and made
  `libasmrun.$(A)` depend on it and fold its member objects in (via
  `ar x` extraction into a temp dir, then one `ar rc` combining everything
  — `MKLIB` is a plain `ar rc`, which can't merge a nested `.a` directly).
  Also extended `clean:` to remove the temp extraction dir.

**Verification:** built `libasmrun.a` end to end (`make -C runtime -j8
libasmrun.a`) — succeeded, no errors. Compiled a trivial `hello.ml` with
the *stock* `ocamlopt` (from `ocaml-4.14-unchanged`) and manually linked it
against our `libasmrun.a` by placing a copy in an `-I`-searched directory
(`ocamlopt -I vergc_lib hello.ml` — confirmed via `-verbose` that it
resolved `libasmrun.a` to our copy, not the stdlib one). No compiler
rebuild needed, exactly per the plan.

### Bug found and fixed: `Alloc_small_aux` cross-contamination

The linked binary ran and crashed (expected at this stage — no startup
wiring or trap redirection exists yet). But the *first* crash was
interesting enough to chase: SIGSEGV inside `caml_memprof_track_young`,
reached via `caml_call_gc`, during `Stdlib` module init — nothing we'd
written yet.

Root cause: `runtime/caml/memory.h`'s `Alloc_small_aux` macro (already
patched, unconditionally, for bytecode's benefit) is not exclusive to the
bytecode interpreter — it's a general C-level macro used by *any* runtime
C file that allocates a small object directly (e.g. `memprof.c`'s internal
tracking entries). Since this header has no `#ifndef NATIVE_CODE` guard,
every native runtime `.c` file that includes it (nearly all of them) *also*
picked up the redirect to `vergc_minor_bump_ref` — meaning two completely
separate "minor heaps" were active in the same process: the real one
native's own compiled machine code uses (`young_start`/`young_end`), and
our separate buffer, used inconsistently depending on which code path
happened to allocate. `Is_young()` and friends only know about the former,
so anything allocated via the latter looked invalid to the rest of the
runtime.

Fix: added `#ifdef NATIVE_CODE` / `#else` around `Alloc_small_aux` in the
live tree (`ocaml-4.14-verified-gen/runtime/caml/memory.h`) — native gets
back the genuinely-stock body (`young_ptr`-based), bytecode keeps the
existing vergc-redirected one. Rebuilt from clean; the crash moved further
into the program (past `Stdlib` init, into user code's own `print_endline`
call) — confirms the fix addressed a real, distinct problem, not a
coincidence.

**Confirmed with a control test:** the exact same `hello.ml`, linked
against the fully unmodified stock `libasmrun.a`, runs fine (exit 0). So
this crash class is specific to our build, not a pre-existing environment
quirk.

### Second crash found, not yet fixed (expected — this is Phase 3/4's job)

After the fix above, `hello_vergc` now crashes later: inside
`caml_putblock` (`io.c`), while `print_endline` tries to write to stdout.
Inspected with gdb: `channel->curr` and `channel->end` hold garbage (one
points into the program's own code segment, the other is an unmapped
near-null address) — the channel struct's buffer bookkeeping is corrupted.

Not investigated further yet — this is squarely in the territory Phase 3
(native startup wiring) and Phase 4 (trap redirection) are meant to fix:
right now, native's minor-GC *triggering* entry points
(`caml_minor_collection`/`caml_check_urgent_gc` in `minor_gc.c`) are
*also* still unconditionally stubbed out by the existing patch (no
native guard added yet — that's explicitly scheduled for Phase 3/4, not
done here). Revisit this specific crash once that lands; if it persists
afterward, it needs its own root-cause pass.

**Open follow-up carried into Phase 3:** `caml_minor_collection`/
`caml_check_urgent_gc` need the same kind of native/bytecode split
`Alloc_small_aux` just got — noting this explicitly so it isn't dropped.

---

## Phase 2 — Standalone invariant spike

**File:** `verified_gc/spike_young_ptr_invariant.c` (new, kept in the repo
as a runnable check, not deleted after use).

Emulates, entirely outside the OCaml tree: a top-down `young_ptr`/
`young_limit` pair over a small (4 KB, to force frequent collections)
buffer, a trap when it runs out, a stand-in "collector" (models the one
guarantee that matters: `minor_collect_full` unconditionally empties the
whole nursery — doesn't attempt real reachability), and the translate-in/
collect/translate-out dance from the plan. Drives 200,000 emulated
allocations, including combined (Comballoc-style, 1-4 objects per trap)
requests, and asserts after every trap that `young_ptr == (returned
address) - 8` exactly, plus that no two objects live in the same
collection epoch ever overlap in memory.

**Bug caught immediately on first run:** the first version of
`trap_handler` computed `used_bytes = young_end - young_ptr` directly,
without first undoing the speculative decrement that triggered the trap.
Since native's real instructions do `young_ptr -= n` *before* the bounds
check (matching the real `Ialloc` emission), `young_ptr` can legitimately
be sitting below `young_start` at the moment the trap fires — the
translation math needs the real contract's first step,
`Caml_state->young_ptr += whsize` (`caml_alloc_small_dispatch`'s "undo"
line), before it means anything. Missing it made the very first
assertion (`bump_ref <= HEAP_SIZE`) fail immediately via unsigned
underflow. Added the undo step; reran; 200,000 allocations / 5,457
forced collections, invariant held every time, zero overlaps.

This is exactly the value of doing this spike before touching the real
runtime, per the plan: a wrong mental model surfaced as one failed
`assert()` in a 130-line file in under a second, instead of as a mystery
crash somewhere downstream in a real OCaml program.

---

## Phase 3 — Native startup wiring

**Discovery first:** `ensure_heap()` (`verified_gc/alloc_gen.c`) already
sets `young_start`/`young_end`/`young_ptr`/`young_alloc_start`/
`young_alloc_end` to point at the verified minor buffer — it already does
this for bytecode's `Is_young()`/write-barrier benefit. So most of what
Phase 3 needs was already there by coincidence. Two things were missing,
both load-bearing for native specifically (harmless-to-omit for bytecode,
which never reads them):

1. `young_trigger`/`young_limit` were never set.
2. Nothing called `ensure_heap()` eagerly — bytecode triggers it lazily on
   first allocation; native's compiled fast path never calls into our C
   code for the common case, so nothing would trigger it if left lazy.

**Changes:**
- `verified_gc/alloc_gen.c`: new `vergc_native_minor_startup_init()`
  (`#ifdef NATIVE_CODE`), called once at startup. Calls `ensure_heap()`,
  sets `young_trigger`/calls `caml_update_young_limit()`, registers the
  minor buffer in the page table (`caml_page_table_add(In_young, ...)` —
  stock's own `caml_set_minor_heap_size` does this for its buffer; ours
  never had an equivalent).
- `.../runtime/caml/memory.h`: declared it.
- `.../runtime/startup_nat.c`: calls it right after `caml_init_gc()`
  (which just set up a real stock buffer we're about to override).

**Testing found two more real bugs, fixed in place:**

1. **memprof sampling on every allocation.** First test crashed in
   `caml_memprof_track_young` during `Stdlib` init. `caml_alloc_small_dispatch`
   checks `young_ptr < caml_memprof_young_trigger` on every allocation to
   decide whether to run memprof's sampling callback — but
   `caml_memprof_young_trigger` was computed by stock's `caml_init_gc()`
   *before* our override, relative to the stock buffer we then abandoned.
   Comparing a stale trigger from one buffer against `young_ptr` from a
   completely different one made the sampling path fire on every
   allocation, even though this program never called `Gc.Memprof.start`.
   Fix: call `caml_memprof_renew_minor_sample()` ourselves, after
   repointing the young fields, so it recomputes relative to the buffer
   we actually use. Confirmed fixed — same crash, in the same function,
   reached via a different path (`caml_do_pending_actions_exn`'s postponed
   callback) survived one more rebuild, then also went away after
   double-checking the fix was rebuilt clean.

2. **Still open, not yet root-caused:** past both memprof fixes, `hello.ml`
   now gets all the way to its own `print_endline` call before crashing —
   inside `caml_putblock` (`io.c`), writing to the stdout channel.
   Inspected with gdb: `channel->curr`/`channel->end` hold values that
   don't look like a valid buffer range for that struct (one lands inside
   the program's own code segment). Not yet clear whether this is related
   to the minor-heap work at all — channels are allocated via
   `caml_stat_alloc` (plain malloc), not through anything this plan
   touches — or a separate, unrelated stdio-initialization-order issue in
   this minimal build. Needs a dedicated pass (e.g. compare against a
   known-good stock channel dump field-by-field, check `sizeof(struct
   channel)` matches the allocation size, check when `caml_std_out` is
   actually created relative to `vergc_native_minor_startup_init()`).
   Explicitly deferred rather than chased further right now — real
   progress was made (two confirmed, fixed bugs) and this third one is a
   good, isolated starting point for the next session rather than
   something to rush.

   **Update — this bug survived Phase 4 unchanged, which is itself useful
   confirmation.** After Phase 4 (below) fixed a completely different,
   more severe bug, this exact channel-write crash reappeared, byte-for-byte
   identical (`channel->end` reads `0xbf7` every time, deterministically,
   not varying like the ASLR'd addresses seen elsewhere in this log) —
   meaning it's a distinct, real, reproducible issue, not a downstream
   symptom of the bug Phase 4 fixed.

   **Update 2 — ruled out "corrupted during our minor collection," with an
   actual test, not just an assumption.** Prompted by a direct question
   ("why do you think this isn't related to the minor heap work") that
   exposed the earlier reasoning as weaker than it sounded (I'd checked
   that the channel *struct* is plain-malloc'd, but never checked whether
   the *custom-block wrapper* holding its pointer — which does go through
   our GC, and does trigger a minor collection at creation time, per the
   Phase 4 bug trace above — was being handled correctly during
   promotion). Two decisive checks:
   - Ran with `MINOR_HEAP_WORDS=134217728` (1GB minor heap — far larger
     than this program could ever fill, guaranteeing zero collections
     run). **Crash still happens, identically.** If our promotion logic
     were corrupting this object during a collection, forcing zero
     collections should have made the crash disappear. It didn't — real
     evidence against that hypothesis, not a restated assumption.
   - Broke specifically at fd=1 (stdout) channel creation (the earlier
     "creation looks fine" check upthread only tested fd 0, an oversight
     worth flagging) — `curr`/`end` are correctly computed (differ by
     exactly `IO_BUFFER_SIZE`) at the moment `stdlib.ml:315`'s
     `let stdout = open_descriptor_out 1` runs.

   **Narrowed conclusion (superseded below):** the channel is built
   correctly, no collection ever runs [with a 1GB heap], yet the values
   are garbage by the time `print_endline` uses it.

   **Update 3 — actual root cause found, precisely.** Prompted by a very
   reasonable challenge ("hello world can't really need >2MB of RAM,
   debug this") that exposed the 1GB test's conclusion as premature: with
   the *default* 2MB heap, traced every single write to `young_ptr` from
   a clean reset. Only 22 writes total occur before the crash, yet the
   buffer drains completely twice — meaning a handful of these writes are
   individually enormous, not "many small legitimate allocations adding
   up" (which was the working theory in Update 2).

   Found the exact one: a trap through `caml_alloc2` (one of the
   untouched, hand-written assembly stubs, requesting a routine 24-byte
   allocation) triggers `vergc_native_run_minor_collection()`, and
   afterward `young_ptr` lands at:
   ```
   expected (reset to young_alloc_end, then -24): 0x7fffe798eff8
   actual observed value:                          0x7fffe778eff8
   difference:                                      exactly minor_heap_size_u64 (0x200000)
   ```
   Confirmed by direct computation, not approximation: the buggy value
   equals `(correct value) - minor_heap_size_u64`, exactly. `young_ptr`
   ends up 24 bytes **below the floor of the buffer**
   (`young_alloc_start`) -- meaning every subsequent access through it
   lands in memory *before* our calloc'd minor buffer even begins. This
   is almost certainly the real mechanism behind the stdout corruption
   (and plausibly related to the earlier "unpromoted root" bug too) --
   not a GC/promotion-correctness issue as suspected in Update 2, but an
   exact one-buffer-size arithmetic error in the reset path, on a specific
   trigger route.

   **Correction — the above was a real mistake, not a confirmed bug.**
   The "exactly one buffer-size off" finding was built by comparing a
   value from one gdb invocation (`find_big_jump3.gdb`) against an
   expectation derived from a *different*, separate gdb invocation
   (`watch_young_ptr2.gdb`'s 22-step trace), without verifying both were
   actually observing the same point in execution. They weren't. Redone
   properly -- checked all 22 recorded values from the single complete
   trace programmatically against `[young_alloc_start, young_alloc_end)`
   -- and every *settled* value (after the undo/collect/redo sequence
   fully completes) lands correctly in range. The only below-floor values
   found (steps 4 and 11, both exactly 24 bytes under) are the expected,
   by-design transient dip from the speculative decrement happening
   *before* the bounds check -- both are immediately corrected by the verg
   `young_ptr += whsize` undo step one instruction later, exactly as
   intended, on every single trap.

   **Update 4 — actual root cause, found by pressing on "why does a tiny
   allocation with 2MB free trigger a collection at all."** Measured the
   real drift since the last reset for the `caml_alloc2` trap: only 192
   bytes used, out of 2,097,152 available. A 24-byte request should never
   trap there. That ruled out "the heap is genuinely under pressure"
   entirely and pointed straight at the trap *condition* being wrong.

   Root cause: `utils/domainstate.ml` -- the file the native code
   generator uses to compute byte offsets for domain-state fields like
   `young_limit`/`young_ptr` -- is generated by preprocessing
   `runtime/caml/domain_state.tbl` directly. The existing (pre-this-session)
   patch inserts a new field, `temp`, *before* `young_limit`:
   ```
   +DOMAIN_STATE(value, temp)
    DOMAIN_STATE(value*, young_limit)
    DOMAIN_STATE(value*, young_ptr)
   ```
   shifting every field after it down one slot (8 bytes) in the real
   struct layout. But all native code in this project's tests -- `hello.ml`
   and Stdlib itself -- is compiled with `ocamlopt` from the *unchanged*
   tree, built entirely from the *stock* `domain_state.tbl` (no `temp`),
   and never rebuilt against the patched one. So the compiler's own
   offset table still thinks `young_limit` is field 0 -- but the actual
   runtime (`libasmrun.a`, built from the patched table) has `temp` at
   field 0 and `young_limit` at field 1.

   Net effect: every native allocation site's `cmpq
   Caml_state(young_limit), %r15` reads the compiler's stale offset for
   "young_limit", which lands on whatever the *runtime* actually put
   there -- `temp`, a scratch variable bytecode's (disabled-for-native)
   `Alloc_small_aux` fallback occasionally writes to. Every allocation is
   comparing `young_ptr` against essentially arbitrary memory, not a real
   limit. `caml_call_gc`'s save/restore of `young_ptr` is similarly one
   slot off, reading/writing what the runtime considers `young_limit`'s
   memory instead of `young_ptr`'s. This is a structural
   compiler/runtime domain-state layout mismatch, not a bug in anything
   this plan has written -- it fully explains both the spurious
   collection triggers and is a strong candidate for the stdout
   corruption too, since it corrupts the one register-save/restore path
   every single native trap goes through.

   **First fix attempt (superseded below by a cleaner one -- kept here
   because the diagnostic journey and the verification numbers are still
   the ones that apply).** Went with the cheaper of the two options
   originally considered (user's suggestion): scope `temp` to bytecode
   only, so native's struct layout stays identical to stock's rather than
   rebuilding the compiler. `runtime/caml/domain_state.tbl`:

   ```
   #ifndef NATIVE_CODE
   DOMAIN_STATE(value, temp)
   #endif
   DOMAIN_STATE(value*, young_limit)
   ```

   First attempt at testing this exposed a **second**, independent
   instance of the same class of bug: `runtime/amd64.S` also computes
   its own domain-state offsets, by directly `#include`-ing
   `domain_state.tbl` itself (a third place this layout gets computed,
   independent of both the runtime C code and the compiler's
   `utils/domainstate.ml`). Its own build rule
   (`gcc -c -DSYS_linux -I../runtime -DMODEL_default -o amd64.o amd64.S`)
   never passes `-DNATIVE_CODE` -- unsurprising, since in stock OCaml
   this file has no `#ifdef NATIVE_CODE` branches of its own and never
   needed to care. My new guard silently reintroduced `temp` for this
   one file, since the macro was undefined there. Fixed by having
   `amd64.S` declare its own nativeness explicitly rather than depend on
   a build flag never meant to apply to it:
   ```
   #ifndef NATIVE_CODE
   #define NATIVE_CODE
   #endif
   ```
   (placed before its own `domain_state.tbl` include). Also caught,
   separately: `amd64.o` is a binary object file, and Make's dependency
   tracking doesn't know an assembly file's `#include` means "rebuild on
   `domain_state.tbl` changes" -- it was stale from the very first build
   this session and had to be deleted by hand to force recompilation
   after each of these two edits. Worth fixing properly in the Makefile
   at some point (explicit dependency), not just remembering to `rm` it.

   **Verification, not just "it compiles now":**
   - `hello.ml`: prints correctly, exit 0, 5/5 consecutive runs.
     `OCAMLRUNPARAM=v=0x400` reports `minor_words: 53,
     minor_collections: 0` -- matching stock's own numbers *exactly*,
     not approximately.
   - A heavier allocation test (200,000-iteration loop building and
     discarding small lists) run against both stock and our build:
     identical correct output (`total=800000`) at the default heap size,
     **and** with a deliberately tiny 512-word heap forcing 4,762 real
     collections through `vergc_native_run_minor_collection()` --
     confirmed via breakpoint count, not assumed. Correct output
     survived all 4,762 cycles.
   - This **was** the root cause of the stdout corruption (task #7),
     confirmed directly: `hello.ml` (the exact original reproduction --
     `print_endline "hello from native"`, the one that reliably crashed
     with garbage `channel->curr`/`channel->end` all session) now runs
     correctly, 5/5 times, with this fix applied and nothing else
     changed. `caml_call_gc`'s own register save/restore of `young_ptr`
     was reading/writing through this exact wrong offset on every single
     native trap, all session -- task #7 is resolved, not just
     "probably related."

   **Portability note, not urgent:** the same `.equ domain_field_caml_##name /
   #include domain_state.tbl` pattern exists in `riscv.S`, `s390x.S`,
   `power.S`, `arm.S`, `i386.S`, `arm64.S` too -- would have needed the
   same fix there too, if this project ever targeted those architectures.
   Moot now, given the superseding fix below touches neither file.

   **Superseding fix -- no `domain_state.tbl` or `amd64.S` changes at
   all.** Flagged (rightly) as an unwanted amount of surface area for
   what should be a small, contained problem: two extra files patched
   (one of them hand-written assembly), plus a workaround for a Makefile
   dependency gap, just to give bytecode's slow path one scratch word.
   Checked stock `domain_state.h` for a cleaner option and found one
   already built in:
   ```c
   DOMAIN_STATE(extra_params_area, extra_params)
   /* This member must occur last, because it is an array, not a scalar */
   ```
   `extra_params` is a **64-word array, already present in stock OCaml's
   own `domain_state.tbl`, already unused anywhere in the entire tree**
   (confirmed by grep) -- clearly intended by upstream as exactly this
   kind of forward-compatible extension point. Since it already exists in
   the *stock* table, the stock compiler's `utils/domainstate.ml` and
   every architecture's `.S` file already agree on where it lives, with
   zero involvement from this project. Using one of its slots instead of
   adding a new named field means: no edit to `domain_state.tbl` at all
   (reverted to byte-for-byte stock), no edit to `amd64.S` at all
   (reverted to byte-for-byte stock), no Makefile dependency workaround
   needed, no compiler rebuild, and nothing native-specific to guard,
   because the struct layout literally never changes.

   `runtime/caml/memory.h`'s `Alloc_small_aux` (bytecode-only branch)
   now uses `Caml_state_field(extra_params)[0]` in place of the removed
   `Caml_state_field(temp)` -- the only two lines that ever referenced
   the old field, confirmed by grep across the whole patched tree before
   removing it.

   **Re-verified after switching to this fix**, full clean rebuild of
   both flavors (`ocamlrun` and `libasmrun.a`, forcing every object file
   to recompile, not just the ones touched):
   - Native: `hello.ml` and the 200,000-iteration allocation test both
     produce identical, correct output to stock (3/3 and 1/1 runs
     respectively; the allocation test forced real collections via a
     tiny 512-word heap as before).
   - Bytecode: same two test programs, compiled with `ocamlc` and run
     under the freshly-rebuilt `ocamlrun` -- both produce correct output
     (`hello from native`, `total=800000`).
   - `git diff` on the patched tree now shows no changes at all to
     `domain_state.tbl` or `amd64.S` -- confirmed reverted to stock.

   **Net result: the young_ptr/bump_ref arithmetic itself is not the bug.**
   Ruled out cleanly, not abandoned. The nested-reentrancy hypothesis
   above was a plausible-sounding mechanism that, walked through with
   concrete numbers, didn't actually reproduce the (mistaken) measurement
   it was invented to explain -- withdrawn along with the measurement.
   Back to the "Update 2" territory: the pointer arithmetic is sound, so
   the real defect is more likely in how this specific object/root is
   tracked during promotion, not in the reset math. Next session should
   resume from there, not from the arithmetic angle.

   **Narrowed slightly before stopping:** broke at channel creation
   (`io.c`, right after `channel->end = channel->buff + IO_BUFFER_SIZE`)
   and confirmed the values are computed correctly at creation time
   (`curr`/`end` differ by exactly `IO_BUFFER_SIZE`, both sane addresses)
   — but that check happened to hit fd 0 (stdin), not fd 1 (stdout, the
   one that actually crashes). `struct channel`'s field layout
   (`caml/io.h`) was also confirmed by hand against the observed struct
   dump, ruling out a struct-layout/`sizeof` mismatch as the cause.

---

## Phase 3 addendum — reclaim the abandoned stock buffer

Flagged by a user question, not testing: `vergc_native_minor_startup_init()`
runs *after* `caml_init_gc()` has already allocated a real stock minor
buffer (2MB by default). We repoint `young_start`/`young_end`/`young_ptr`
at our own buffer, but the original stock allocation was never freed —
a genuine, if small and bounded (not growing), memory leak for the life
of every native process using this runtime.

Fix: save `young_base`/`young_start`/`young_end` at the very top of
`vergc_native_minor_startup_init()`, *before* calling `ensure_heap()`
(which immediately overwrites those fields — once overwritten, the old
pointer is unrecoverable), then after everything else, reclaim it:
`caml_page_table_remove(In_young, old_start, old_end)` +
`caml_stat_free(old_base)`. This exactly mirrors what stock's own
`caml_set_minor_heap_size` (`minor_gc.c:162-166`) already does to itself
when resizing an existing minor heap — same cleanup, just applied to the
buffer stock set up for us moments ago instead of one it's replacing on
its own initiative. Rebuilt and retested: identical behavior (same exit
point, the pre-existing channel bug), confirming this only stops the
leak and doesn't change program behavior.

---

## Phase 4 — Trap redirection

**First attempt (superseded):** redirected `caml_garbage_collection`
(`signals_nat.c`, the function `caml_call_gc` calls when the
compiled-code fast path traps) to a new `vergc_native_alloc_dispatch()`
in `alloc_gen.c`, hand-rolling the undo/check/translate/collect/
translate-back/redo sequence designed in Phases 2-3.

**Testing found this redirect was incomplete, at the right severity to
matter.** `hello.ml` progressed past `Stdlib` init (further than any
prior test) but then hit a real `caml_fatal_error` from our own code:
*"internal error — unpromoted root after gen_gc"*. Traced with gdb:

```
caml_alloc_shr_aux(wosize=137438553664, ...)   <- absurd, corrupted size
  <- caml_alloc_shr_for_minor_gc
  <- caml_oldify_one (promoting a GLOBAL ROOT, main_argv)
  <- caml_scan_global_young_roots / caml_oldify_local_roots
  <- caml_empty_minor_heap                      <- STOCK's real collector
  <- caml_gc_dispatch
  <- caml_alloc_small_dispatch
  <- caml_alloc_small                           <- plain C helper, NOT the compiled-code trap
  <- alloc_custom_gen (custom.c, building the stdout channel's custom block)
```

**Root cause:** `caml_alloc_small()` — a plain C function used internally
by `custom.c`/`weak.c`/etc. for allocations that don't originate from
compiled OCaml code — calls `caml_alloc_small_dispatch` **directly**,
which was still calling **stock's** `caml_gc_dispatch()` →
`caml_empty_minor_heap()`. Redirecting only `caml_garbage_collection`
(the compiled-code trap's target) left this second, equally-real path
running stock's actual Cheney collector against our buffer. Stock's
collector correctly reset `young_ptr` afterward (so *native's* view
looked consistent) but has no idea our own bump-pointer counter
(`gc_gen_heap.minor.bump_ref`) exists — leaving it stale and desynced
from `young_ptr`. The next allocation's translate-in math
(`bump_ref = minor_heap_size - used_bytes`) then computed nonsense
against a `young_ptr` that stock had already reset out from under it,
and the corrupted `wosize` downstream was a direct consequence.

**Fix — corrected design, smaller than the first attempt.**
`caml_alloc_small_dispatch` (`runtime/minor_gc.c`) already has its own
undo/loop/recheck/redo structure with exactly **one** call to
`caml_gc_dispatch()`. Both problem paths (the compiled-code trap *and*
`caml_alloc_small()`'s direct C-level calls) funnel through this one
shared call site. Redirecting it there, instead of duplicating
undo/redo logic one layer up, fixes both paths at once and is less code:

- `verified_gc/alloc_gen.c`: replaced `vergc_native_alloc_dispatch`
  with a narrower `vergc_native_run_minor_collection()` — just the
  translate-in / `do_minor_gc()` / translate-back core, no undo/redo
  (that stays exactly as stock already wrote it).
- `runtime/minor_gc.c`: `caml_alloc_small_dispatch`'s one
  `caml_gc_dispatch();` call site now branches on `NATIVE_CODE` —
  native calls `vergc_native_run_minor_collection()`, bytecode
  (if this function is even reachable there) is untouched.
- `runtime/signals_nat.c`: reverted to calling
  `caml_alloc_small_dispatch(...)` exactly like stock — it no longer
  needs its own special case, since the real fix lives one layer deeper
  now.

**Retested after the fix:** the fatal error (and the corrupted-header
crash it came from) is gone. The program now progresses to the exact
same point as before Phase 4 existed — the pre-existing, separately
tracked stdout-channel bug (see Phase 3 above) — confirming this fix
resolved a real, distinct problem rather than just relocating a symptom
(the channel bug reproduces byte-for-byte identically before and after,
which is exactly what you'd expect from two genuinely independent bugs).

---

## Phase 5 — named regression check against prior art (InnocentZero's failing testcase)

The plan (Phase 4/5) called out a specific known regression to check
against: InnocentZero's `ocaml_mmtk_expr` attempt at this same
integration shipped with a documented, unfixed bug (see its README,
"Failing testcase for `ocamlopt.vergc`") — structural equality on the
result of a tail-recursive function broke, and an `assert` using that
equality segfaulted. Their own note ("uncommenting a custom `(=)`
makes it work for some reason") is exactly the signature of a `young_ptr`
translation bug: something about going through the trap during a tail
call in compiled code left `young_ptr` slightly wrong, corrupting the
value read back for the `+8` computation.

Fetched the exact failing testcase from their README and ran it
verbatim, unmodified, against this session's build:

```ocaml
let rec tail lst = match lst with
  | [] -> None
  | [ t ] -> Some t
  | _ :: t -> tail t

let () =
  print_endline "I have no mouth yet I must scream!!!!";      (* works *)
  if (tail [] = None) then print_endline "NONE!";               (* works *)
  begin match tail [3; 4] with                                  (* works *)
    | Some 4 -> print_endline "FOURRRRRRR"
    | Some x -> print_int x; print_endline ""
    | None -> print_endline "WAT"
  end;
  begin if tail [ 3; 4 ] = Some 4 then                           (* THEIRS: doesn't work *)
    print_endline "SOME 4" else print_endline "WAT"
  end;
  assert (tail [] = None);                                       (* works *)
  assert (Some 1 = Some 1);                                      (* works *)
  assert (tail [ 1 ] = Some 1)                                   (* THEIRS: segfaults *)
```

**Result: passes completely**, including both lines that failed for
them — `tail [3; 4] = Some 4` correctly prints `SOME 4`, and
`assert (tail [1] = Some 1)` no longer segfaults. Verified this wasn't
a fluke:
- 5 repeated runs, identical output every time.
- Re-run under `MINOR_HEAP_WORDS=16/32/64/128` (our env var sizing the
  verified minor buffer) to force many real collections mid-recursion,
  the exact circumstance most likely to expose a `young_ptr` bug —
  still passes at every size, including 16 words (guarantees frequent
  collection during the tail-recursive descent).
- Cross-checked against a build linked to stock's own `libasmrun.a`
  (sanity baseline) — identical output, confirming this is a
  regression check on our integration, not a semantics difference in
  the test itself.

Separately, and unprompted by the plan, verified the direct-to-major
allocation dispatch path (`caml_alloc_shr` for anything with
`wosize > Max_young_wosize` = 256 words = 2KB, entirely independent of
minor heap size) empirically: compiled a test allocating a 16-byte and
a 100,000-byte `Bytes.t`, broke on `caml_create_bytes` in gdb, and
confirmed via address-range comparison against our own
`minor_base`/`minor_heap_size_u64` and `zero_addr`/`heap_size_u64`
globals that the small one lands in the minor heap and the large one
lands directly in the major heap, never touching the minor buffer.
This exercises a code path this session's work never modified
(`caml_alloc_shr` and the verified major allocator), confirming it's
unaffected by the minor-heap integration.

This closes out the named regression-check item from the original
Phase 5 plan. The remaining Phase 5 items (root-scanning composition
with `roots_nat.c` under deeply-nested native-stack-only liveness, and
whether native inlines any part of the write barrier the way it inlines
allocation) are still open — not yet explicitly re-checked against the
final `extra_params`-based fix.

---

## Phase 5 continued — root-scanning composition, and a real open bug

Checked the two remaining Phase 5 items from the plan:

- **Write barrier / `Is_young` native inlining**: `asmcomp/amd64/emit.mlp`
  is completely unpatched and has no `caml_modify`-related emission —
  confirmed by inspection (only `Ialloc`/`Ipoll` touch `young_ptr`/
  `young_limit` directly). The write barrier is always a plain call to
  `caml_modify`, which is itself unpatched stock code depending only on
  `Is_young`'s `[young_start, young_end)` check — already set correctly
  by Phase 3's startup wiring. No native-specific work needed here;
  closed by inspection, not by a new test.
- **Root-scanning composition with `roots_nat.c`**: wrote a new test,
  `deep_stack_roots.ml` — ~4000 levels of non-tail recursion, each frame
  holding a live local tuple reachable *only* through a native stack
  frame slot (no globals), verified against an independently-computed
  expected value after collection. Passes at the default 2MB minor
  heap, including 5 repeated runs.

**Found in the process (unplanned, but exactly what Phase 5 exists to
catch): a real, separate bug**, fixed and confirmed safe: `caml_gc_major`,
`caml_gc_full_major`, `caml_gc_compaction` (backing `Gc.major`,
`Gc.full_major`, `Gc.compact`), `Gc.set`'s allocation-policy-change path,
and `compact.c`'s compaction all call `caml_empty_minor_heap()` directly
— a second, independent family of call sites distinct from
`caml_alloc_small_dispatch`'s (the one Phase 4 already redirected).
Left alone, any of these — all ordinary, commonly-used public API calls
— would run stock's real semispace/in-place-forwarding minor collector
against our buffer for native, corrupting it without touching our own
bump_ref bookkeeping. Rather than patch each call site individually
(easy to miss one, as the first attempt at this fix — directly patching
`memprof.c`'s own direct `caml_gc_dispatch()` call — demonstrated: it
turned out to be a false lead for the failure below, and redundant once
the real fix landed), redirected `caml_empty_minor_heap()` itself
(`runtime/minor_gc.c`) at its single definition:
```c
void caml_empty_minor_heap (void)
{
#ifdef NATIVE_CODE
  if (Caml_state->young_ptr != Caml_state->young_alloc_end)
    vergc_native_run_minor_collection();
#else
  ... [original stock body, unchanged] ...
#endif
}
```
This covers every current caller (and any future one) by construction.
Verified no regressions: `hello.ml`, the InnocentZero regression test,
`alloc_test.ml` (200k iterations), and `deep_stack_roots.ml` at the
default heap all still pass identically after this change.

**Still open — a real, unresolved bug, found by `deep_stack_roots.ml`
under artificial stress**: forcing the verified minor buffer down to an
unusually small size (`MINOR_HEAP_WORDS=32` through at least `16384`,
i.e., even sizes far above any plausible "too small to hold one object"
concern) makes the test fail deterministically:
```
Fatal error: verified gen GC: internal error — unpromoted root after check
```
Confirmed this is native-specific, not a general limitation: bytecode
(`ocamlrun` + this same verified GC) passes at every one of the same
heap sizes, and stock unmodified `ocamlopt` also passes at equally tiny
heaps (`OCAMLRUNPARAM=s=32`). Root-caused as far as: a specific,
deterministic root (same index, same offset, every run) shows up in
`scan_minor_root`'s gathered set as a value pointing exactly one word
(8 bytes) too low — landing on what a memory dump confirms is the
*header* of a real, valid, densely-packed tuple in the minor heap,
rather than past it (the correct value position). The object this
points to is never visited by the verified BFS (`gc_fwd_arr` has no
entry for that offset at write-back time), so the promotion-completeness
check correctly rejects it rather than silently mishandling it — this
is the safety net working as intended, not the bug itself. Ruled out:
duplicate root values, duplicate root locations, the nested
`do_full_gc()`-from-`do_minor_gc()` path (this specific fatal message
only fires from the non-nested `do_minor_gc_core` path), and the
`caml_empty_minor_heap` gap just fixed above (fix applied, bug persisted
unchanged). Only reproduces with several thousand simultaneous live
native stack roots under sustained collection pressure — not yet seen
at moderate scale (the default-heap run of the same test, and every
other test this session, pass cleanly). Leading hypothesis going in:
something in how a root's address is computed or rewritten specifically
under very high simultaneous root counts, but this is not yet confirmed
to a specific line. Left open pending direction on how deep to dig
before moving on.

---

## Major heap — attempted a `do_full_gc()` fix, found it wrong, reverted

Followed up on the major-heap difficulty assessment from earlier: two
`do_full_gc()` call sites reach it directly from plain C code, never
through the compiled-code trap that `vergc_native_run_minor_collection()`
relies on —

- `verified_allocate()`'s OOM retry (`alloc_gen.c:692`) — a large
  (>256-word) allocation finds the major heap full, calls `do_full_gc()`,
  retries.
- `caml_trigger_verified_gc()` (`alloc_gen.c:718`) — an OCaml-callable
  debug primitive, registered in `prims.c`, reachable from native code
  too if anything declares an `external` binding to it.

**First attempt**: copy the exact translate-in/translate-out pattern
from `vergc_native_run_minor_collection()` into `do_full_gc()` itself
(mirroring the `caml_empty_minor_heap()` fix's "patch the one shared
definition" approach), reasoning that since `do_full_gc()`'s only use
of `bump_ref` is the minor-collection stat lines (confirmed by
inspection — root discovery is 100% `caml_do_roots`-driven, never
bounded by `bump_ref`), this would only improve `Gc.stat()` accuracy,
never affect data correctness.

**Built a real test to check it anyway** rather than trust the
reasoning (`major_gc_test.ml` — interleaves small minor-heap allocations
with large, >256-word ones inside a small `MIN_EXPANSION_WORDSIZE`
major heap, forcing `verified_allocate()`'s OOM branch to fire
repeatedly; a fixed-size ring keeps only the most recent few large
objects live so the test also exercises real promotion/reclaim, not
just allocation). Data correctness held either way (ring stays intact,
2855 `do_full_gc()` calls). But `Gc.stat()` afterward showed the "fix"
made things *worse*, not better:

| | minor_words | minor_collections | major_collections |
|---|---|---|---|
| before this attempt | 220,180 | 0 | 2855 |
| with the attempted fix | 748,201,127 | 2855 | 2855 |

**Why it's wrong**: `Caml_state->young_ptr` in memory is only
synchronized with the live `%r15` register during an actual trap —
`caml_call_gc`'s assembly does `movq %r15, Caml_state(young_ptr)` on
entry and reloads it on exit. `vergc_native_run_minor_collection()` is
*only* ever reached via that trap, so reading memory there is safe —
it's freshly written moments earlier by the same trap. `do_full_gc()`'s
two problem call sites are reached via a plain C call chain
(`caml_alloc_shr` → ... → `verified_allocate` → `do_full_gc`) that never
goes through the trap at all, so memory's `young_ptr` is stale —
frozen at whatever the *last* real trap left it at, unrelated to
`%r15`'s actual current position. Added a debug print to confirm
directly: `used_bytes` computed from this stale value came out tiny
(616 bytes) and *identical* across many consecutive calls, confirming
memory genuinely never changes between them — the formula
`bump_ref = minor_heap_size - used_bytes` then reports "almost the
entire heap in use" every single time (since a tiny `used_bytes`
against a 2MB heap leaves `bump_ref` close to the full 2,097,152), and
2855 calls each mis-reporting ~262,000 words compounds to the observed
748 million.

**Reverted both blocks entirely** — confirmed `do_full_gc()` byte-for-byte
back to its original form, rebuilt, and re-ran the full regression
suite (`hello`, the InnocentZero regression test, `alloc_test`,
`deep_stack_roots` at the default heap, `major_gc_test` at both default
and small major heap, plus a bytecode sanity check) — all pass,
numbers back to the pre-attempt baseline (`minor_words=220180`,
`major_collections=2855` at the small heap).

**Net status**: the underlying stats-accuracy gap (`Gc.stat()`'s
`minor_words`/`minor_collections` undercounting activity attributable
to major-heap-triggered collections) is confirmed real but **not
fixed** — reading `young_ptr` from memory doesn't work outside a trap
context, and there's no cheap way to force a real trap/sync from a
plain C call site without deeper changes. Left as-is (matching
pre-session behavior) rather than ship a fix that measurably makes it
worse. Everything else about major-heap integration stands as
assessed earlier: `caml_alloc_shr`/`verified_allocate`'s actual
allocation and collection logic is unaffected by any of this (never
touches `bump_ref` for correctness, only for these now-reverted stat
lines), confirmed working under real OOM-driven collection pressure by
`major_gc_test.ml`.

---

## Smoke tests — the existing bytecode suite, extended to native

`tests/Makefile`'s `test` target runs 8 Computer Language Benchmarks
Game programs (binarytrees, fasta, quicksort, fannkuchredux,
count_change, nbodies, spectralnorm, mandelbrot) once each against the
verified GC's bytecode `ocamlrun` — real, independently-authored
programs with much more varied allocation patterns than anything
written for this session (deep tree construction/teardown, string
building, in-place array sorting, floating-point n-body simulation,
matrix-free power iteration, PPM image generation).

Ran `make test` first: all 8 pass unchanged against the bytecode
runtime, confirming the `caml_empty_minor_heap` fix from Phase 5 (which
touches `minor_gc.c`, shared with bytecode via its `#else` branch)
didn't regress anything broader than this session's own bespoke tests
already covered.

No native equivalent existed in the Makefile, so built one ad hoc:
compiled all 8 `.ml` files with the stock `ocamlopt` against our
`libasmrun.a` (same `-I vergc_lib` linking trick used throughout this
session), ran each with the exact same arguments and
`MIN_EXPANSION_WORDSIZE` the bytecode target uses. All 8 pass. Cross-
checked output against both the bytecode run and a build linked to
stock's own `libasmrun.a`:

- Every program's output matches the bytecode run exactly, including
  `nbodies`/`spectralnorm`'s floating-point energy/norm values
  (`-0.169075164`/`-0.169087605`, `1.274219991`) — numerically
  sensitive enough that any memory corruption would very likely have
  shown up as a different number, not just a crash.
- `diff`'d five of the eight (`binarytrees`, `nbodies`, `spectralnorm`,
  `fannkuchredux`, `count_change`) against stock native byte-for-byte —
  identical in every case.

This is meaningfully broader smoke coverage than anything in this
session's own test files (all independently-authored, pre-existing
benchmark code, not written to exercise this integration specifically)
and it passed cleanly on the first attempt with no fixes needed.

---

## Native smoke tests, follow-up: `spectralnorm` failure reveals the open bug is worse than scoped

Added a checked-in `test-native` target to `tests/Makefile` (mirroring
`test`, same programs/args/heap sizes, building each `.ml` with the
stock `ocamlopt` via `-I $(VERGC_NATIVE_RUNTIME_DIR)` instead of
running `.byte` files under `ocamlrun`). Running it cold turned up a
real failure that the earlier ad hoc scratchpad run had not shown:
`spectralnorm.native` crashes with
`verified gen GC: internal error — unpromoted root after gen_gc`.

This was surprising because the scratchpad run of the *exact same
program* passed and matched stock byte-for-byte. Investigated rather
than assumed it was a fluke:

- Confirmed via `sha256sum`/`cmp` that the failing `tests/spectralnorm.native`
  and the passing scratchpad `spectralnorm.vergc` are **byte-identical
  binaries** — not a stale build or a different link.
- Renamed the exact same (byte-identical, `sha256sum`-verified) binary
  to different filenames and reran with no other change. Result flips
  between the correct answer (`1.274219991`) and the fatal error purely
  based on the string length of `argv[0]`:

  | argv[0] length | result |
  |---|---|
  | 12–13 | pass |
  | 14–15 | **fail** |
  | 16–21 | pass |
  | 22–23 | **fail** |
  | 24–29 | pass |
  | 30–31 | **fail** |
  | 36, 41 | pass |
  | 46 | **fail** |
  | 51 | pass |

  20/20 repeated runs at a "pass" length all pass; 20/20 at a "fail"
  length all fail — fully deterministic per length, not ASLR noise.

**Why this matters more than the original scoping of this bug**: the
deep-stack-roots investigation characterized this "unpromoted root"
family of errors as needing thousands of simultaneous live native
stack frames plus an artificially tiny heap — a synthetic, unlikely-
to-occur-in-practice scenario. `spectralnorm.ml` is an ordinary,
independently-authored benchmark (simple nested loops over float
arrays, no recursion at all, default 2MB minor heap, a generous 256MB
major heap) — nothing about it looks like stress-testing. The fact
that its pass/fail outcome hinges entirely on `argv[0]`'s length points
at the true mechanism: `caml_alloc_string` for argv[0] is one of the
very first allocations at process startup (confirmed by observation
earlier this session), and its exact byte length determines how many
words it consumes — shifting every allocation address that follows by
a few bytes. Some shifts happen to land wherever the still-unresolved
address-off-by-one-word issue lives; most don't. **This means the bug
is not a narrow synthetic edge case — it can affect ordinary native
programs, unpredictably, based on nothing more than install path or
binary filename length.**

`tests/Makefile`'s `test-native` target is left in place (it did
exactly its job — this is a real, meaningfully worse-than-previously-
known finding, not a reason to hide the test), but as of this session
it will deterministically fail on `spectralnorm` given its current
filename. Task #8 (tracking this bug) has been updated to reflect the
new severity and the argv[0]-length evidence, in case whoever picks it
up next wants a much more promising lead than the original
deep-stack-roots trace: sweep argv[0] length systematically against a
*minimal* repro (not a full benchmark) to find the exact byte offset
where the corruption starts, rather than starting from a 4000-frame
recursion.

---

## Deep-dive on the spectralnorm failure — traced further, not yet resolved

Went deeper on the argv[0]-length-sensitive `spectralnorm` failure at
the user's direction, since the new lead (a small, ordinary benchmark,
not a 4000-frame synthetic stress test) looked far more tractable than
the original repro.

**Traced the exact mechanism**, using temporary `fprintf` instrumentation
at each layer (all fully reverted afterward — see below):

1. `caml_make_vect` (`array.c:227`, the `FLAT_FLOAT_ARRAY` branch,
   `tag=Double_array_tag=254`) calls `caml_alloc(wsize, Double_array_tag)`
   where `wsize` should be `100` (from `Array.make 100 1.0`).
2. Instead, `caml_alloc_shr` is entered with
   `wosize=4461767045439297` (`0xfd9f417d05f41`) — nonsensically large,
   forcing the `wosize > Max_young_wosize` branch that a 100-element
   array should never reach.
3. This "large" (bogus) request predictably fails to fit even a 256MB
   major heap, triggering `do_full_gc()` — which is what then hits the
   `unpromoted root after gen_gc` fatal error, on a heap that was
   already in a bad state before the collector ever ran.

**The bogus wosize value is the real puzzle, and it's stranger than
first assumed**: `0xfd9f417d05f41` recurs *byte-identically* across
dozens of runs with completely different ASLR-randomized addresses.
That rules out "reading an uninitialized stack slot" or "misreading a
stray pointer" (both would vary run to run) and points at something
more structural — though checking it against embedded binary data,
float reinterpretation, and known size constants (`Max_wosize`, etc.)
found no match.

**Ruled out, with direct evidence, not assumption**:
- *`Sys.argv` corruption*: instrumented `Array.iteri` over `Sys.argv`
  in the `.ml` source itself — confirmed correct (`"100"`) in every
  single failing case. The argv[1] value reaching `int_of_string` is
  never the problem.
- *Exception fallback to `n=2000`*: an early `gdb` session showed
  `wosize=2000` at a breakpoint on `caml_alloc_shr`, suggesting
  `Array.get Sys.argv 1` was failing and falling back to the `with _ ->
  2000` default. This was a red herring — running under `gdb` is
  itself an environmental change (like renaming the binary or
  recompiling) that shifts memory layout and can change which failure
  mode appears, or whether one appears at all.

**Important methodological finding, worth preserving for whoever
continues this**: recompiling the `.ml` file — even just adding
`Printf.eprintf` debug lines — shifts *which* `argv[0]` lengths trigger
the bug. A length that reliably crashed before a rebuild started
passing after one, purely because the rebuild shifted subsequent
addresses the same way renaming the binary does. This means **"does it
still crash after my change" is not a valid test of whether a fix
worked** — any change to the binary can accidentally realign things
and mask the bug at whatever config you happen to be testing, while
leaving it fully present elsewhere. The sweep-of-lengths approach
(this log, previous section) survives this trap because it holds the
binary fixed and only changes the filename; adding instrumentation
that requires recompilation does not.

**Recommended approach for whoever continues this**: pick one fixed
binary that reproduces reliably (confirmed via a spot-check, not
assumed), and use `gdb` watchpoints (`watch`) on the `wsize`/`size`
local variables inside `caml_make_vect`, or on the exact stack address
holding them, rather than adding source-level prints that require
rebuilding. Start from `array.c:209-227` and `alloc.c`'s `caml_alloc`
dispatch. Not yet established whether this shares a root cause with
the original `deep_stack_roots` "root ends up one word off" trace, or
is a distinct bug in the same general "memory-layout-sensitive
corruption" family — that connection (or lack of one) is the most
valuable open question for a fresh investigation to resolve first.

**Cleanup**: all `fprintf` instrumentation added during this
investigation (in `do_full_gc`, `rewrite_root_from_forwarding`,
`do_minor_gc`'s proactive branch, `verified_allocate`'s OOM branch,
`caml_trigger_verified_gc`, and `caml_alloc_shr`) was fully reverted.
Confirmed `alloc_gen.c` and `memory.c` are back to their pre-
investigation state and regenerated `patches/runtime_gen.patch`
accordingly. Re-ran the full regression suite (`hello`,
`regression_test`, `alloc_test`, `deep_stack_roots` at the default
heap, `major_gc_test` at both default and small major heap sizes) —
all still pass, confirming this investigation left no regressions
despite not reaching a fix.

---

## Extended overnight investigation — real progress, root cause still not found

Continued the `spectralnorm` investigation much further at the user's
request ("spend all night trying to fix it"). No fix landed, but this
session materially narrowed the search space and — importantly — found
and documented a hard methodological trap that would otherwise cost
the next investigator significant time. All source files are
confirmed reverted to their pre-investigation state (verified via
`git diff --stat`) and the standard regression suite passes cleanly.

### Methodology established

Two separate techniques were confirmed, empirically, to perturb this
bug's exact manifestation:

1. **Recompiling** (already known from the earlier session) — shown
   again here: rebuilding at `-O0` for debuggability shifted which
   `argv[0]` lengths trigger the bug, though the *pattern* stayed
   exactly periodic (period 8, matching word alignment) in every build
   tried.
2. **Live `gdb`/`ptrace` attachment** — newly discovered, more subtle:
   even the lightest possible touch (one breakpoint hit, read a few
   registers, `detach` with zero modifications, before the program is
   allowed to run to completion on its own) changes the outcome. Two
   different gdb sessions on the *same* reliably-failing binary
   produced two *different* crash symptoms (a `SIGSEGV` inside
   `caml_putblock` in one case, a larger core in another) — neither
   matching the `SIGABRT`/"unpromoted root" error that binary produces
   100% reliably when run standalone. This means **any conclusion drawn
   from a live gdb session on this bug is suspect** unless independently
   confirmed via the technique below.

**The reliable technique found**: this crash is a `caml_fatal_error()`
→ `abort()` → `SIGABRT`, and this system runs `systemd-coredump`
(confirmed active), so every natural crash produces a real core file,
retrievable via `coredumpctl gdb <path-to-still-existing-binary> -1`.
This lets the process run **completely unperturbed, start to finish**,
and inspects the corpse afterward — no ptrace during the actual
execution that matters. Every core dump analyzed this way reproduced
the exact same "unpromoted root after gen_gc" signature.

**Important caveat discovered about post-mortem analysis**: register
and stack-frame-saved values in the core dump are trustworthy (frozen
at call time, never touched again). **Heap *content* is not** — by the
time the process aborts, `do_full_gc()` has already run a substantial
amount of its own work (root gathering, `gen_gc`'s attempted
evacuation) before the final consistency check fails, and this can
legitimately zero out or rewrite memory that held different content at
the moment the original corruption actually happened. Concretely: a
value's header read as all-zero in a post-mortem dump does *not* mean
it was zero at the time of corruption — it may have been overwritten
by the crashing collection's own (failed) attempt to process it.

AddressSanitizer was attempted as a faster path to an authoritative
answer, but the system's ASan runtime library is not actually
installed (`libasan.so` is a linker script pointing at a path that
doesn't exist) — closed off without installing packages, which wasn't
done unprompted.

### What was traced, concretely

Using the core-dump technique above (confirmed reproducible across 7+
independent crashes at different `argv[0]` lengths, all showing
*byte-identical* corrupted values):

- The crash originates from `eval_AtA_times_u`'s `let w = Array.make
  (Array.length u) 0.0` — specifically, `Array.length u` (compiled as
  a direct header read + `shr $0x9` + `or $1`, a standard OCaml native
  optimization) returns a nonsensical value, which flows into
  `caml_make_vect` as `len`, then into `caml_alloc`'s dispatch as
  `wosize`, forcing the "large allocation" branch for what should be a
  100-element array — this is why the failure surfaces as a major-heap
  OOM inside `verified_allocate`/`do_full_gc`, even though the actual
  defect is upstream of any GC code.
- **Ruled out, with direct evidence, not inference**: `Sys.argv`
  corruption (checked directly, correct in every failing case in an
  earlier build); the exception-fallback `n=2000` path (an earlier
  `gdb`-based finding that turned out to be exactly the kind of
  gdb-induced artifact described above — a *different* build's
  post-mortem trace, unaffected by gdb, shows the true corrupted value
  is a **fixed, ASLR-independent constant** — `0x1fb3e82fa0be83` when
  tagged — ruling out any theory involving a stray/uninitialized
  pointer, which would vary with ASLR); a `Whsize_wosize`/profinfo
  size-computation mismatch (verified both are simple, unconditional
  macros, identical for every allocation site); an off-by-one in
  `caml_make_vect`'s float-array fill loop (`for (i = 0; i < size;
  i++)`, checked directly against the source — no off-by-one); a bug
  in the compiled `Array.length` sequence itself (verified bit-by-bit
  that `(header >> 9) | 1` is robust to any color-bit value, always
  producing the correct tagged wosize regardless of the header's low
  bits — the sequence is correct); **a root-rewrite bug during a real
  minor collection** (the leading hypothesis for a while, since it
  would connect directly to the original `deep_stack_roots` finding —
  directly disproved by reading `Caml_state->_stat_minor_collections`
  from the core dump: it reads **0** at the crash, meaning no real
  minor collection ever ran before the corruption; whatever
  loses `u`'s data does so without any collection involved at all).

### The most concrete lead for whoever continues this

Reading `u` and `v`'s actual runtime addresses and the domain state's
`_young_alloc_start`/`_young_alloc_end` directly from a core dump
(all frozen, trustworthy stack/register values) revealed a genuine,
confirmed violation of native's allocation invariant:

- `u = Array.make n 1.0` is unambiguously the *first* of the two
  allocations (confirmed three independent ways: source order, the
  compiled instruction stream — its `caml_make_vect` call executes
  textually and temporally first — and the actual float constant at
  its `init` argument's address, read directly from the binary's data
  section, is `1.0`, not `0.0`).
- `v = Array.make n 0.0` is the second allocation, immediately after,
  with **no other allocation and no collection in between** (confirmed
  via `_stat_minor_collections == 0`).
- Native allocates by decrementing `young_ptr` — every subsequent
  allocation must land at a *lower* address than every previous one,
  with no exceptions, in the absence of a collection.
- **Measured instead**: `v`'s address is *closer* to
  `_young_alloc_end` (the top) than `u`'s — by exactly 808 bytes, which
  is exactly `Whsize_wosize(100) * 8` (one 100-float array, header
  included). `v`, the *second* allocation, ended up positioned as if
  it were allocated *before* `u`, the first — a direct violation of
  the monotonic top-down invariant that Phase 1-4's extensive testing
  (thousands of real collections, all compiler-inlined `Ialloc`
  allocations) never once exposed.

The one structural difference between this pattern and everything
tested successfully all session: `u` and `v` are both allocated via
`caml_make_vect`, a C function reached through `caml_c_call` (the
general "compiled code calls a C primitive" trampoline), using the
*C-level* `Alloc_small_aux` macro — not the compiler's inlined
`Ialloc` fast path that every previously-tested allocation used.
`caml_c_call`'s own mechanism was read directly in `amd64.S` and looks
correct in isolation (`movq %r15, Caml_state(young_ptr)` before the
call; compiled code reloads `%r15` from the same field immediately
after each of the four call sites this function uses) — but something
in how `young_ptr` propagates specifically across **two consecutive**
such C-primitial-allocation call sites does not preserve the
monotonic-decrease invariant that same-fast-path allocations always
have. This is a genuinely new, more specific, and more promising lead
than anything in the original `deep_stack_roots` trace — recommend
starting here: construct a minimal repro that does exactly two
back-to-back `caml_make_vect` (or other C-primitive `Alloc_small`)
calls with nothing else happening in between, and use the core-dump
technique above (never live `gdb`) to check whether the same address-
ordering violation reproduces in isolation, without spectralnorm's
surrounding complexity.

### Cleanup

All investigation used command-line `CFLAGS`/`OC_CFLAGS` overrides
(`-O0`, `-g`, briefly `-fsanitize=address`) to rebuild
`libasmrun.a`/`libvergc_gen_native.a` — no source files were edited
this round. Confirmed via `git diff --stat` that `alloc_gen.c`,
`memory.c`, `minor_gc.c`, `startup_nat.c` show only the pre-existing,
already-logged diffs from earlier phases, with `array.c`/`alloc.c`/
`main.c` showing no diff at all. Rebuilt the normal `-O2` production
`libasmrun.a`/`ocamlrun` and re-ran the full regression suite (`hello`,
`regression_test`, `alloc_test`, `deep_stack_roots`, `major_gc_test`
at both heap sizes) — all pass, confirming this extended investigation
leaves the codebase exactly as it was, with substantially better
documentation of the bug for next time.

---
