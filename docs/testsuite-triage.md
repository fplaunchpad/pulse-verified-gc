# OCaml testsuite triage — PR #3 (`alloc-exactness-rightjust`)

Run [34925353663](https://github.com/fplaunchpad/pulse-verified-gc/actions/runs/34925353663),
head `1426bc2`, 2026-09-15, 27m 29s. Companion `verify` run: 30m 50s against the
merge-base's 31m 48s, so the proof work costs nothing in CI.

```
passed=2923  failed=29  errors=40  skipped=43  not_started=106  considered=3141
expected-failure entries: 71   new: 0   fixed: 2
```

**Verdict: nothing is failing that is not accounted for.** All 69 failures are in
`ci/expected-failures.txt`, two tests newly pass, and every failure traces to one of
seven named gaps. None of them is the allocator.

## The two results this branch was for

- `tests/ast-invariants/'test.ml'` — **passes**, both `1 (hasunix)` and `1.1 (native)`.
  This is the SIGSEGV that motivated the whole change and the one entry the baseline
  deliberately refused to record. On its own it is **weak** evidence that the fix works,
  because it passes on `main` too — see the section below.
- All of `tests/lib-hashtbl` passes. `Hashtbl`'s `land (Array.length - 1)` masking was
  the mechanism that turned the over-sized header into a wild read, so it is the right
  place to look for a regression, and there isn't one.

Newly passing versus the baseline:

| test | note |
|---|---|
| `tests/asmcomp/'polling_insertion.ml' with 1.1 (native)` | poll-point insertion |
| `tests/lib-threads/'torture.ml' with 1.1 (bytecode)` | previously flaky under load |

Neither is a consequence of right-justification, and this is now measured rather than
guessed: both are newly passing on `main` too (run 34926016097, `31ee076`). They are
baseline drift against the reference branch the list was measured on — exactly what the
file's own provenance note warns about.

## CI caught this bug once, then stopped — and that is the real problem

The baseline's note predicted exactly one new failure, and **CI did catch it.** Run
[33661032604](https://github.com/fplaunchpad/pulse-verified-gc/actions/runs/33661032604),
2026-09-02, `push` on `a674bc1`:

```
passed=2923 failed=27 errors=42 considered=3141
expected-failure entries: 71  new: 1  fixed: 3
  NEW FAILURE: tests/ast-invariants/'test.ml' with 1.1 (native)
```

with `Process 25168 got signal 11(Segmentation fault), core dumped`. So the pipeline
works, and the red check on PR #2 was this.

Three days later the check went green on what the API reports as the **same head SHA**.
That is an event artefact, not a mystery: the Sept 2 run was a `push` and tested
`a674bc1` directly, while the Sept 5 run was a `pull_request` and tested
`refs/pull/2/merge` — and `a8cdacb` had landed on the base 26 minutes earlier. The two
trees differ by 24 lines of `alloc_gen.c` (major-heap exhaustion returning NULL instead
of aborting) plus, in `runtime_gen.patch`, a restored
`if (wosize > Max_wosize) return 0;` and a new `if (hp == NULL) return 0;` in
`caml_alloc_shr_aux`.

**Those 29 lines cannot explain the flip, and this is provable rather than a guess:
`generational/snapshot/` is byte-identical between `a674bc13` and `a8cdacbc`.** The
extracted `allocate()` -- the one containing `makeHeader(block_wz, white, 0ULL)` -- was
the same code in the failing run and the passing run, so the bug was equally present in
both. Taking the delta apart:

- `if (wosize > Max_wosize) return 0;` restored -- `Max_wosize` is 2^54 - 1 words,
  unreachable for any real program.
- `if (hp == NULL) return 0;` added -- on `a674bc13`, `verified_allocate`'s only
  `return NULL` sits *after* `caml_fatal_error(...)`, so it is unreachable and there was
  no NULL to guard against.
- `caml_fatal_error` -> hint + `return NULL` -- fires only on major-heap exhaustion after
  a collection, and that path aborts (SIGABRT), not the SIGSEGV Sept 2 reported.

None of them touches `alloc_search`, the split arms, the header write, coalescing, or the
minor/major boundary. So the flip is *not* explained by the code difference, which leaves
run-to-run variation in whether the test presents a `wz + 1` free block. The reports
corroborate that independently: `lib-systhreads/eintr (bytecode)` passed on Sept 2 *and*
Sept 5 and is in the error list today, and the tallies drift 27/42 -> 29/39 -> 29/40
across three runs with no allocator change between the last two.

The lesson is not about these commits. A gate whose outcome depends on allocation
sequencing cannot be reasoned about from commit diffs at all, which is why
`generational/snapshot/alloc_exact_test.c` exists: it presents the tight fit on every run
and fails on any pre-fix snapshot regardless of event type, base branch, heap pressure or
allocation order.

The consequence matters more than the cause:

- `main` at `31ee076` carries the **old** allocator and its report is behaviourally
  identical to this branch's — same 69 failures, same summary, `ast-invariants` passing
  on both. That is **one sample**, not evidence the old allocator is safe.
- Equally, this branch's green run is not by itself evidence of the fix.
- The deterministic evidence is the local A/B: exit 139 (SIGSEGV, core dumped) before,
  exit 0 after, same machine and binary, only the snapshot differing, checked in both
  directions under `MIN_EXPANSION_WORDSIZE=8388608`.

Why the heap size is the lever: the bug needs a free block *exactly one word* longer than
the request. The default major heap is 32M words = 256 MB
(`verified_gc/alloc_gen.c:109`); the documented repro uses 8M words = **64 MB**, where
collection churn produces the tight fit reliably. Nothing under `.github/` or `ci/` sets
that variable — its only mention in the CI tree is the how-to-reproduce comment in
`ci/expected-failures.txt` itself. So CI runs the one discriminating test at the heap size
where it is a coin flip.

## How the 69 break down

| # | cause | verdict |
|---|---|---|
| 32 | weak pointers, ephemerons, finalisers | not implemented |
| 24 | `Gc.Memprof` allocation sampling | not implemented |
| 3 | signal handlers not run at allocation safe points | integration gap |
| 3 | `Gc.set` knobs the verified heap cannot honour | unsupported by design |
| 3 | build and link packaging | not GC behaviour |
| 2 | fixed-size root buffer | capacity limit |
| 2 | custom-block finalisation | not implemented |

Signal distribution: 33 SIGSEGV, 3 SIGABRT, 3 timeout, 30 output-mismatch or
non-zero exit.

### 32 — weak pointers, ephemerons, finalisers

`misc/ephetest{,2,3,_new,2_new}`, `misc/ephe_infix{,_new}`, `misc/ephe_issue9391`,
`ephe-c-api/test`, `misc/weaklifetime{,2}`, `misc/finaliser`, `tool-ocaml/t340-weak`,
`tool-ocaml/t350-heapcheck`, `lib-sys/opaque`, `backtrace/callstack`,
`c-api/alloc_async`.

The collector implements no weak table, ephemeron list or finaliser queue. Three of
these are worth naming because the test name does not give the cause away:

- `lib-sys/opaque.ml` looks like a `Sys.opaque_identity` test, and it is — but its
  middle third calls `Gc.finalise` and asserts on finaliser timing across
  `Gc.full_major ()`.
- `backtrace/callstack.ml` likewise installs `Gc.finalise (fun _ -> f0 ()) [|1|]` and
  prints a backtrace from inside the finaliser.
- `c-api/alloc_async.ml` reads as a C-allocation test, and its failure looks like a
  polling gap, but its subject is `Gc.finalise (fun s -> r := !s) (ref 17)`. The C stub
  forces a major cycle so that finaliser becomes pending; the test then checks it did
  *not* fire asynchronously inside the C code (`C, after: 42`) and *did* fire at the next
  OCaml allocation (`OCaml, after alloc: 17`). We print `42`, so it never ran at all.
  The allocation is only how the test observes the finaliser queue, which is why this
  belongs here and not under the safe-point gap below.

`misc/weaklifetime2.ml` is the one failure in this group whose mechanism is worth
recording, because it aborts on an **internal consistency check** rather than simply
misbehaving:

```
verified gen GC: internal error — unpromoted root after check
```

emitted by `write_back_rewritten_roots` (`generational/ocaml-integration/verified_gc/alloc_gen.c:331`),
which requires every rewritten root to come back as a major-heap address. The
reconstruction, consistent with the code and the test but not stated by the log:
`Weak.set` deliberately takes no write barrier, so a major-heap weak array pointing into
the minor heap is neither a root nor a `ref_table` entry. Stock fixes those fields up
explicitly during minor collection; we do not, so the array keeps a stale minor address.
A later `Weak.get` hands that stale value back to live code, the next
`scan_minor_root` collects it as a minor-absolute root, Cheney has no forwarding entry
for it, and the check fires. If that is right it is a *downstream* symptom of the missing
weak table, not an independent bug — but it is the only failure here that trips an
invariant we wrote ourselves, so it is the one to re-examine when weak support lands.

### 24 — `Gc.Memprof` sampling

Every `tests/statmemprof/*` entry. `Gc.Memprof.start` has no implementation, so these
either produce no samples (output mismatch), exit non-zero, or hang —
`blocking_in_callback` and `moved_while_blocking` account for all three timeouts.

### 3 — signal handlers not run at allocation safe points

`callback/signals_alloc`, `lib-systhreads/eintr` (bytecode + native).

These are the most allocator-adjacent failures in the run, and they are about *when* the
allocator yields, not what it returns.

A Unix signal cannot run its OCaml handler at the instant it arrives: the handler is
OCaml code that allocates, and the GC must see consistent roots, which is not true at an
arbitrary instruction. So the C-level handler only records that something is pending, and
the runtime runs it at the next *safe point* via `caml_process_pending_actions` — which
covers signal handlers, finaliser callbacks and memprof callbacks alike. In 4.14 the
primary safe point is an **allocation**: the handler sets `young_limit` so the next minor
allocation appears to be out of room, `caml_alloc_small`'s fast path fails, and
`caml_call_gc` processes pending actions before returning.

`verified_allocate` and the minor bump path consult neither `young_limit` nor
`caml_process_pending_actions`, so an allocation is no longer such a point. Deferred work
still runs, at compiler-inserted polls and function returns — just later than stock.

`signals_alloc` measures precisely that:

```ocaml
seen_states.(!pos) <- 2; pos := !pos + 1;     (* writes 2 *)
let _ = Sys.opaque_identity (ref 1) in        (* allocation: handler should write 3 *)
seen_states.(!pos) <- 4; pos := !pos + 1;     (* writes 4 *)
```

The handler writes `3`. Stock produces `01234`; we produce `01243`, so the handler ran
after the allocation rather than at it.

`eintr` adds threads and `Thread.sigmask`. Its SIGSEGV is consistent with a handler
running while root state is inconsistent, but the log does not pin the mechanism and I am
not going to claim it does.

Note this area is live: main's `5ce4480` ("Do not route `caml_check_urgent_gc` through
`caml_gc_dispatch`") is the same integration surface.

### 3 — `Gc.set` knobs the verified heap cannot honour

- `regression/pr9326/gc_set.ml` (SIGSEGV) sets `minor_heap_size = 512k` and
  `major_heap_increment = 4M`. The verified minor heap is fixed at startup; resizing it
  under the running collector leaves the young pointers dangling.
- `regression/pr9292/pr9292.ml` (both variants) sets `allocation_policy = 2` (best-fit),
  which does not exist here, and then allocates 5,000 × 10,000-word arrays — about
  400 MB into a 256 MB major heap. It now reports

  ```
  verified gen GC: major heap exhausted (256 MB) — raising Out_of_memory.
  ```

  which is main's `a8cdacb` working as intended: a catchable `Out_of_memory` instead of a
  fatal abort. The test still fails, because it does not expect the exception, but it
  fails *politely*.

### 3 — build and link packaging, not GC behaviour

- `instrumented-runtime/main.ml` needs `-runtime-variant=i`; the verified build does not
  produce `libasmrun_i.a`, so `ocamlopt` exits 2.
- `output-complete-obj/test.ml` (both script variants) fails at `ld`, not at run time:

  ```
  undefined reference to `caml_startup', `minor_heap_size_u64', `zero_addr',
  `heap_size_u64', `max_young_wosize_u64', `krmlinit_globals', `caml_do_roots', ...
  ```

  `-output-complete-obj` emits a self-contained object linked against `libcamlrun.a`
  alone, and the verified GC's objects and KaRaMeL globals are not in that archive. A
  packaging fix, with no bearing on collector semantics.

### 2 — fixed-size root buffer

```
verified gen GC: root overflow          alloc_gen.c:256
```

- `typing-modules/merge_constraint.ml (expect)`
- `unboxed-primitive-args/test.ml (ocamlopt.byte)` — aborts while *compiling*, exit −6

Both look GC-unrelated from their names, and both are the same thing: the failing process
is an OCaml **tool** (`expect_test`, `ocamlopt`) running on the verified runtime, and it
exceeds `MAX_ROOTS = 1 << 18` (`alloc_gen.c:82`) during `caml_do_roots`. `unboxed-primitive-args`
generates a very large source file, which is why it is the one that tips over. Raising
`MAX_ROOTS`, or growing the buffer dynamically, would likely clear both — they are a
capacity limit in the bridge, not a collector defect.

### 2 — custom-block finalisation

`regression/pr3612` (both variants) round-trips a custom block through `Marshal` a million
times and prints deserialised-minus-freed. Custom-block finalisers never run, so the
counter never drops and the output differs.

## What this run does not tell us

- The gate is "no NEW failures". A test that regresses *within* the baseline — same
  entry, different reason — would not be flagged. Nothing here suggests that happened,
  but the report cannot rule it out.
- `verify` runs with `--retry 3` (`Makefile:26-38`), so green means less than it looks.
- 106 tests are `not_started` and 43 skipped, mostly platform and configuration gates
  (flambda disabled, no libwin32unix, non-x86 targets). Those are properties of the
  runner, not of the collector.

## Timeouts are not failures, and the gate cannot tell

Three times now the gate has gone red on one check and green on another for the
same commit, and each time the test involved was timing-sensitive rather than
broken:

| when | red check | green check |
|---|---|---|
| run 33661032604, attempts 1 vs 2 | `ast-invariants` (native) | — |
| PR #3, push vs pull_request runs | `misc/weaktest.ml` (native) | `lib-systhreads/eintr` (bytecode) |

`weaktest` is the clearest case because the reason string says so outright --
`Timeout expired, killing all child processes`, never a signal -- and the
bytecode variant passed in both runs. Measured locally on the fixed allocator:

```
native weaktest, verified GC:  108.31 s      harness budget was TIMEOUT=120
native weaktest, stock OCaml:    0.20 s      ~540x slower
```

So it sat ~10% under the limit and flapped with runner load. `TIMEOUT` is now
300 in `.github/workflows/testsuite.yml` and `ci/run-testsuite.sh`.

Two things this corrects in the earlier sections of this document.

The 540x is itself a finding, and it belongs with the weak/ephemeron/finaliser
group: the collector implements no weak table, so a program that hammers a
`Weak` hashtable degrades enormously. That is a performance consequence of the
same gap, not a separate defect.

And the "the crash traded places, totals conserved" reading was over-drawn. In
both pairs the totals happened to match at 69, but each run simply contained
exactly one timing-sensitive failure; two coin flips landing on the same count
is not conservation. The substantive point survives in weaker form: a green
"no new failures" can coexist with a different test having taken the hit, so
the tally alone is not evidence that nothing changed.

## Follow-ups this triage suggests

0. **Done: gate on the deterministic tests, not on `ast-invariants`.** The
   earlier suggestion here -- pin `MIN_EXPANSION_WORDSIZE` and re-run
   `tests/ast-invariants` in CI -- is superseded. `ast-invariants` detects this
   bug only when the phantom field happens to be followed and faulted on, which
   is why it fails 100% on Fedora 44 / gcc 16 and passes 15/15 on
   `ubuntu-latest` with the allocator provably broken in both. Two checks now
   decide on the code instead of on the platform, and both run in
   `testsuite.yml` ahead of the suite:
   `generational/snapshot/alloc_exact_test.c` drives the extracted allocator
   directly, and `ci/run-promotion-test.sh` drives the promotion path end to
   end and asserts on the promoted objects' own lengths.
1. **Do not baseline `weaktest` (or `eintr`).** Both are timing-sensitive and
   pass most of the time; recording either as an expected failure would hide a
   real weak-pointer or signals regression later. `ci/expected-failures.txt`
   now carries that warning where someone would go to add the line.
2. **Raise `MAX_ROOTS` or make the root buffer grow.** Two failures, both of them OCaml
   tools rather than test programs, and the cheapest fix on the list.
3. **Re-examine `weaklifetime2`'s internal-error abort when weak support lands.** It is
   the only failure that trips an invariant we wrote, and the reconstruction above should
   be confirmed rather than assumed.
4. **Process pending actions at allocation points.** Restores the safe point stock
   relies on, fixing `signals_alloc` and plausibly `eintr`. It would also make
   `alloc_async` observable once finalisers exist — today that test fails one layer
   earlier, on the empty finaliser queue. Adjacent to work already on main.
5. **Reject unsupported `Gc.set` fields instead of corrupting the heap.** `pr9326`
   segfaults where raising `Invalid_argument` would be honest.
