# Phase 0 spike: parallel mark-and-sweep

Branch `sheera/spike-parallel`. Spikes 1 and 2 touched no existing GC file. Spike 3 adds one `#ifdef`'d call to `generational/snapshot/GC_Gen_Impl.c`, on this branch only.

Toolchain: the pinned `./fstar` only.

- F* `nightly-2026-08-15` (commit `ae858eac`).
- KaRaMeL `2309d841`.
- Z3 4.15.3.
- The F* flags are the repo's own, copied into `fstar.flags`.
- krml was run the same way as `generational/Makefile`: `-skip-compilation -skip-linking -warn-error -2-9-15`.

## Outcome: stopped before the spike program

The specified program cannot be built with this toolchain without a workaround, so the spike stopped there. Two blockers, each independent of the other:

1. **No U64 compare-and-swap exists** (Q2). The program as specified cannot be written against the library.
2. **`Pulse.Lib.Par.par` does not extract to C** (Q1). Even with a CAS available, the two-thread composition cannot reach C.

So the ThreadSanitizer run and the OCaml 4.14 bytecode and native builds were **not performed**: there is no extracted C to compile. Q1 and Q2 are answered by two small probe modules. Each isolates one library primitive and uses only library code, with no shims.

| File | Purpose | Verifies | Extracts to C |
|---|---|---|---|
| `Spike.ParProbe.fst` | `par` over two disjoint `box U64` writes | yes | **no**: krml drops `run_par` |
| `Spike.CasProbe.fst` | a single call to the library's `cas_box` (U32) | yes | yes, but not atomic (see Q2) |

---

## Q1. Parallel composition

**Answer.** The module is `Pulse.Lib.Par`, which provides `par` and `par_div`. A pooled alternative is `Pulse.Lib.Task` (`setup_pool` / `spawn` / `await`). Both verify, but **neither extracts to C at all**: not to OS threads, and not to sequential code. krml rejects them, and the thread-creation primitive underneath has no implementation in C or OCaml.

**Evidence.**

- `Pulse.Lib.Par.fsti`: `divergent fn par … {| is_send preL, … |} (f: unit -> stt unit preL (fun _ -> postL)) (g: …)`.
- `Pulse.Lib.Par.fst:34-40` implements it as `create` a condition variable, `fork'` a closure that runs `f ()` and then `signal c`, run `g ()`, then `wait c`.
- `fork'` (`Pulse.Lib.Send.fst:482`) is `inline_for_extraction noextract` and calls `Pulse.Lib.Core.fork_core` (`Pulse.Lib.Core.fsti:658`). That is an abstract `val`.
- `grep -r fork_core` over the whole toolchain finds only those two F* files. There is no `.c`, `.h` or `.ml` realization, and neither `krml` nor `fstar.exe` contains the string, so neither special-cases it.
- `Pulse.Lib.Task` reaches threads through the same path: `spawn_worker` calls `fork' … (fun () -> worker_thread …)` at `Pulse.Lib.Task.fst:1478`.
- The condition variable spins on `Primitives.read_atomic_box` and `write_atomic_box` (`Pulse.Lib.ConditionVar.fst:172,256`), so it inherits the Q2 problem as well.

**krml on the probe** (`Spike.ParProbe.run_par` calls `par #(a |-> 0UL) #(a |-> 1UL) #(b |-> 0UL) #(b |-> 2UL) (left a) (right b)`):

```
Warning 16: Cannot enforce arity at call-site for Spike.ParProbe.left (Invalid_argument split -- is this a partial application?)
Cannot re-check Spike.ParProbe.run_par as valid Low* and will not extract it.
Warning 4: in the arguments to Pulse.Lib.Par.par, in top-level declaration Spike.ParProbe.run_par, in file Spike_ParProbe: Malformed input:
subtype mismatch:
  () (a.k.a. ()) vs:
  () -> () (a.k.a. () -> ())
```

The emitted `Spike_ParProbe.c` contains only `write_one`, `left` and `right`. `run_par` is gone.

**krml on `Pulse.Lib.Par` itself** (extracted with `--extract_module Pulse.Lib.Par`):

```
Cannot re-check Pulse.Lib.Par.par as valid Low* and will not extract it.
Warning 4: in the arguments to @3, in the arguments to Pulse.Lib.Core.fork_core, in the sequence statement at index 0,
  after the definition of c, in top-level declaration Pulse.Lib.Par.par, in file Pulse_Lib_Par: Malformed input:
subtype mismatch: () vs: () -> ()
Cannot re-check Pulse.Lib.Par.par_div as valid Low* and will not extract it.
KaRaMeL: wrote out .c files for          <- empty
```

The root cause is that `par` passes closures (`f`, `g`, and the `fn _ { f (); signal c }` that `fork_core` receives). Low* and C have no closures.

**krml on `Pulse.Lib.Task`:**

```
Not extracting type definition Pulse.Lib.Task.pool to KaRaMeL (assumed type)
Cannot re-check Pulse.Lib.Task.grab_work'' as valid Low* and will not extract it.
Cannot re-check Pulse.Lib.Task.do_work_once as valid Low* and will not extract it.
Fatal error: exception Failure("nth")
```

**Shim needed.** C threads would require hand-written C for `fork_core`, for example over `pthread_create`. They would also require restating `par` without closures, such as a C-level `par(void (*f)(void*), void *env_f, …)` declared as an assumed Pulse `val`. Both are trusted code outside the proof. Neither was written, per the brief.

**Small Pulse surface notes**, found while getting the probe to verify:

- `par` has no callers anywhere in the library.
- Its typeclass arguments need the four slprops passed explicitly.
- A Pulse `fn _ {…}` lambda does not parse inside parentheses.
- A branch whose precondition is `exists* x. r |-> x` does not unify: Pulse turns that `exists*` into an implicit binder. The probe uses concrete `|-> 0UL` preconditions.

## Q2. Atomics

**Answer.** **No.** No module in the pinned toolchain provides compare-and-swap on a 64-bit word. The only CAS is a **U32** one, in `Pulse.Lib.Primitives`, and it **does not extract to a C11 atomic**. Depending on the krml flags, it becomes either non-atomic C that does not link, or an `extern` the user must write by hand.

**Evidence.**

- `Pulse.Lib.Primitives.fsti:47`: `val cas (r:ref U32.t) (u v:U32.t) (#i:erased U32.t) : stt_atomic bool …`.
  - Plus `read_atomic` and `write_atomic` (`:35`, `:40`) and the box variants `cas_box` and friends (`:63`). All are U32 only.
- The docstring, lines 30-33: *"primitive atomic operations that are not meant to be extracted to C (since they are intended to be implemented by handwritten C code.) Thus, please use Karamel option `-library Pulse.Lib.Primitives`"*.
- `Pulse.Lib.Primitives.fst:62`: `let cas r u v #i = Pulse.Lib.Core.as_atomic _ _ (cas_impl r u v #i)`.
  - `cas_impl` is an ordinary read-compare-write.
  - `as_atomic` (`Pulse.Lib.Core.fsti:766`) is an abstract `val` that promotes any `stt` computation to `stt_atomic`. **Atomicity is assumed, not implemented.**
- A toolchain-wide grep for `cas`, `atomic_compare`, `__atomic`, `stdatomic` and `_Atomic` over `.fst`, `.fsti`, `.c`, `.h` and `.ml` finds only `Primitives`, its users (`RWLock`, `CountingSemaphore`, `Par`), and unrelated hits. The krml headers mention neither `as_atomic` nor any atomic builtin.

**Extracted C, without `-library`** (`_extract_cas_nolib/Pulse_Lib_Primitives.c`):

```c
static bool cas_impl(uint32_t *r, uint32_t u, uint32_t v)
{
  uint32_t u_ = *r;            /* plain load      */
  if (u == u_) { *r = v; return true; }   /* plain store: a data race */
  else return false;
}
bool Pulse_Lib_Primitives_cas(uint32_t *r, uint32_t u, uint32_t v)
{
  return Pulse_Lib_Core_as_atomic((void *)0U, (void *)0U, cas_impl(r, u, v));
}
void Pulse_Lib_Primitives_write_atomic(uint32_t *r, uint32_t x)
{
  KRML_MAYBE_UNUSED_VAR(r);
  KRML_MAYBE_UNUSED_VAR(x);
  Pulse_Lib_Core_as_atomic((void *)0U, (void *)0U, (void *)0U);   /* the store is erased */
}
```

This is not atomic. `Pulse_Lib_Core_as_atomic` is defined nowhere, so it would not link. And `write_atomic` has **lost its store entirely**: `ConditionVar.signal` would then never wake `wait`.

**Extracted C, with `-library Pulse.Lib.Primitives`** (`_extract_cas_lib/Pulse_Lib_Primitives.h`):

```c
extern bool Pulse_Lib_Primitives_cas(uint32_t *r, uint32_t u, uint32_t v);
extern bool Pulse_Lib_Primitives_cas_box(uint32_t *r, uint32_t u, uint32_t v);
extern uint32_t Pulse_Lib_Primitives_read_atomic(uint32_t *r);
extern void Pulse_Lib_Primitives_write_atomic(uint32_t *r, uint32_t x);
…
```

The caller is `bool Spike_CasProbe_try_claim(uint32_t *r, uint32_t id) { return Pulse_Lib_Primitives_cas_box(r, 0U, id); }`.

**Shim needed.** To get a CAS that works:

- Hand-written C for every `Pulse_Lib_Primitives_*` symbol, for example with `atomic_compare_exchange_strong` on `_Atomic uint32_t`. Note that the extracted signature takes a plain `uint32_t *`, so the shim has to cast.
- For U64, additionally a new assumed `val cas_u64 … : stt_atomic …` in Pulse, plus its C body. That is new trusted surface; nothing in the toolchain provides it today.

## Q3. Runtime (OCaml 4.14)

**Answer. Not tested in Spike 1; answered by Spike 2 below.** Spike 2's extracted C, with a pthread-based `par_env`, runs inside OCaml 4.14.0 as both bytecode and native.

Originally: The precondition, extracted C for the two-thread CAS program, does not exist (Q1 and Q2). The two C-side tools are in place:

- The `4.14.0` opam switch is present (`ocamlc` and `ocamlopt` 4.14.0, `threads.posix` installed).
- Apple clang 12.0.0 on x86_64 is available.

No C stub was written and nothing was linked: a stub over hand-written threading C would test the shim, not the extracted code.

## Reproducing

From `spike/parallel/`:

```sh
F="../../fstar/bin/fstar.exe $(cat fstar.flags)"
K=../../fstar/karamel/krml
P=../../fstar/lib/fstar/pulse/pulse/lib

# Q1
eval $F Spike.ParProbe.fst
eval $F --codegen krml --extract_module Spike.ParProbe Spike.ParProbe.fst
$K -tmpdir _extract -skip-compilation -skip-linking -warn-error -2-9-15 _output/Spike_ParProbe.krml
eval $F --codegen krml --extract_module Pulse.Lib.Par $P/Pulse.Lib.Par.fst
$K -tmpdir _extract_par -skip-compilation -skip-linking -warn-error -2-9-15 _output/Pulse_Lib_Par.krml
eval $F --codegen krml --extract_module Pulse.Lib.Task $P/Pulse.Lib.Task.fst
$K -tmpdir _extract_task -skip-compilation -skip-linking -warn-error -2-9-15 _output/Pulse_Lib_Task.krml

# Q2
eval $F Spike.CasProbe.fst
eval $F --codegen krml --extract_module Spike.CasProbe Spike.CasProbe.fst
eval $F --codegen krml --extract_module Pulse.Lib.Primitives $P/Pulse.Lib.Primitives.fst
$K -tmpdir _extract_cas_nolib -skip-compilation -skip-linking -warn-error -2-9-15 \
   _output/Spike_CasProbe.krml _output/Pulse_Lib_Primitives.krml
$K -tmpdir _extract_cas_lib   -skip-compilation -skip-linking -warn-error -2-9-15 \
   -library Pulse.Lib.Primitives _output/Spike_CasProbe.krml _output/Pulse_Lib_Primitives.krml
```

Each verification and extraction step above takes seconds.

## What unblocking would take (a decision, not done here)

Every path to the spike as specified adds trusted, hand-written C beneath the proof:

- a `fork`/`join` primitive whose interface has no closures, and
- a U64 CAS, plus the U32 primitives if `ConditionVar` is reused.

The open choice is whether that trusted surface is acceptable for Phase 1. Two alternatives:

- Restate `par` as an assumed `val` over C function pointers plus an environment.
- Keep parallelism entirely on the C/OCaml side, and verify only the per-thread work, with the shared word specified through an assumed atomic interface.

---

# Spike 2: option A, parallel composition over top-level functions plus an environment

The brief:

- Declare an assumed Pulse operation over top-level functions plus an explicit environment, with `Pulse.Lib.Par.par`'s specification.
- Write its C body with `pthread_create` and `pthread_join`.
- Use it so that two threads each fill their own half of one array, with a postcondition that states the whole array.
- Extract, compile, run under ThreadSanitizer, and call it from OCaml 4.14, as bytecode and as native.
- No atomics.

## Outcome: every step passes

| Step | Result |
|---|---|
| Verify `Spike.ParEnv` (the assumed operation) | **yes** |
| Verify `Spike.FillHalves` (the program) | **yes**, no admits; the only trusted item is `par_env` |
| Extract with F* `--codegen krml`, then krml (repo flags) | **yes**, with a typed `extern` prototype for `par_env` |
| Compile with the hand-written `par_env.c` (Apple clang 12, `-Wall -Wextra`) | **yes**, no warnings |
| Run | `ok: 1000001 elements, two threads` |
| ThreadSanitizer, the spike (5 runs) | **no reports**, all `ok`, two distinct threads each time |
| ThreadSanitizer, racy control | **data race reported**, so TSan is live |
| OCaml 4.14.0, bytecode (`ocamlc -custom`) | `ok: OCaml 4.14.0 bytecode, 1000001 elements, two threads` |
| OCaml 4.14.0, native (`ocamlopt`) | `ok: OCaml 4.14.0 native, 1000001 elements, two threads` |
| A second thread really ran (C, TSan, bytecode, native) | checked by the test itself: the two branches record `pthread_self()`, and the test fails unless the ids differ |

One deviation needs flagging. **The TSan builds use Homebrew clang 18.1.8, not the system Apple clang 12.0.0.** Under Apple clang 12 on macOS 15.7.9, *an empty `int main(void){return 0;}`* compiled with `-fsanitize=thread` segfaults (exit 139). That is a broken sanitizer runtime on this OS, unrelated to the spike. The spike's own TSan binary crashed the same way before printing anything. Homebrew clang 18.1.8 runs the same empty program cleanly, so `build_c.sh` uses it for the two TSan builds only (`TSAN_CC`). The plain C build and the OCaml builds use the system compiler. F* and krml remain the pinned `./fstar`.

## The first attempt: a generic declaration does not extract

The first version of `par_env` was generic over the environment types (`#ea #eb: Type0`). It verified, but F* would not extract it:

```
Not extracting Spike.ParEnv.par_env to KaRaMeL (polymorphic assumes are not supported)
```

The call site was still emitted, against an undeclared `Spike_ParEnv_par_env`. It had 12 arguments, 8 of them `(void *)0U` placeholders for erased proof terms. A hand-written C body would have had to match that call with nothing to check it against.

We chose option 1: make `par_env` monomorphic in a concrete environment type, still generic in the (erased) pre- and postconditions.

## The assumed operation (`Spike.ParEnv.fst`)

```fstar
noeq
type half = {
  arr: A.array U64.t;
  lo: SZ.t;
  hi: SZ.t;
  v: U64.t;
}

assume val par_env
  (#preL #postL #preR #postR: half -> slprop)
  (ef eg: half)
  {| is_send (preL ef) |} {| is_send (postL ef) |}
  {| is_send (preR eg) |} {| is_send (postR eg) |}
  (f: (e: half -> stt unit (preL e) (fun _ -> postL e)))
  (g: (e: half -> stt unit (preR e) (fun _ -> postR e)))
  : stt_div unit (preL ef ** preR eg) (fun _ -> postL ef ** postR eg)
```

This is `par`'s specification:

- **Resources:** separate resources in, both postconditions out.
- **Divergence:** `stt_div` overall, as with `par`; the branches are terminating `stt`.
- **Thread-safety:** the same `is_send` obligations.

Each branch is a top-level function applied to an environment, with conditions indexed by that environment.

The environments and instances come before `f` and `g` because Pulse does not resolve typeclass arguments that come last: *"This function is partially applied. Remaining type: {| _: is_send (half_pre el) |} -> …"*.

All the erased arguments disappear in C. krml emits this prototype in `Spike_ParEnv.h`:

```c
typedef struct Spike_ParEnv_half_s
{
  uint64_t *arr;
  size_t lo;
  size_t hi;
  uint64_t v;
}
Spike_ParEnv_half;

extern void
Spike_ParEnv_par_env(
  Spike_ParEnv_half ef,
  Spike_ParEnv_half eg,
  void (*f)(Spike_ParEnv_half x0),
  void (*g)(Spike_ParEnv_half x0)
);
```

## The program (`Spike.FillHalves.fst`)

- `half_pre e = exists* s. pts_to_range e.arr lo hi s`.
- `half_post e = pts_to_range e.arr lo hi (Seq.create (len lo hi) e.v)`.
- Both have `is_send` instances.
- `fill_range` is a `while` loop over `Pulse.Lib.Array.PtsToRange.pts_to_range_upd`. It carries a `decreases` clause, because an undecorated loop is `stt_div` and `par`'s branches must be terminating `stt`.
- `fill_half (e: half)` is the top-level branch.
- The entry point:

```fstar
divergent
fn fill_halves (a: A.array U64.t) (n: SZ.t) (#s: erased (Seq.seq U64.t))
  requires A.pts_to a s ** pure (Seq.length s == SZ.v n)
  ensures A.pts_to a (expected (SZ.v n))
//  expected n = Seq.append (Seq.create (n / 2) 1UL) (Seq.create (n - n / 2) 2UL)
```

It works in four steps:
1. Split with `pts_to_range_split` at `n / 2`.
2. Call `par_env #half_pre #half_post #half_pre #half_post el er fill_half fill_half`.
3. Rejoin with `pts_to_range_join`.
4. Convert back with `pts_to_range_elim`.

The specification-only helpers `len` and `expected` are `noextract`. Before that, `len` leaked into the C as `krml_checked_int_t` arithmetic over `Prims_op_*`, and `expected` was dropped with a krml warning. Now neither reaches C, and krml prints no warnings.

The extracted C (`_extract_fill/Spike_FillHalves.c`) is complete and contains no atomics:

```c
void Spike_FillHalves_fill_range(uint64_t *a, size_t lo, size_t hi, uint64_t v)
{
  size_t i = lo;
  size_t __anf0 = i;
  bool cond = __anf0 < hi;
  while (cond)
  {
    size_t vi = i;
    a[vi] = v;
    i = vi + (size_t)1U;
    size_t __anf0 = i;
    cond = __anf0 < hi;
  }
}

void Spike_FillHalves_fill_half(Spike_ParEnv_half e)
{
  Spike_FillHalves_fill_range(e.arr, e.lo, e.hi, e.v);
}

void Spike_FillHalves_fill_halves(uint64_t *a, size_t n)
{
  size_t mid = n / (size_t)2U;
  Spike_ParEnv_half el = { .arr = a, .lo = (size_t)0U, .hi = mid, .v = 1ULL };
  Spike_ParEnv_half er = { .arr = a, .lo = mid, .hi = n, .v = 2ULL };
  Spike_ParEnv_par_env(el, er, Spike_FillHalves_fill_half, Spike_FillHalves_fill_half);
}
```

## ThreadSanitizer

**The spike** (`_build/test_fill_tsan`, Homebrew clang 18.1.8 `-fsanitize=thread -g -O1`) ran five times. Each run exited 0, produced **no ThreadSanitizer output**, and printed:

```
branch f ran on thread 0x7a0000104000, branch g on thread 0x7ff84f9df180: distinct
ok: 1000001 elements, two threads
```

The run covers both the verified entry point `fill_halves` and the thread probe (described in the next section).

**The control** (`c/tsan_control.c`) deliberately breaks the Pulse precondition by handing both branches the *whole* array. TSan flags it (exit 134):

```
WARNING: ThreadSanitizer: data race (pid=18816)
  Write of size 8 at 0x729000000000 by thread T1:
    #0 Spike_FillHalves_fill_half Spike_FillHalves.c:29 (tsan_control:x86_64+0x100003dc7)
    #1 run par_env.c:7 (tsan_control:x86_64+0x100003cdf)

  Previous write of size 8 at 0x729000000000 by main thread:
    #0 Spike_FillHalves_fill_half Spike_FillHalves.c:29 (tsan_control:x86_64+0x100003dc7)
    #1 Spike_ParEnv_par_env par_env.c:15 (tsan_control:x86_64+0x100003c72)
    #2 main tsan_control.c:14 (tsan_control:x86_64+0x100003b8b)

  Location is heap block of size 8000 at 0x729000000000 allocated by main thread:
    #0 calloc <null>:179490793 (libclang_rt.tsan_osx_dynamic.dylib:x86_64h+0x5c944)
    #1 main tsan_control.c:10 (tsan_control:x86_64+0x100003b03)

  Thread T1 (tid=1118648, running) created by main thread at:
    #0 pthread_create <null>:179490793 (libclang_rt.tsan_osx_dynamic.dylib:x86_64h+0x3310f)
    #1 Spike_ParEnv_par_env par_env.c:14 (tsan_control:x86_64+0x100003c2d)
    #2 main tsan_control.c:14 (tsan_control:x86_64+0x100003b8b)

SUMMARY: ThreadSanitizer: data race Spike_FillHalves.c:29 in Spike_FillHalves_fill_half
```

So TSan does see the two threads `par_env` creates, and the spike's silence is a real negative.

## OCaml 4.14.0

Built by `build_ocaml.sh` with the `4.14.0` opam switch:

- The stub (`ocaml/fill_stub.c`), `par_env.c`, the test probe `thread_probe.c` and the extracted `Spike_FillHalves.c` are compiled with `ocamlc -c`.
- They are linked into `ocaml/main.ml`, both by `ocamlc -custom` (bytecode) and by `ocamlopt` (native).
- The array is a `Bigarray.Array1` of `int64`, whose data lives outside the OCaml heap.

`main.ml` calls the verified entry point `fill_halves` and checks every element. It then clears the array, runs the thread probe, and checks every element again. It exits 1 if any element is wrong or if the probe reports one thread.

```
branch f ran on thread 0x7000003ae000, branch g on thread 0x7ff84f9df180: distinct
ok: OCaml 4.14.0 bytecode, 1000001 elements, two threads
branch f ran on thread 0x70000af8f000, branch g on thread 0x7ff84f9df180: distinct
ok: OCaml 4.14.0 native, 1000001 elements, two threads
```

### How the tests prove a second thread ran

`par_env` falls back to running both branches sequentially if `pthread_create` fails, so a correct array alone does not prove that a second thread ran. The tests check it themselves, with no debugger and no extra tooling, so they can run in CI.

`c/thread_probe.c` calls `Spike_ParEnv_par_env` on the two halves of the array. Its branches are a wrapper, `recording_fill_half`, which:

1. stores `pthread_self()` in a slot chosen by the branch's environment, and
2. runs the extracted, verified `Spike_FillHalves_fill_half`.

After `par_env` returns, the probe compares the two ids with `pthread_equal`, prints both, and returns whether they differ. `test_fill.c` and `main.ml` both fail when they do not.

Three choices to note:

- **Nothing verified or trusted was changed for the test.** `fill_halves` itself cannot be observed this way: its branch function is fixed in the extracted C. So the probe drives `par_env` with the same extracted `fill_half` wrapped in a recorder, and `fill_halves` is still checked separately for its result.
- **No counter in `par_env.c`.** Adding one would have put a test hook in trusted code.
- **The two slots are not raced.** Each branch writes a different one, and the main thread reads them only after `pthread_join`. TSan confirms this.

An earlier version of this check used a `DYLD_INSERT_LIBRARIES` interposer on `pthread_create`. It was macOS-only and outside the test, so it was replaced by the probe and deleted.

What this does and does not show about the OCaml runtime:

- **Shown:** the 4.14 runtime, in both backends, tolerates a C call that creates and joins a pthread. The worker never touches OCaml values or the runtime.
- **Not tested:** worker threads that touch the OCaml heap, releasing the runtime lock (`caml_enter_blocking_section`), or the `threads` library. The real sweep will run on the OCaml heap with the mutator stopped, which needs its own spike.

## Every line of hand-written C

Three groups:

- **Trusted, linked into the product:** `par_env.c`, the body of the assumed `par_env`, 17 lines.
- **Glue between OCaml and the extracted C:** `ocaml/fill_stub.c`, 19 lines.
- **Test-only, not part of any product:** `thread_probe.h`, `thread_probe.c`, `test_fill.c`, `tsan_control.c`.

No hand-written C touches atomics.

### Trusted

`c/par_env.c` (17 lines):

```c
 1  #include <pthread.h>
 2  #include <stdlib.h>
 3  #include "Spike_ParEnv.h"
 4  
 5  typedef struct { void (*f)(Spike_ParEnv_half); Spike_ParEnv_half e; } job;
 6  
 7  static void *run(void *p) { job *j = p; j->f(j->e); return NULL; }
 8  
 9  void Spike_ParEnv_par_env(Spike_ParEnv_half ef, Spike_ParEnv_half eg,
10                            void (*f)(Spike_ParEnv_half), void (*g)(Spike_ParEnv_half))
11  {
12    job j = { f, ef };
13    pthread_t t;
14    if (pthread_create(&t, NULL, run, &j) != 0) { f(ef); g(eg); return; }
15    g(eg);
16    if (pthread_join(t, NULL) != 0) abort();
17  }
```

On success it runs `f(ef)` on a new thread and `g(eg)` on the calling thread, then joins. If `pthread_create` fails it runs `f` then `g` sequentially, which still meets the specification. If `pthread_join` fails it aborts rather than return while `f` may still be running.

### OCaml stub

`spike_thread_probe_fill` exists only for the test.

`ocaml/fill_stub.c` (19 lines):

```c
 1  #include <caml/mlvalues.h>
 2  #include <caml/memory.h>
 3  #include <caml/bigarray.h>
 4  #include "Spike_FillHalves.h"
 5  #include "thread_probe.h"
 6  
 7  value spike_fill_halves(value ba)
 8  {
 9    CAMLparam1(ba);
10    Spike_FillHalves_fill_halves((uint64_t *)Caml_ba_data_val(ba), Caml_ba_array_val(ba)->dim[0]);
11    CAMLreturn(Val_unit);
12  }
13  
14  value spike_thread_probe_fill(value ba)
15  {
16    CAMLparam1(ba);
17    bool distinct = thread_probe_fill((uint64_t *)Caml_ba_data_val(ba), Caml_ba_array_val(ba)->dim[0]);
18    CAMLreturn(Val_bool(distinct));
19  }
```

### Test-only

`c/thread_probe.h` (7 lines):

```c
 1  #include <stdbool.h>
 2  #include <stddef.h>
 3  #include <stdint.h>
 4  
 5  /* Fills the two halves of a through par_env, with branches that record the
 6     thread they ran on.  Prints both, and returns true iff they differ. */
 7  bool thread_probe_fill(uint64_t *a, size_t n);
```

`c/thread_probe.c` (24 lines):

```c
 1  #include <pthread.h>
 2  #include <stdio.h>
 3  #include "Spike_FillHalves.h"
 4  #include "thread_probe.h"
 5  
 6  static pthread_t ran_on[3];
 7  
 8  static void recording_fill_half(Spike_ParEnv_half e)
 9  {
10    ran_on[e.v] = pthread_self();
11    Spike_FillHalves_fill_half(e);
12  }
13  
14  bool thread_probe_fill(uint64_t *a, size_t n)
15  {
16    Spike_ParEnv_half el = { .arr = a, .lo = 0, .hi = n / 2, .v = 1 };
17    Spike_ParEnv_half er = { .arr = a, .lo = n / 2, .hi = n, .v = 2 };
18    Spike_ParEnv_par_env(el, er, recording_fill_half, recording_fill_half);
19    bool distinct = !pthread_equal(ran_on[1], ran_on[2]);
20    printf("branch f ran on thread %p, branch g on thread %p: %s\n",
21           (void *)ran_on[1], (void *)ran_on[2], distinct ? "distinct" : "SAME");
22    fflush(stdout);
23    return distinct;
24  }
```

`c/test_fill.c` (25 lines):

```c
 1  #include <stdio.h>
 2  #include <stdlib.h>
 3  #include "Spike_FillHalves.h"
 4  #include "thread_probe.h"
 5  
 6  static int check(const uint64_t *a, size_t n)
 7  {
 8    for (size_t i = 0; i < n; i++)
 9      if (a[i] != (i < n / 2 ? 1 : 2)) { printf("FAIL at %zu\n", i); return 0; }
10    return 1;
11  }
12  
13  int main(void)
14  {
15    size_t n = 1000001;
16    uint64_t *a = calloc(n, sizeof *a);
17    if (a == NULL) return 2;
18    Spike_FillHalves_fill_halves(a, n);
19    if (!check(a, n)) return 1;
20    for (size_t i = 0; i < n; i++) a[i] = 0;
21    if (!thread_probe_fill(a, n) || !check(a, n)) return 1;
22    printf("ok: %zu elements, two threads\n", n);
23    free(a);
24    return 0;
25  }
```

`c/tsan_control.c` (18 lines):

```c
 1  /* Negative control, not verified: both branches write the WHOLE array, which
 2     the Pulse precondition of par_env forbids.  ThreadSanitizer must flag it. */
 3  #include <stdio.h>
 4  #include <stdlib.h>
 5  #include "Spike_FillHalves.h"
 6  
 7  int main(void)
 8  {
 9    size_t n = 1000;
10    uint64_t *a = calloc(n, sizeof *a);
11    if (a == NULL) return 2;
12    Spike_ParEnv_half e1 = { .arr = a, .lo = 0, .hi = n, .v = 1 };
13    Spike_ParEnv_half e2 = { .arr = a, .lo = 0, .hi = n, .v = 2 };
14    Spike_ParEnv_par_env(e1, e2, Spike_FillHalves_fill_half, Spike_FillHalves_fill_half);
15    printf("control ran\n");
16    free(a);
17    return 0;
18  }
```

The OCaml side is `ocaml/main.ml` (23 lines), not C.

## Reproducing

From `spike/parallel/`:

```sh
F="../../fstar/bin/fstar.exe $(cat fstar.flags)"
for m in Spike.ParEnv Spike.FillHalves; do
  eval $F $m.fst
  eval $F --codegen krml --extract_module $m $m.fst
done
../../fstar/karamel/krml -tmpdir _extract_fill -skip-compilation -skip-linking -warn-error -2-9-15 \
  _output/Spike_ParEnv.krml _output/Spike_FillHalves.krml
./build_c.sh            # plain build, TSan build, TSan control
./_build/test_fill && ./_build/test_fill_tsan   # both check results and two threads
./_build/tsan_control                          # must report a data race
./build_ocaml.sh        # OCaml 4.14.0, bytecode and native
./_build/ocaml/main.byte && ./_build/ocaml/main.native
```

## For Phase 1: one environment type, k-way parallelism by nesting

F* extracts only a monomorphic assumed operation, and each assumed operation brings its own C body. The real parallel sweep should therefore keep the trusted surface to **one** `par_env`:

- **A single environment type for segments.** Use one record that describes a segment of the heap for the sweep, for example `{ heap; lo; hi; ... }`, rather than one environment type per phase or per caller. Every parallel step of the pass takes this type, so one `assume val` and one C body cover the whole pass.
- **k-way parallelism by nesting the binary operation.** `par_env` stays binary. A `k`-way split is a verified, recursive Pulse function on the segment environment: halve the range, then call `par_env` on two branches, each of which recurses on its half. A branch is itself the recursive function, still top-level, still a function of the segment environment. Each level splits the range with `pts_to_range_split`, and rejoins it on return. So k-way parallelism costs no extra trusted code, only proof.

It follows that splitting, joining, and the per-segment sweep are all verified. The only trusted C stays the 17-line `par_env.c` above, reviewed once.

---

# Spike 3: par_env inside a real collection, on the real major heap

The brief:

- Inside the existing collector, at the start of sweep, with the mutator stopped, walk the heap once to pick two segment boundaries on object headers.
- Use `par_env` so two threads each walk their own segment, read-only, counting objects and total whole size.
- Check the two counts add up to the sequential walk.
- The workers call no OCaml runtime function.
- Run in bytecode and native, under ThreadSanitizer, on a few test-suite programs.

"The existing collector" is the repo's verified generational collector (`generational/ocaml-integration`). It is the collector Phase 1 will change, on the heap Phase 1 will walk.

## Outcome: passes in bytecode; native does not exist

| Step | Result |
|---|---|
| Hook between mark and sweep in `collect_with_roots` | **yes**, 4 lines, compiled only with `-DSPIKE_SWEEP_PROBE` |
| Default build unchanged | **yes**: the rebuilt default `ocamlrun` contains no probe symbol, and `make test` passes |
| Sequential walk, split, two-thread walk, counts add up | **yes**, in every one of 111 probed collections across 5 programs |
| Two distinct threads every time | **yes**, checked by the probe; it aborts otherwise |
| Program output unchanged versus the unprobed runtime | **yes**, all 5 programs, with heap addresses masked |
| ThreadSanitizer, whole bytecode runtime instrumented (5 runs × 5 programs) | **no reports** |
| ThreadSanitizer, racy control on the real heap | **data race reported**, so TSan is live there |
| **Native** | **not run: the verified collector has no native integration** (next section) |

## The verified collector has no native integration

**The strategy note assumed the verified collector runs under native code. It does not.** The integration is bytecode only:

- `setup.sh:75` builds `make -C runtime ocamlrun`, commented *"we only need ocamlrun for bytecode"*. The compiler used for the tests is the separate, unchanged OCaml build.
- `patches/runtime_gen.patch` links `libvergc_gen.a` only into `ocamlrun`, `ocamlrund` and `ocamlruni`. No `libasmrun` target links it.
- The patch redirects allocation in `memory.h` (`Alloc_small`, used by C and the bytecode interpreter) and in `interp.c`. Native code emits its own inline allocation against `Caml_state->young_ptr`, and nothing patches that path.
- `verified_gc/OCAML_INTEGRATION.md:949` notes that native frame-table roots are *"not applicable to bytecode"*. The bridge never scans them.
- The repo README describes the integration as *"an OCaml bytecode runtime integration"*.

So a native run of this spike would need a native port of the integration first: inline allocation, frame-table roots, and `libasmrun` linking. That is a project of its own, not a workaround, so it was not attempted. The strategy note itself is not in this repository, so it is not edited here.

## Toolchain

- OCaml **4.14.2**: the tag `generational/ocaml-integration/setup.sh` pins, cloned and built by its `make setup` (4.5 minutes). Spike 2 used the opam `4.14.0` switch. That switch has no verified collector, so it is not used here.
- Plain build: Apple clang 12.0.0, the compiler `make setup` uses.
- TSan build: Homebrew clang 18.1.8, for the reason given in Spike 2 (Apple clang 12's TSan runtime crashes on macOS 15.7.9).
- F* and krml: not re-run. The probe reuses Spike 2's extracted `_extract_fill/Spike_ParEnv.h` and its unchanged trusted `c/par_env.c`.

## Where the hook is

`gen_gc` → `collect_with_roots` (`generational/snapshot/GC_Gen_Impl.c`) runs `mark_loop_bounded` and then `fused_sweep_coalesce`. The probe call goes between the two:

```c
   mark_loop_bounded(heap, st);
+  /* SPIKE (sheera/spike-parallel only, not extracted): see spike/parallel/SPIKE.md, Spike 3. */
+#ifdef SPIKE_SWEEP_PROBE
+  { extern void spike_sweep_probe(uint8_t *base); spike_sweep_probe(heap.data); }
+#endif
   return fused_sweep_coalesce(heap);
```

At that point:

- **Marking is finished and nothing is swept.**
- **The mutator is stopped.** `gen_gc` is called synchronously from the allocation slow path: `caml_alloc` → `verified_allocate_minor` → `do_minor_gc` → `do_full_gc` (see the TSan stack below). The test programs are single-threaded and do not use the `threads` library.

The heap is the real major heap that `alloc_gen.c` allocates. `heap.data` is `NULL` (the bridge's NULL-base convention), so addresses are absolute, and the heap spans `[zero_addr1, heap_size_u640)`. These are the same two globals `fused_sweep_coalesce` uses.

## The probe (`c/sweep_probe.c`, test-only)

1. **One sequential walk on the main thread.** It uses `fused_sweep_coalesce`'s own loop: header at `cur`, `whsize = (hdr >> 10) + 1`, stop when `cur + 8 >= heap_size_u640`. It counts objects and whole words. A second cursor trails it, one object for every two the walk passes, so it ends on the header of object number `objs / 2`.
   - Segment A is `[start, mid)` and segment B is `[mid, stop)`. Both boundaries are object headers.
2. **`par_env` on the two segments.** Spike 2's `half` record is reused as it is: `arr` is the first heap word, `lo..hi` are word indices, and `v` is the result slot. `walk_segment` loads headers, counts, and finally stores `{objs, words, pthread_self()}` into `res[v]`.
   - That is all a worker does. It makes **no OCaml runtime call**, not even a `caml/` macro; its one library call is `pthread_self`.
   - It writes nothing on the heap.
3. **Checks on the main thread, after the join.** `res[0] + res[1]` must equal the sequential counts, for objects and for words, and the two thread ids must differ. Otherwise the probe prints `FAIL` and aborts.

The probe prints one line per collection to stderr, and a summary at exit:

```
sweep-probe #1: 56440 objs = 28220 + 28220, 2000000 words = 86311 + 1913689, split at word 86311 of 2000000, threads distinct
...
sweep-probe: 2 collections checked, all matched, two threads each
```

### The first split was degenerate

The first version split at the first header at or past the **byte** midpoint. Segment B came out empty in every collection: `1974 objs = 1974 + 0, ... split at word 300000 of 300000`.

The cause is the heap's shape after promotion. Live objects are packed at the front, and one free block runs from there to the end of the heap: in `infix_closures`, the first 4183 of 300000 words hold 1974 objects. So no header lies past the midpoint.

The object-count split fixes the spike. **For Phase 1:** balancing the parallel sweep by address range will not work on this heap. It needs a split by object count, or by estimated sweep work.

## Programs

`run_sweep.sh` runs each program on a probe runtime and on the unprobed verified `ocamlrun`, using the `.byte` files that `make test` builds. Collections are counted from one runner pass; the TSan runtime gave the same counts.

| Program | Major heap (words), args | Probed collections | Objects per split (first collection) |
|---|---|---|---|
| `infix_closures` | 300000 (its `make test` size) | 54 | 987 + 987 |
| `no_scan` | 4000000 (its `make test` size) | 22 | 878 + 878 |
| `make_vect_barrier` | 4000000 (its `make test` size) | 2 | 1130 + 1130 |
| `fasta` | 300000, `100000` | 31 | 320 + 321 |
| `count_change` | 2000000, `100` | 2 | 28220 + 28220 |

The fourth correctness test, `nursery_no_scan_interior`, does no major collection, at its `make test` size or at 1000000 words.

**None of the eight benchmarks collects at its smoke-test size.** Their major heaps (8M to 134M words) never reach `do_minor_gc`'s 50%-promoted trigger. So `fasta` and `count_change` were run with smaller heaps. `binarytrees` and `quicksort` could not be used:

- `quicksort` (100000 and 1000000 elements, heaps of 1M to 6M words) did no major collection.
- With any heap small enough to force a major collection, the following abort with `Fatal error: verified gen GC: out of memory (major heap too small)` **on the unprobed runtime as well**:
  - `binarytrees` 10, 12 and 14 (300000, 1M and 3M words);
  - `count_change` 200 (4M and 8M words) and 300 (20M words).

  That is a property of the existing collector, unrelated to this spike, and was not investigated. `binarytrees 10` failing in a 300000-word heap looks worth a separate look.

## ThreadSanitizer

`build_sweep.sh` builds `_build/sweep/ocamlrun_tsan`:

- It copies the `make setup` tree and **rebuilds the bytecode runtime itself** (`libcamlrun.a`, `prims.o`) with `-fsanitize=thread`. 45 of its members reference `__tsan_write8`. So the interpreter's own heap writes are instrumented, not just the GC.
- The extracted collector, `alloc_gen.c`, `par_env.c` and the probe are compiled with TSan as well.

**The spike.** `run_sweep.sh _build/sweep/ocamlrun_tsan` was run five times. Every program exited 0 with unchanged output, and there was no ThreadSanitizer output at all. The plain runtime was run three more times, also clean.

**The control.** With `SPIKE_PROBE_RACE=1`, branch `g`, on the main thread, rewrites (with its own value) the first header of segment A while branch `f` walks it. TSan reports it, exit 134:

```
WARNING: ThreadSanitizer: data race (pid=54618)
  Read of size 8 at 0x000107bfe000 by thread T1:
    #0 walk_segment sweep_probe.c:44
    #1 run par_env.c:7

  Previous write of size 8 at 0x000107bfe000 by main thread:
    #0 walk_segment_racy sweep_probe.c:54
    #1 Spike_ParEnv_par_env par_env.c:15
    #2 spike_sweep_probe sweep_probe.c:83
    #3 collect_with_roots GC_Gen_Impl.c:1543
    #4 gen_gc GC_Gen_Impl.c:363
    #5 do_full_gc alloc_gen.c:509
    #6 do_minor_gc alloc_gen.c:428
    #7 verified_allocate_minor alloc_gen.c:546
    #8 caml_alloc alloc.c:46
    #9 caml_alloc_tuple alloc.c:75
    #10 caml_gc_quick_stat gc_ctrl.c:304
    #11 caml_interprete interp.c:938
    #12 caml_main startup_byt.c:588
    #13 main main.c:37

  Location is heap block of size 2400000 at 0x000107bfe000 allocated by main thread:
    #0 calloc
    #1 ensure_heap alloc_gen.c:115
    ...
  Thread T1 (tid=1243867, running) created by main thread at:
    #0 pthread_create
    #1 Spike_ParEnv_par_env par_env.c:14
    #2 spike_sweep_probe sweep_probe.c:83
    #3 collect_with_roots GC_Gen_Impl.c:1543
    ...
```

The racing address is the first word of the real major heap, the 2400000-byte block (300000 words) that `ensure_heap` allocates. So TSan sees both `par_env` threads touching the OCaml heap from inside a collection, and the spike's silence is a real negative.

## What this does and does not show

- **Shown:** `par_env`, Spike 2's trusted 17 lines unchanged, runs two threads over the live major heap from inside a real verified collection, between mark and sweep, in the 4.14.2 bytecode runtime. The runtime tolerates it, results are exact, and TSan finds no race with the whole runtime instrumented.
- **Not shown:**
  - Native code, for the reason above.
  - A verified worker: the segment walk is test-only C. Phase 1's per-segment sweep would be Pulse code behind the `par_env` interface, as in Spike 2.
  - Workers that **write** the heap, or the sweep's free-list and coalescing state, which crosses segment boundaries.
  - Programs using the `threads` library.
  - Any platform other than macOS 15.7.9 on x86_64.
- **For Phase 1:**
  - The hook point is `collect_with_roots`.
  - Heap addresses are absolute (`heap.data == NULL`), so a segment environment must carry absolute bounds or a base pointer.
  - Split by objects, not bytes (see "The first split was degenerate").

## Every line of hand-written C and script

- **Snapshot edit:** the 4 lines above in `GC_Gen_Impl.c`. They are inert unless `SPIKE_SWEEP_PROBE` is defined.
- **Test-only:**
  - `c/sweep_probe.c` (100 lines): the probe and the race control.
  - `build_sweep.sh`: builds both runtimes, out of tree, under `_build/sweep/`. It never touches the `make setup` tree.
  - `run_sweep.sh`: the runner and its checks.
- **Unchanged:** `c/par_env.c`, `_extract_fill/`, and every other repository file.

## Reproducing

```sh
cd generational/ocaml-integration && make setup && make test   # 4.14.2 + verified GC; builds tests/*.byte
cd ../../spike/parallel
./build_sweep.sh                            # _build/sweep/ocamlrun and ocamlrun_tsan
./run_sweep.sh                              # plain: must end "ok: all programs"
./run_sweep.sh _build/sweep/ocamlrun_tsan   # TSan: same, no reports
cd ../../generational/ocaml-integration/tests
SPIKE_PROBE_RACE=1 MIN_EXPANSION_WORDSIZE=300000 \
  ../../../spike/parallel/_build/sweep/ocamlrun_tsan infix_closures.byte   # must report a data race
```
