# Phase 0 spike: parallel mark-and-sweep

Branch `sheera/spike-parallel`. No existing GC file was touched.

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

**Answer. Not tested.** The precondition, extracted C for the two-thread CAS program, does not exist (Q1 and Q2). The two C-side tools are in place:

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
