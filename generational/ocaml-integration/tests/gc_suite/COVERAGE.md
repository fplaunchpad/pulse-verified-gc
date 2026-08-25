# Coverage notes

Findings from first running this suite against the verified GC
(2026-08-25, commit `b202a9a`). The suite's own README is unchanged; this file
records what running it showed.

## Run it against this project, not stock OCaml

`run_tests.sh` defaults to `ocamlc`/`ocamlopt` from `PATH`. That is a useful
baseline but does not exercise the verified collector. Use `run_verified.sh`,
which points both at the in-tree compilers and pins bytecode executables to
`runtime/ocamlrun` with `-use-runtime`.

Two prerequisites, and the second one cost a full round of wrong results.

`make coldstart` builds only the **bytecode** runtime flavours. Native needs the
`allopt` side, which produces `libasmrun.a` with `libvergc_gen_native.a`
embedded in it.

**But building in `runtime/` is not enough.** `ocamlopt` links
`stdlib/libasmrun.a`, not `runtime/libasmrun.a` — the tree keeps a second copy,
placed there by the `runtime`/`runtimeopt` Makefile targets
(`Makefile:822-829`). Build only in `runtime/` and native tests link whatever
older collector is sitting in `stdlib/`, silently. The correct incantation is:

```
make -C ../../verified_gc
cd ../../ocaml-4.14-verified-gen && make runtime runtimeopt
```

`run_verified.sh` now `cmp`s the two copies and refuses to run if they differ,
because this failure is invisible in the output: the tests link, run, and pass.

Checking that *a* verified GC is linked is not sufficient either — `nm` on a
native executable resolving `find_infix_parents`, `minor_collect_full` and
`verified_allocate` was true of the stale library too. The identity of the
library is what has to be checked, not its provenance.

## Result: 22/22 pass, but t01_infix does not cover infix

All ten supplied tests pass in both modes. The A/B, however, shows the suite
does not detect the bug it was written for. With `resolve_object` in the
generated C neutered to `return obj` — i.e. hand patch 14 removed, the exact
defect that broke `make coldstart` — **the suite still passes 20/20.**

`t01_infix` cannot detect it, for two independent reasons:

1. **It triggers no collection at all.** Measured with `Gc.quick_stat`:
   `minor_collections=0, major_collections=0`. 200 closure pairs plus
   2000 x 50-word arrays is about 100k words, comfortably inside the 256k-word
   nursery. The collector never runs, so nothing in it is under test. (The
   counters are wired: a 40M-word churn reports 153 minor and 2 major.)
2. **It keeps both functions.** `make_pair` returns `(even, odd, n)`. `even` is
   the block's own start address, so the `Closure_tag` block stays reachable
   through a normal pointer and is darkened correctly whether or not infix
   resolution works. The bug needs a block reachable *only* through an infix
   pointer.

`t11_infix_only.ml` fixes both: only the second function escapes, the group
captures a variable so it must be heap-allocated, and the churn forces a major
collection. Validated by A/B/A on the file itself — with resolution disabled it segfaults in
both bytecode and native; with resolution enabled, before and after, it passes.

## Both modes reproduce; an earlier claim of a native asymmetry was a build error

With resolution disabled, `t11_infix_only` segfaults in **both** bytecode and
native, and the ten supplied tests still pass 20/20 in both:

| arm | supplied t01-t10 | t11_infix_only |
|---|---|---|
| resolution enabled | 20/20 pass | bytecode pass, native pass |
| `resolve_object` -> `return obj` | 20/20 pass | **bytecode SIGSEGV, native SIGSEGV** |

An earlier version of this file reported that native did not reproduce and
called it unexplained. That was wrong, and the cause was the stale
`stdlib/libasmrun.a` described above: native was linking a collector built
before the change, so the disabled arm never reached it. There is no asymmetry
between the two modes here.

## One note on the suite README

The README describes t01 as "the known native failure". Per this repository's
record the infix bug was found in `make coldstart`, which builds the stdlib with
`boot/ocamlc` under `runtime/ocamlrun` — bytecode. Commit `582358c` says so
directly: "This is what broke `make coldstart`."

That is a statement about where it was *discovered*, not about which modes are
affected. The A/B above shows both modes are affected equally.

## Also worth fixing in t11

`t11_infix_only` captures `n` so the recursive group must be heap-allocated. A
group with no free variables can be emitted as a static closure, which never
involves the collector at all — worth remembering when writing further infix
tests, since such a test would pass unconditionally and look like coverage.
