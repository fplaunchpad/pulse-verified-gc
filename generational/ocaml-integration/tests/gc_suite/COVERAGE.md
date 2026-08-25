# Coverage notes

Findings from first running this suite against the verified GC
(2026-08-25, commit `b202a9a`). The suite's own README is unchanged; this file
records what running it showed.

## Run it against this project, not stock OCaml

`run_tests.sh` defaults to `ocamlc`/`ocamlopt` from `PATH`. That is a useful
baseline but does not exercise the verified collector. Use `run_verified.sh`,
which points both at the in-tree compilers and pins bytecode executables to
`runtime/ocamlrun` with `-use-runtime`.

Note that `make coldstart` builds only the **bytecode** runtime flavours.
Native needs `make -C runtime allopt`, which is what produces `libasmrun.a`
with `libvergc_gen_native.a` embedded in it. Without that step there is nothing
to link native tests against.

Confirmed both paths really use the verified GC before trusting any result:
the native executables resolve `find_infix_parents`, `minor_collect_full` and
`verified_allocate`; the bytecode header names the in-tree `ocamlrun`, which
links the same objects.

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
collection. Validated by A/B — with resolution disabled it segfaults
(exit 139) in bytecode; with resolution enabled it passes.

## The native asymmetry is unexplained

With resolution disabled, `t11`'s shape reproduces in **bytecode** but not in
**native**, even scaled to 5000 live infix-only closures across 10 major
collections and 691 minor ones. Native produced correct output every time.

What has been ruled out:

- Native does create infix pointers here. `Obj.tag` on the second function
  reports 249 in both modes.
- The verified major collector is active in native. `do_full_gc` in
  `alloc_gen.c` is not behind `#ifdef NATIVE_CODE`, and it is what darkens the
  post-minor roots and runs mark-and-sweep.

So the reason native tolerates the missing resolution is not yet known, and
until it is, **a native pass on any infix test should not be read as evidence
that the infix path works in native.** Bytecode is currently the only mode
where this class of bug is known to be observable.

## One correction to the suite README

The README describes t01 as "the known native failure". Per this repository's
record the infix bug was found in `make coldstart`, which builds the stdlib with
`boot/ocamlc` under `runtime/ocamlrun` — bytecode. Commit `582358c` states it
directly: "This is what broke `make coldstart`." The A/B above agrees: the
failure is observable in bytecode, not native.
