# Verified OCaml Garbage Collector

This repository is a verified generational garbage-collector for OCaml
4.14, specified in [F*](https://fstar-lang.org/) and implemented in
[Pulse](https://fstar-lang.org/). It contains shared OCaml heap/object
infrastructure, a verified major-heap allocator, a bounded-stack mark-and-sweep
major collector, a generational collector with Cheney-style minor collection,
SPOT contract audits, KaRaMeL extraction to C, and an OCaml bytecode runtime
integration.

For the detailed design, proof architecture, public contracts, OCaml bridge
layout, benchmark table, and current verification boundary, see
[`DESIGN_AND_IMPL.md`](DESIGN_AND_IMPL.md).

## Quick local setup

The exact sequence CI runs in [`.github/workflows/verify.yml`](.github/workflows/verify.yml),
guaranteed to work end-to-end. Steps must run in this order

```bash
./setup.sh # setups up F*

fstar/bin/fstar.exe --version # check fstar version
# verify GC
make -j$(nproc) 

# verify SPOT
make -C spot -j$(nproc) 

# extract to C using Karamel
make extract

# generate a snapshot for integrating into OCaml runtime
make -C generational snapshot
# setup ocaml integration (stock ocaml and modified ocaml runtime with verified gc)
make -C generational/ocaml-integration setup

make -C generational/ocaml-integration/tests test # run smoke tests
make -C generational/ocaml-integration/tests benchmark # run benchmarks
```

## Testing against the verified GC

```bash
# Once: clone and build both OCaml trees (stock, installed + verified, patched).
# This already produces everything needed to run your own code: the verified
# runtime/ocamlrun and runtime/libasmrun.a.
make -C generational/ocaml-integration setup

# Run your own code, bytecode and native.
sh ci/run-verified.sh prog.ml
sh ci/run-verified.sh --byte prog.ml
sh ci/run-verified.sh --stock prog.ml     # stock OCaml, for comparison
sh ci/run-verified.sh some/dir            # every t*.ml; diffs against
                                          # expected_output.txt if present

# After changing the F* source, the snapshot, or a hand patch: rebuild the GC
# and the runtimes. `setup` will not do this -- it skips a tree that exists.
sh ci/build-verified-toolchain.sh

# OCaml's own testsuite -- 231 directories, ~3100 test instances, each in a
# bytecode and a native variant. Needs the tree's compilers to EXIST, which
# --full builds (15-40 min); after that a GC change needs only the rebuild
# above, not another --full. See below.
sh ci/build-verified-toolchain.sh --full
sh ci/run-testsuite.sh
sh ci/run-testsuite.sh tests/lib-hashtbl  # one directory
```

These are the same steps as
[`.github/workflows/testsuite.yml`](.github/workflows/testsuite.yml), so a local
result and a CI result mean the same thing.

### How the collector gets swapped in

Simpler than it looks, and worth knowing so results are interpretable.

**Bytecode**: a `.byte` file is portable and contains no collector — the
collector is whichever `ocamlrun` you invoke. So compile with the **stock**
compiler and run with the verified runtime. The very same `.byte` runs on
either, which is why `--stock` costs nothing and gives a free side-by-side.

**Native**: the collector is archived *inside* `libasmrun.a`, so stock
`ocamlopt` is pointed at the verified GC's copy with
`-I .../ocaml-4.14-verified-gen/runtime`. No compiler rebuild needed. Check it
worked with `nm prog.exe | grep verified_allocate` — 3 symbols with the `-I`,
none without.

Same mechanism the benchmarks in `generational/ocaml-integration/tests` use.

### What `world.opt` is really for

Not a prerequisite so much as a test in its own right.

The testsuite needs the tree's compilers to **exist**, but not to be rebuilt
after a GC change. `ocamltest` resolves the runtime as
`<tree>/runtime/ocamlrun` (`ocamltest/ocaml_files.ml:36`) and passes
`-use-runtime` for it (`ocaml_flags.ml:49`), so every bytecode test runs on the
tree's *current* runtime whatever compiled it. Verified here: with compilers
from 11:29 and a runtime rebuilt at 11:42, `tests/lib-hashtbl` runs 6/6.

What a rebuild does change is the collector inside the *compiler processes* —
`ocamlc.opt`/`ocamlopt.opt` are native binaries with the runtime statically
linked, so a stale pair keeps running on an older collector while still
compiling correctly.

The real argument for `--full` is that the bootstrap is itself the broadest
stress test available: it rebuilds the whole toolchain *on* the verified
collector, and one broken enough to matter cannot finish. The infix bug surfaced
exactly that way, with `make coldstart` dying on `camlinternalFormat.ml` — not
from reading the specification.

### What a testsuite result means

The gate is **no new failures**, not zero failures. The verified GC does not
implement statmemprof, weak references or ephemerons, so those tests fail by
design; [`ci/expected-failures.txt`](ci/expected-failures.txt) is the baseline
and `ci/run-testsuite.sh` diffs against it, exactly as CI does. It writes
`testsuite-report.html` and exits nonzero only on a regression.

Single-directory runs skip the baseline comparison and print a raw tally — the
baseline covers the whole suite, so comparing one directory against it would
report every unrelated failure as "now passing".

## Current status

The active development is organized around dependency-scanned builds. The
top-level default verifies the active generational roots; `make generational`
checks the common, mark-and-sweep, generational, and SPOT sources. Excluding
bundled toolchain code and archived attempts, the active F*/Pulse tree contains
223 `.fst`/`.fsti` files and about 104k lines of source.

| Area | Path | Status |
| --- | --- | --- |
| Shared model and Pulse infrastructure | `common/` | OCaml headers, heap words, object layout, field traversal, graph/reachability, and shared Pulse heap/stack predicates. |
| Major collector and allocator | `mark-and-sweep/` | Verified free-list allocator, bounded-stack mark phase, sweep/coalescing, extraction rules, and snapshot C output. |
| Generational collector | `generational/` | Verified minor heap, promotion, forwarding, remembered-slot/root rewriting, Cheney BFS, and composed `gen_gc`. |
| SPOT contract audits | `spot/` | Concrete three-object scenario calls the real `minor_collect_full` and `gen_gc` entry points and proves client-visible consequences. |
| OCaml integration | `generational/ocaml-integration/` | Extracted verified GC bridge for OCaml 4.14 bytecode, smoke tests, timing benchmarks, GC/RSS stats CSVs, heap calibration, and refreshed results. |

The latest default-heap verified-GC benchmark run reports a geometric-mean
slowdown of **1.45x** versus stock OCaml 4.14; a calibrated-heap pass using
stock-RSS-sized verified heaps reports **1.35x**. The full per-benchmark numbers
and discussion are in [`DESIGN_AND_IMPL.md`](DESIGN_AND_IMPL.md); the refreshed
CSV data lives under `generational/ocaml-integration/tests/results*/`.

## Build and verification

First run ./setup.sh to install a compatible F* binary release.

The repository uses a unified top-level `Makefile` with `fstar.exe --dep full`
for incremental dependency scheduling and parallel verification.

The top-level `Makefile` defaults to `FSTAR_HOME=$(pwd)/fstar`, so first ensure
that checkout contains a built `fstar/bin/fstar.exe` and `fstar/karamel/krml`.

```bash
make -j$(nproc)       # verify the active dependency roots
make generational     # verify common + mark-and-sweep + generational + SPOT
make extract          # verify and extract mark-and-sweep + generational C
make clean
```

Useful focused targets:

```bash
make common
make mark-and-sweep

cd spot && make -j    # local SPOT verification with its own .depend file
```

## Extraction, OCaml integration, and benchmarks

The generational collector is extracted through KaRaMeL and connected to OCaml's
bytecode runtime by `generational/ocaml-integration/verified_gc/alloc_gen.c`.
The current full-GC bridge uses a separate mutable `roots_for_gc` buffer and a
separate initially empty gray stack; verified `gen_gc` performs minor
collection, verified root darkening, and then major mark/sweep.

```bash
make extract

cd generational
make snapshot

cd ocaml-integration/verified_gc
make

cd ..
make setup
make test

cd tests
make benchmark
make bench-stats
make bench-min-heaps
```

See [`DESIGN_AND_IMPL.md`](DESIGN_AND_IMPL.md) for the exact `gen_gc` contract,
root/gray-stack protocol, verified boundary, and benchmark interpretation.

## Repository tour

| Path | Role |
| --- | --- |
| `common/` | Shared F*/Pulse definitions for OCaml-compatible heaps, objects, fields, graph construction, reachability, and low-level ownership. |
| `mark-and-sweep/` | Major-heap allocator and bounded-stack stop-the-world collector. |
| `generational/` | Minor heap, copying collection, promotion, forwarding maps, remembered slots, combined generational GC, extraction, and OCaml integration. |
| `spot/` | Small proof-oriented tests that audit whether the exported collector contracts are usable from concrete client scenarios. |
| `generational/snapshot/` and `mark-and-sweep/snapshot/` | Checked-in extracted C snapshots. |
| `research/docs/` and older planning files | Historical notes; prefer `DESIGN_AND_IMPL.md` for the current architecture. |

## References

A starting point for this GC was the verified mark-and-sweep collector described
in the following paper:


- Sheera Shamsu, Dipesh Kafle, Dhruv Maroo, Kartik Nagar, Karthikeyan Bhargavan & KC Sivaramakrishnan,
  [*A Mechanically Verified Garbage Collector for OCaml*](https://link.springer.com/article/10.1007/s10817-025-09721-0),
  J. Autom. Reason. **69**, 7 (2025).
- Original implementation: <https://github.com/fplaunchpad/verified_ocaml_gc/>
