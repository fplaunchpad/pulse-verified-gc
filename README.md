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

## Compiling and running your own `.ml` file

After `make -C generational/ocaml-integration setup`, both compilers exist in the
OCaml tree. From the repository root:

```bash
GC=$PWD/generational/ocaml-integration/ocaml-4.14-verified-gen
```

**Bytecode**

```bash
$GC/ocamlc.opt -nostdlib -I $GC/stdlib \
               -use-runtime $GC/runtime/ocamlrun \
               -o prog.byte prog.ml
./prog.byte
```

**Native**

```bash
$GC/ocamlopt.opt -nostdlib -I $GC/runtime -I $GC/stdlib \
                 -o prog.exe prog.ml
./prog.exe
```

Two flags carry the whole thing, and both fail *silently* if you drop them.

`-use-runtime` pins the bytecode executable to the verified `ocamlrun`. Without
it the header names the compiler's configured runtime — `/usr/local/bin/ocamlrun`
— so on a machine with a stock OCaml installed your test runs on the **stock**
collector and looks fine.

`-I $GC/runtime` **must precede** `-I $GC/stdlib`. The verified collector is not
a separate library: it is archived inside `libasmrun.a`. The tree keeps two
copies of that archive — `runtime/libasmrun.a` is the build output,
`stdlib/libasmrun.a` is a copy refreshed only by `make runtimeopt` — and `-I`
directories are searched in the order given. Put `stdlib` first and you link
whatever was propagated last, which compiles, links, runs, and passes against an
old collector.

**After changing the GC** — any edit to the F\* source, the snapshot, a hand
patch, or a `git checkout` (the snapshot is tracked, the build artifacts are
not, so they survive and go stale):

```bash
make -C generational/ocaml-integration/verified_gc
cd generational/ocaml-integration/ocaml-4.14-verified-gen && make runtime runtimeopt
```

`make runtime runtimeopt` builds the archives *and* propagates them.
`make -C runtime all allopt` builds without propagating; `make coldstart` builds
no native archive at all.

**Checking which collector you linked**

```bash
nm prog.exe | grep -E 'verified_allocate|minor_collect_full'   # native
head -1 prog.byte                                              # bytecode
cmp $GC/runtime/libasmrun.a $GC/stdlib/libasmrun.a             # copies in sync?
```

Finding those symbols proves *a* verified GC is linked, not the current one — a
stale archive contains them too, which is what `cmp` is for.

**Scope.** This runs your *program* on the verified collector, not the compiler:
`ocamlc.opt` and `ocamlopt.opt` are prebuilt binaries with their own vintage
statically linked, unaffected by the rebuild above. To put the current collector
under the compiler itself, rebuild it — `make coldstart` (bytecode stdlib
bootstrap) or `make world.opt` (native, ~900 `ocamlopt` invocations). Those are
also the strongest tests available, since a collector broken enough to matter
cannot finish a bootstrap.

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
