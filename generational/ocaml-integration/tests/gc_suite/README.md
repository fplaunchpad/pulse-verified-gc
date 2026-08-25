# Test Plan for the Verified GC

Repository: `FStarLang/pulse-verified-gc`.

## Why

The infix gap was found by compiling `camlinternalFormat.ml`, not by
reading the specification. Running the collector on real workloads finds
coverage gaps. Reading finds internal inconsistencies. The first is what has
been catching real problems.

Bytecode integration passes. Native integration is where the gap appeared.
So the tests should be run both ways and the difference recorded.

## How to use

Each test is a small standalone OCaml file. Build and run each one against
the runtime linked with the verified GC.

```
sh run_tests.sh          # bytecode and native
sh run_tests.sh byte     # bytecode only
sh run_tests.sh native   # native only
```

All ten tests compile and pass under stock OCaml 4.14.1. Their expected
output is recorded in `expected_output.txt`. Every value is deterministic.

So the runner reports three distinct outcomes.

- `COMPILE FAIL` means the toolchain, not the collector.
- `FAIL (exit n)` means a crash or an assertion.
- `OUTPUT DIFFERS` means the program ran but produced wrong values. That
  indicates heap corruption, which is more serious than a crash.

For a failure, note which heap feature the test targets. Then check whether
the specification permits that feature at all. That is how the infix gap was
diagnosed.

## The tests

### t01_infix.ml

Mutually recursive closures produce infix objects. A field pointing at an
infix object is what `well_formed_heap` currently forbids.

This is the known native failure, reduced to a small case. Keep it as the
regression test once the fix lands.

### t02_noscan.ml

Strings, `Bytes` and float arrays carry a tag at or above `no_scan_tag`.
Their contents are never traced.

The test writes byte patterns that resemble heap addresses into the
`Bytes` values. If the collector traced them it would follow garbage.

### t03_large.ml

Objects above `max_young_wosize` skip the minor heap. The test allocates at
one word either side of that threshold, and well above it.

### t04_promotion.ml

Two phases. First, every tenth object stays live, so each minor collection
has survivors to copy. Second, none survive, so each collection has none.

The all-dead phase matters. Earlier benchmark work found the verified GC
had many minor collections with a full minor heap and zero survivors, which
stock OCaml did not.

### t05_writebarrier.ml

The C bridge uses `caml_ref_table`, populated by `caml_modify`. The
specification instead scans the whole major heap for minor references.

Those agree only if the write barrier fires on every store. The bridge has
to register both heaps with OCaml for that to happen. See the comments at
`alloc_gen.c` lines 193 and 203.

So the code can miss a root the proof would find. This test drives stores
through four paths: `Array.set` into a major array, a mutable int array
field, a mutable string field, and a mutable field holding a record.

### t06_stale_ref.ml

A major object is pointed at a fresh minor object, then the slot is
overwritten before any collection runs. The ref table still holds the first
entry, now pointing at something unreachable.

The specification cannot exhibit this, since it rescans rather than
recording. So this tests the code beyond what the proof covers.

### t07_fragmentation.ml

Allocate many major blocks, drop alternate ones, then request blocks larger
than any single hole. That forces adjacent free blocks to be merged.

This is the path the free list liveness work is about. If a free block were
ever stranded, sustained runs of this shape would show it as growing memory
use.

The test uses allocation churn rather than `Gc.compact`. The verified GC
does not implement compaction. Searching
`generational/ocaml-integration/verified_gc/*.c` for `compact` returns
nothing.

No test in this suite depends on the `Gc` module.

### t08_deep.ml

A tree of about 260,000 nodes and a list of 400,000 elements. Both force
many pending objects during marking.

The bounded mark variant has a fixed stack. This exercises the overflow
path.

### t09_small_sizes.ml

A free block needs one word for its header and one for the next pointer. So
a one-word block is the boundary for free list linking.

The allocator refuses to split when the remainder would be under two words.
That is what prevents zero-size blocks. This test works that boundary hard.

### t10_mixed.ml

All the above features together over a long run. Failures here that do not
appear in the isolated tests point at interactions.

## Features not covered

The collector does not support custom blocks, lazy values, or ephemerons.
So no tests for those.

Forwarding pointers exist in the generational collector, but are modelled as
a separate map rather than stored in the object. The infix case is handled
there explicitly, in `cheney_forward_one`.

## Suggested additions

Native compilation of `camlinternalFormat.ml` as a standing test, since that
is what exposed the infix gap.

The full `make coldstart`, as the broadest single check.

The OCaml standard library test suite, run separately in bytecode and
native, with the difference recorded.
