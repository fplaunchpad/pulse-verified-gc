# Issue #19 regression tests

Two tests for one defect: when a free block is exactly **one word longer** than
the request, the pre-fix allocator hands the whole block over and writes the
header with the *block's* wosize instead of the requested one, so the object
declares a field it does not own.

Both **fail on `main` today**, on purpose. They are wired into
`.github/workflows/testsuite.yml` as `continue-on-error` so `main` stays green
while the bug is measured rather than merely described. When the
right-justification fix lands, delete those two lines and they become hard
gates.

| test | what it drives | run it |
| --- | --- | --- |
| `generational/snapshot/alloc_exact_test.c` | the extracted allocator, directly | `make -C generational/snapshot alloc-exact-test` |
| `ci/promotion-exactness/promotion_exactness.ml` | the promotion path, end to end | `sh ci/run-promotion-test.sh` |

## Why two

The **unit** test presents the tight fit itself: a heap whose free list holds
one blue cell of wosize `wz + 1`, then a request for `wz`. It needs no OCaml
and finishes in under a second, and it asserts the contract directly — the
allocated object declares exactly what was asked for, and the heap still tiles
exactly.

The **end-to-end** test exists because the unit test cannot show that the
defect reaches a running program. It has to go through **promotion**: on the
direct major path `caml_alloc_shr_aux` overwrites the header as soon as
`verified_allocate` returns, so the lie never lands. The minor→major copy does
not — it rebuilds the header from what the allocator wrote
(`wz_read = getWosize(major_hdr)`), so the promoted object carries the inflated
size, and `Array.length` reads it.

Two things had to be arranged to make the allocator take that branch at all,
and both are easy to get wrong:

- **The free list must be out of tail.** Coalesce walks upward making each
  flushed block the new head, so the head is the highest-address free block —
  the unallocated tail — and first fit serves every request from it with a
  large leftover, never touching a fragment. Hence the fill phase.
- **`Gc.full_major ()` does not drive this collector.** `caml_gc_full_major`
  calls stock `caml_finish_major_cycle`. The verified sweep is reachable from
  the promotion threshold, a failed major allocation, or the
  `caml_trigger_verified_gc` primitive, which is what the test calls. Without
  it the victims are never swept, no fragments exist, and the run looks like a
  pass.

## Why not `tests/ast-invariants`

It detects the same defect, and it is how the bug was found — but only
sometimes, because it needs the phantom field to be *followed and faulted on*,
which depends on the platform:

| | pre-fix allocator |
| --- | --- |
| Fedora 44 / gcc 16 / glibc 2.43 | fails **130/130** |
| `ubuntu-latest` / gcc 13 / glibc 2.39 | passes **15/15** |

Both measured, with the unit test failing in the same CI job that
`ast-invariants` passed. An inflated length is the defect itself; a segfault is
one of its possible symptoms.
