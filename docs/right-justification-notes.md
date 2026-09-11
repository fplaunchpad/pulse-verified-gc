# Right-justified allocation — working notes

Stock OCaml's `nf_allocate_block` (`runtime/freelist.c:113`) puts the allocated
object at the **high end** of the free block and leaves the remainder at the
block's own address.  This branch makes the verified allocator do the same,
and in doing so makes it size-exact — the fix that retires hand patch 17.

    leftover = 0    exact fit: header at hd, block detached
    leftover = 1    the spare word cannot carry a link, so it becomes an empty
                    block (header only, wosize 0, blue, never linked) at hd,
                    and the object starts at hd + 8; block detached
    leftover >= 2   remainder at hd shrinks to leftover - 1 and stays a blue,
                    linked cell; object header at hd + leftover * 8

In every case the allocated block declares **exactly** `requested_wz`.

## Why this fixes the ast-invariants SIGSEGV

The old allocator, at `leftover = 1`, handed over the whole block and wrote
the header with `block_wz` rather than `wz`.  The object then declares a field
it does not have.  `Array.length` reads `Wosize_val` straight from the header
(`runtime/array.c:39`) and the bounds check uses the same inflated size, so the
safety net is defeated by the same lie.  `Hashtbl` indexes with
`land (Array.length h.data - 1)` (`stdlib/hashtbl.ml:355,504`), valid only for
power-of-two lengths; a `2^n` bucket array declared as `2^n + 1` yields index
`2^n`, which reads the phantom word.  `Is_block(0)` is true, so the reader
follows it to NULL.  `ocamlcommon` is full of `Hashtbl`s, which is why
`ast-invariants` is where it surfaced.

Measured, same machine, same test binary, same environment, only the snapshot
differing:

| snapshot | `ast-invariants` |
|---|---|
| before | **exit 139** (SIGSEGV, dumped core) |
| after  | **exit 0**, output byte-identical to stock |

## What right-justification gives back

Three things fell out that the low-end design did not have.

**The remainder keeps its address and its link.**  At `leftover >= 2` the free
list is bit-identical across a split — same cell, same address, same link word
at `hd + 8`.  `fl_descending` holds trivially and the free-list preservation
proofs stop having to relocate a cell.

**The only object allocation creates is the allocated block.**  The remainder
was already there; it only shrinks.  `alloc_from_block_only_new_is_alloc` says
so, and it collapsed the hardest case of two 200-line closures in
`PromoteUpdate.BlueAlloc` — for a *blue* `src`, "not in the old heap" is now a
contradiction, because the one new object is white.

**`obj_out` is interior to the free block before allocation**, hence not an
object of the pre-allocation heap at all, hence on no chain.
`chain_avoids_non_object` turns most of `alloc_search_obj_not_in_chain_part1`
into two lines.

## What it costs

**`alloc_spec_new_objects_blue_part1` had to be weakened**, and this is a real
consequence of the geometry rather than a proof convenience.  Under the low-end
design the new object was the blue remainder; now it is the **white allocated
block**.  The theorem gains `x <> r.obj_out`, which makes it vacuous — the
honest statement.  Its three consumers already case-split on `obj_out`.

**The header frame needs the object off the free list.**  Right-justification
splits `obj_out` from the block it came out of, and the remainder's header is
rewritten too, so "not `obj_out`" no longer covers every header the allocation
touches.  `alloc_spec_read_header_other_part1` now wants
`chain_avoids g fp excl heap_words`.  Four consumers had to supply it; three of
them were deriving non-blueness rather than assuming it, so they needed a new
`alloc_spec_preserves_blue_part1` ("a blue object other than `obj_out` stays
blue") to rule out "was a free-list cell, came out gray or black".

**One shape had to be guarded.**  `alloc_search` rewrites the predecessor's
link and then runs the block writes on the result — the order the free-list
proofs need, because at `leftover = 1` the block becomes wosize 0 and
`fl_valid` of the intermediate heap is flatly false.  But the block writes
re-read the block size from the heap the link write just produced, and those
disagree in exactly one case: the predecessor's *object* address being this
block's *header* word, i.e. a wosize-0 predecessor.  `fl_valid` excludes it;
`alloc_search`, being total, does not.  Adding `prev_fp <> hd` to the arm's
condition sends that shape down the existing not-a-usable-predecessor path.

## Rules of thumb, paid for

**Nested opaque applications are catastrophic.**  The reorder initially left
two `alloc_from_block` applications with one nested in the other's argument.
`GC.Spec.Allocator.fst` went 913s -> 49.7s once `alloc_replacement_fp` — a
transparent mirror of `snd (alloc_from_block ...)`, bridged by
`alloc_replacement_fp_eq` — replaced the inner one.

**A transparent definition inside a recursive one is nearly as bad.**  An
`alloc_block_writes` carrying the geometry instead of re-reading it looked like
the right fix for the degenerate shape above.  Transparent, it put two nested
`write_word`s into every unfolding of `alloc_search`: Core went 4s -> 304s.

**Duplicating an arm's body doubles every unfolding.**  Writing the
`prev_fp <> hd` guard as a nested `if` inside the arm cost
`GC.Spec.Allocator.fst` 22s -> 610s, with knock-on timeouts in Part1 and Core.
Folded into the arm's condition instead, the body stays the same size: 13.7s.

**A stale term is not a flake, and `--retry` will hide the difference.**
`alloc_from_block_objects_facts_part1` began failing without `--retry`, and I
called it pre-existing on the strength of one retry-enabled run.  It was not:
measured against the branch point, base passes 3/3 and HEAD failed 3/3,
deterministically.  The cause was mine -- the exact-fit arm still built
`make_header (uint_to_t block_wz)` while right-justification had changed
`alloc_from_block` to write `make_header (uint_to_t wz)`.  Equal values,
different terms, so the header write never matched; no rlimit could have
fixed it (150 and 400 were both tried).  Naming the term the spec actually
writes took it to 16.5s -- faster than base.  Four more sites carried the
same stale term and were absorbing the cost silently; they are aligned too.

The lesson is about method, not F*: `--retry` is there for genuine Z3
flakiness, and it will happily mask a deterministic regression as one.  A
claim of "pre-existing" is worth an A/B against the branch point before it
is made.

**Trivial goals fail in large contexts.**  `block_wz == wz` in an exact-fit
arm, `d > 0` under `if d = 0`, two aligned addresses being a word apart —
all linear arithmetic, all timing out at rlimit 400 inside these proofs.  The
fix is never more rlimit; it is a one-line private lemma discharged where the
context is empty (`aligned_distinct`, `add_zero_offset`,
`block_prev_separated`).

**Elapsed time is not a failure signal.**  Two long runs were nearly killed on
suspicion and one 28-minute result actually was.  Error position tells you
whether you are stuck; the clock does not.  Also: `pkill -f fstar.exe` matches
the killing shell's own command line — use `pkill -x`.

## Verification

    gmake -j16                    0 errors
    gmake -C spot -j16            0 errors
    gmake -C generational extract && snapshot
    tests: === All smoke tests passed ===
    ast-invariants                exit 0 (was 139)

Per-module, measured individually with `--retry` off:

| module | |
|---|---|
| `GC.Spec.Allocator.fst` | 13.7s |
| `GC.Spec.Allocator.Lemmas.Chain.fst` | 14.7s |
| `GC.Spec.Allocator.Lemmas.Part1.fst` | 16.5s |
| `GC.Spec.Allocator.Lemmas.Core.fst` | 4.1s |
| `GC.Spec.Allocator.Lemmas.Part2.fst` | 75.9s |
| `GC.Impl.Allocator.fst` | 39.1s |
| `GC.Gen.AllocProps.fst` | 42.5s |
| `GC.Gen.Cheney.Dense.fst` | 26.1s |
| `GC.Gen.CheneyPreservation.fst` | 36.8s |
| `GC.Gen.CheneyPreservation.Frame.fst` | 10.9s |
| `GC.Gen.CheneyPreservation.Forwarding.fst` | 53.4s |
| `GC.Gen.CheneyPreservation.NonBlueOrigin.fst` | 19.0s |
| `GC.Gen.PromoteUpdate.BlueAlloc.fst` | 23.0s |
| `GC.Gen.PromoteUpdate.BlueProm.fst` | 28.5s |

0 admits.


## Verification cost, base vs HEAD

Measured per module against the branch point `8bd4559`, each side with its
own cold-built cache, `--retry 3` (the build default), and the same eager-QI
flags the Makefile applies.  Both sides were measured under similar
concurrent load except where noted.

| module | base | HEAD | |
|---|---|---|---|
| `GC.Spec.Allocator` | 338.9s | **9.8s** | 0.03x |
| `GC.Gen.PromoteUpdate.BlueAlloc` | 53.2s | 23.0s | 0.43x |
| `GC.Gen.CheneyPreservation.NonBlueOrigin` | 10.1s | 5.4s | 0.53x |
| `GC.Gen.Cheney.Dense` | 33.5s | 21.3s | 0.64x |
| `GC.Spec.Allocator.Lemmas.Core` | 2.3s | 1.6s | 0.70x |
| `GC.Spec.Allocator.Lemmas.Part2` | 96.8s | 76.8s | 0.79x |
| `GC.Gen.CheneyPreservation.Fields` | 10.4s | 8.3s | 0.80x |
| `GC.Gen.PromoteUpdate.BlueProm` | 8.4s | 6.9s | 0.82x |
| `GC.Gen.Promote` | 9.8s | 8.3s | 0.85x |
| `GC.Gen.CheneyPreservation.Forwarding` | 59.0s | 51.2s | 0.87x |
| `GC.Impl.Allocator` | 50.4s | 44.6s | 0.88x |
| `GC.Spec.Allocator.Lemmas.Part1` | 19.7s | 18.9s | 0.96x |
| `GC.Gen.Cheney` | 304.4s | 307.5s | 1.01x |
| `GC.Gen.CheneyPreservation` | 33.3s | 34.2s | 1.03x |
| `GC.Gen.CheneyPreservation.Frame` | 7.2s | 7.7s | 1.07x |
| `GC.Gen.AllocProps` | 20.4s | 53.8s | **2.64x** |

Roughly 1058s -> 679s across the set.  `GC.Spec.Allocator` carries most of
it: at 188 lines and 338.9s it was the worst cost-per-line in the
repository, and the transparent `alloc_replacement_fp` mirror takes it to
9.8s.  `Promote`, `Fields` and `Cheney` are untouched by this branch and
got faster from the spec change alone.

Two entries needed explaining rather than accepting.

**`GC.Gen.AllocProps`, 2.64x.**  Attributed by deletion: with the 191-line
blue section removed the module is 24.6s, so the new
`alloc_search_preserves_blue` -- a fresh recursive induction over
`alloc_search`, the expensive shape in this codebase -- accounts for ~29s
of the ~33s, and the three rewritten arms for ~4s.  It is deterministic
without `--retry` (51.7s, 52.3s on repeat), which is what distinguishes new
work from the Part1 defect.

**`GC.Gen.Cheney`, apparently 1.22x.**  An artifact: that pair was measured
with both sweeps running concurrently.  Serialized on an idle machine it is
304.4s vs 307.5s.  Worth recording because it is the failure mode of this
kind of comparison -- a 300s module is where contention shows up first.

## Still open

- `GC.Spec.Sweep.sweep_object` mishandles wosize 0 three ways (blue but not a
  cell; the incoming free pointer is dropped; a header is followed as a link).
  Unreachable — nothing consumes `snd (sweep ...)`; the shipped pipeline is
  `fused_sweep_coalesce` — but it should be fixed or documented as reference
  semantics only.
- `linkable_heap` / `fl_complete` still say "every object" and "every blue
  object"; a wosize-0 fragment falsifies both.  They are assumed, never
  established, and `fl_exact` has no consumers, so nothing breaks today.
- Coupling with `origin/sheera/coalesce-exact`, whose walk invariant
  `run_words > 0 ==> run_words >= 2` exists to rule out the wosize-0 flush.
