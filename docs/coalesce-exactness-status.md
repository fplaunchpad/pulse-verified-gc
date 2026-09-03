# Coalesce free-list exactness: current status

Branch `sheera/coalesce-exact`, based on `gc_gen_impl_spec_tightening`.
All work is in `mark-and-sweep/spec/GC.Spec.Coalesce.fst`, appended after
the existing content.

## What this proves

Upstream proved sweep exactness in `GC.Spec.FreeList` and
`GC.Spec.FreeList.Sweep`: after sweeping, the free list holds exactly the
blue blocks. This is the same claim for the coalescing pass.

```fstar
val coalesce_establishes_fl_exact (g: heap) (fp: U64.t)
  : Lemma (requires post_sweep_strong g /\ linkable_heap g /\ fl_exact g fp)
          (ensures (let (g', fp') = coalesce g in fl_exact g' fp'))
```

Built on the upstream definitions `on_fl`, `reachable_on_fl`, `fl_sound`,
`fl_complete`, `fl_exact` and `linkable_heap`.

## Status

The walk induction is complete. All four cases proven, no admits inside the
case lemmas themselves, no assumes anywhere in the file.

Four helpers remain admitted, so the theorem rests on those.

## Why coalesce differs from sweep

Sweep never removes objects, links immediately, and extends an existing
list. Exactness is a straightforward preservation property.

Coalesce merges runs of adjacent blue blocks, so absorbed blocks stop being
objects and one merged block replaces them. It defers linking: a run is
accumulated in `first_blue` and `run_words` and written only when a white
object ends it, so mid-run there are blue objects on neither list. And it
builds a new list from `0UL` rather than extending the old one.

## Structure

Split into four lemmas, because a single one was not stable under Z3 4.15.3.

- `coalesce_empty_case` — standalone, does not recurse
- `coalesce_aux_fl_exact` — dispatcher, mirrors `coalesce_aux`'s three-way
  split
- `coalesce_blue_case`
- `coalesce_white_case`

The last three form a mutual recursion group with a lexicographic measure:
`%[Seq.length objs; 1]` for the dispatcher, `%[Seq.length objs; 0]` for the
cases. Without this the dispatcher's call at the same `objs` does not
decrease.

Each case splits further on `run_words = 0`, so `new_first` is a concrete
term rather than an `if`. That removed several failures at once.

## The walk invariant

Ten clauses, shared by all four lemmas. The bound throughout is
`if run_words > 0 then hd_address first_blue else start`, the `sync`
quantity the file already uses elsewhere.

1. `walk_pre g0 g start objs all_objs first_blue run_words`
2. `linkable_heap g`
3. `linkable_heap g0` — `wosize` is read from the frozen heap
4. `fl_sound g fp` — full soundness holds throughout, since merging changes
   no colours
5. `run_words > 0 ==> run_words >= 2` — rules out the wosize-0 flush
6. `run_words > 0 ==> Seq.mem first_blue (objects zero_addr g)`
7. objects of `g0` at or above `start` are objects of `g`
8. objects of `g` not in `objs` lie below `start`
9. chain cells lie below the bound
10. blue objects below the bound are on the chain

## The four admitted helpers

All say some form of "the flush only touches the run".

- `flush_merged_in_walk` — the merged block is an object of the flushed
  walk. Its inner induction `flush_walk_reaches` is proven; what is missing
  is a no-straddle hypothesis, that no object below the run spans the run's
  start. True, because the run begins at an object boundary, but not
  derivable from what the invariant carries. Carrying it as an invariant
  clause was tried and reverted: after a flush it is false for addresses
  inside the merged block, which are no longer object starts.
- `flush_objects_reflect` — an object of the flushed walk other than the
  merged block is an object of the original, and lies outside the run.
- `flush_above_from` — an object above the run survives the flush.
- `flush_preserves_linkable` — the flush preserves `linkable_heap`.

The last three all need the same fact: a decomposition of the flushed object
walk into the prefix below the run, the merged block, and the suffix above
it. One lemma giving that would likely close all three.

## Proven along the way

- `flush_prefix_from` and `flush_preserves_prefix_membership` — an object
  below the run survives the flush. An induction over the object walk,
  recursing on `Seq.length (objects s g)`.
- `flush_walk_reaches` — the walk from any position reaches the merged
  block, given no-straddle.
- `flush_preserves_chain` and `flush_preserves_reachable` — the free-list
  chain is unchanged when every cell lies below the run. Mirrors
  `on_fl_write_outside` in `GC.Spec.FreeList`.
- `flush_step_fl_exact` — soundness, bounded completeness and a position
  bound for one flush. Extracted so the empty case and the blue
  tail-exhausted case share it.
- `coalesce_aux_empty`, `coalesce_aux_blue_step`, `coalesce_aux_white_step`
  — pair-level unfolding lemmas. The existing `coalesce_heap_*` lemmas only
  cover the heap component, not the free pointer.
- `flush_blue_snd_is_fb`, `pow2_57_div_8`.

## Related upstream work worth knowing

`GC.Spec.FreeList.Descending` proves the descending property and derives the
allocator's entry conditions `fl_valid` and `fl_chain_terminates` from it.
`GC.Spec.Coalesce.Descending` establishes it for the coalescer's output, via
`coalesce_fl_entry`. So the termination half is done, and an earlier attempt
here at an address-ordering property was redundant.

`run_geometry` and `run_floor` in `GC.Spec.Coalesce.Descending` are named
abstractions for the run geometry and the `sync` bound that this proof still
writes out inline. Worth adopting.

`coalesce_aux_head_in_walk` and `flush_blue_head_in_walk` in
`GC.Spec.Coalesce` prove the free-list head is a walk object. The second
gives membership in `objects (hd_address first_blue)`, not in
`objects zero_addr`, so it does not directly replace
`flush_merged_in_walk`, but it is the same argument one step in.

## Two gaps in the surrounding spec

Neither is caused by this work; both were found while doing it.

`linkable_heap` is required by `sweep_preserves_fl_exact` but appears
nowhere in `GC.Spec.Correctness` or `GC.Impl`, and `well_formed_heap` does
not imply it — machine-checked, see the negative tests in `de32deb`. So the
spec permits a zero-size object. `sweep_object` skips the link write when
`ws = 0` but still returns the object as the new free pointer, so the head
is unlinked and every block already on the list becomes unreachable. And
`fl_next` reads the word at the object's own address, which for a zero-size
object is the next object's header, so the allocator would follow a header
as a link.

`fl_exact` and `sweep_preserves_fl_exact` are not referenced from
`GC.Spec.Correctness.fst` or anything under `impl/`, so the result is proven
but not yet consumed. The four pillars of `full_gc_correctness` — heap
integrity, reachability equals blackness, successor preservation, colour
reset — say nothing about the free list.

## Build notes

Use `./setup.sh` at the repository root. It pins F* nightly-2026-08-15 with
Z3 4.15.3. A system F* produces spurious proof failures.

Use `gmake`, not `make`. The Makefile uses `private` on a target-specific
variable, which needs GNU Make 3.82 or later; macOS ships 3.81 and the
error ("multiple target patterns") does not indicate the cause.

The Makefile is the authority. `pulsegc.fst.config.json` needs
`--cache_dir _cache` and `--z3version 4.15.3` for the editor to resolve
modules, and a `(set-option :timeout 300000)` to bound queries the way the
Makefile does. Without it a non-converging query hangs the editor
indefinitely. Adding `--retry 3` matches the Makefile but hides
instability, so a green editor then means less.

## Traps worth knowing

**Position arguments must be `nat`, not `hp_addr`,** when the run can end at
the heap boundary. `flush_step_fl_exact` and `flush_merged_in_walk` both had
to change for this.

**Guarded hypotheses do not survive the induction.** Clauses first written
as `Seq.length objs = 0 ==> ...` or `run_words > 0 ==> ...` had to become
unguarded, because the recursive call needs them when the guard is false.
The `sync` form handles this: the bound switches rather than the clause
disappearing.

**A whole-heap quantifier over aligned addresses is not the same as one over
walk positions.** The no-straddle clause was written the first way and is
false after a flush, because addresses inside the merged block are no longer
object starts and their `getWosize` reads a field word.

**`hd_address obj == start` is never automatic.** It also connects
`wosize_of_object obj g0` with `getWosize (read_word g0 start)`, without
which the run geometry cannot be checked.

**Case implications do not combine.** Asserting a fact for `run_words = 0`
and for `run_words > 0` separately does not give the unconditional form.
Splitting the branch on `run_words` at the top is better.

**`assert_norm` does not work on `heap_size`.** It is a `val` whose
refinement gives `heap_size < pow2 57`; a plain `assert` picks that up.

**`pow2 57 / 8 == pow2 54` needs its own lemma.** `assert_norm` proves it in
isolation but fails inside a large query.

**Order of asserts matters.** Coercion bounds such as
`U64.v new_first < heap_size` must come before any assert that coerces to
`obj_addr`.

**`--split_queries always` no longer exists** in the current nightly. With
many hypotheses a failure prints the whole context and no isolated goal.
Workaround: assert each conjunct separately before a call.

## Method notes

Read the upstream proof of the analogous property before writing.
`GC.Spec.FreeList.Sweep.fst` gives the shape: split on colour, split on
head, transport, prepend. Doing this earlier would have saved most of the
effort here, and would have found `Coalesce.Descending` before an
address-ordering property was attempted independently.

Check a lemma is not vacuous: replace the body with `()` and the `ensures`
with `False`. If that typechecks the hypotheses are contradictory. Leaving
`admit ()` in the body makes the test meaningless.

Probe a branch with `assert False` before proving it. Several cases here
turned out vacuous that way.

State a lemma with `admit ()` and check it composes into its caller before
proving it.

When a large lemma becomes unstable, split it per case rather than raising
the rlimit.
