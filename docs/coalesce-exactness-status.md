# Coalesce free-list exactness: current status

Branch `sheera/coalesce-exact`, based on `gc_gen_impl_spec_tightening`.
All work is in `mark-and-sweep/spec/GC.Spec.Coalesce.fst`, appended after
the existing content.

## What this proves

Upstream proved sweep exactness in `GC.Spec.FreeList` and
`GC.Spec.FreeList.Sweep` (commit `de32deb`): after sweeping, the free list
holds exactly the blue blocks. This work is the same claim for the
coalescing pass.

```fstar
val coalesce_establishes_fl_exact (g: heap) (fp: U64.t)
  : Lemma (requires post_sweep_strong g /\ linkable_heap g /\ fl_exact g fp)
          (ensures (let (g', fp') = coalesce g in fl_exact g' fp'))
```

Built on the upstream definitions: `on_fl`, `reachable_on_fl`, `fl_sound`,
`fl_complete`, `fl_exact`, `linkable_heap`.

## Why coalesce differs from sweep

Sweep never removes objects, links immediately, and extends an existing
list. So exactness is a straightforward preservation property.

Coalesce merges runs of adjacent blue blocks, so absorbed blocks stop being
objects and one merged block replaces them. It defers linking: a run is
accumulated in `first_blue` and `run_words` and written only when a white
object ends it, so mid-run there are blue objects on neither list. And it
builds a new list from `0UL` rather than extending the old one.

## Structure

The walk lemma is split into four, because a single lemma was too large to
be stable under Z3 4.15.3.

- `coalesce_empty_case` — standalone, does not recurse
- `coalesce_aux_fl_exact` — dispatcher, mirrors `coalesce_aux`'s three-way
  split
- `coalesce_blue_case`
- `coalesce_white_case`

The last three form a mutual recursion group with a lexicographic measure:
`%[Seq.length objs; 1]` for the dispatcher and `%[Seq.length objs; 0]` for
the cases. Without this the dispatcher's call at the same `objs` does not
decrease.

Each case lemma splits further on `run_words = 0`, so `new_first` is a
concrete term rather than an `if`. That removed several failures at once.

## The walk invariant

Ten clauses, shared by all four lemmas. The bound throughout is
`if run_words > 0 then hd_address first_blue else start`, the `sync`
quantity the file already uses elsewhere.

1. `walk_pre g0 g start objs all_objs first_blue run_words`
2. `linkable_heap g`
3. `linkable_heap g0` — `wosize` is read from the frozen heap
4. `fl_sound g fp` — full soundness holds throughout, since merging changes
   no colours
5. `run_words > 0 ==> run_words >= 2` — rules out the wosize-0 flush, which
   writes a header without linking it
6. `run_words > 0 ==> Seq.mem first_blue (objects zero_addr g)`
7. objects of `g0` at or above `start` are objects of `g`
8. objects of `g` not in `objs` lie below `start`
9. chain cells lie below the bound
10. blue objects below the bound are on the chain

## Status

Proven: `coalesce_empty_case`, `coalesce_blue_case`, and the
`run_words = 0` half of `coalesce_white_case`.

Open: `coalesce_white_case`, pending-run branch. Three obligations fail at
the recursive call, corresponding to clauses 7, 8 and 9 at the new walk
position:

- clause 7: objects of `g0` above `next` must be objects of `g_flush`
- clause 8: objects of `g_flush` not in the tail must lie below `next`
- clause 9: chain cells of the new list must lie below `next`

Clause 9 is being addressed by strengthening `flush_step_fl_exact`'s
conclusion with a position bound. Clause 7 needs `flush_objects_above`.
Clause 8 should follow from the existing `span` helper once the step is
made explicit.

## Admitted helpers

Eight, all `admit ()`. **The theorem currently rests entirely on these**, so
a green build means the case analysis is consistent, not that anything is
proved.

- `flush_merged_in_walk` — the merged block is an object of the flushed heap
- `flush_preserves_chain` — the chain is unchanged when cells lie below the
  run
- `flush_preserves_reachable` — the existential wrapper for the above
- `flush_preserves_prefix_membership` — an object below the run survives
- `flush_objects_reflect` — an object of the flushed heap other than the
  merged block is an object of the original, and lies outside the run
- `flush_preserves_linkable` — flushing preserves `linkable_heap`
- `flush_objects_above` — an object above the run survives the flush
- the position-bound conjunct of `flush_step_fl_exact`

`flush_preserves_prefix_membership` is the one to attack first. Its
analogue was proved on an earlier branch as `flush_prefix_from`: an
induction over the object walk from `zero_addr`, recursing on
`Seq.length (objects s g)` rather than on the distance to the run boundary.
Recursing on the walk avoids needing a no-straddle hypothesis, because the
bound at each step follows from the target being above the current
position.

## Build notes

Use `./setup.sh` at the repository root. It pins F* nightly-2026-08-15 with
Z3 4.15.3. A system F* will produce spurious proof failures.

Use `gmake`, not `make`. The Makefile uses `private` on a target-specific
variable, which needs GNU Make 3.82 or later; macOS ships 3.81 and the
error ("multiple target patterns") does not indicate the cause.

The Makefile is the authority. `pulsegc.fst.config.json` needs
`--cache_dir _cache` and `--z3version 4.15.3` for the editor to resolve
modules, and a `(set-option :timeout 300000)` to bound queries the way the
Makefile does. Without the timeout a non-converging query can hang the
editor indefinitely.

## Traps worth knowing

**Position arguments must be `nat`, not `hp_addr`,** when the run can end at
the heap boundary. `flush_step_fl_exact` and `flush_merged_in_walk` both
had to change for this.

**Guarded hypotheses do not survive the induction.** Clauses first written
as `Seq.length objs = 0 ==> ...` or `run_words > 0 ==> ...` had to become
unguarded, because the recursive call needs them when the guard is false.
The `sync` form handles this: the bound switches rather than the clause
disappearing.

**`hd_address obj == start` is never automatic.** It also connects
`wosize_of_object obj g0` with `getWosize (read_word g0 start)`, without
which the run geometry cannot be checked.

**Case implications do not combine.** Asserting a fact for `run_words = 0`
and for `run_words > 0` separately does not give the unconditional form.
Splitting the branch on `run_words` at the top is better.

**`assert_norm` does not work on `heap_size`.** It is a `val` whose
refinement gives `heap_size < pow2 57`; a plain `assert` picks that up.

**`pow2 57 / 8 == pow2 54` needs its own lemma.** `assert_norm` proves it in
isolation but fails inside a large query. Hence `pow2_57_div_8`.

**Order of asserts matters.** Coercion bounds such as
`U64.v new_first < heap_size` must come before any assert that coerces to
`obj_addr`.

**`--split_queries always` no longer exists** in the current nightly. With
many hypotheses a failure now prints the whole context and no isolated goal.
Workaround: assert each conjunct separately before a call.

## Method notes

Read the upstream sweep proof before writing. `GC.Spec.FreeList.Sweep.fst`
gives the shape: split on colour, split on head, transport, prepend.

Check a lemma is not vacuous: replace the body with `()` and the `ensures`
with `False`. If that typechecks the hypotheses are contradictory. Leaving
`admit ()` in the body makes the test meaningless.

Probe a branch with `assert False` before proving it. Two cases here turned
out vacuous that way.

State a lemma with `admit ()` and check it composes into its caller before
proving it.

When a large lemma becomes unstable, split it per case rather than raising
the rlimit.
