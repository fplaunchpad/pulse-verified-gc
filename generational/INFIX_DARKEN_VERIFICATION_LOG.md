# Retiring hand patch 14 into verified source — working log

Branch `akhil/infix`. Goal: make the major mark phase normalise an infix pointer to
its enclosing closure *in the verified source*, so the generated C carries the
resolution and `patches/snapshot/0001-infix-handling.patch` can drop patch 14's hunk.
Nothing here is committed, by request.

Running record; appended to as each step lands. Plan of record:
`~/.claude/plans/imperative-launching-ocean.md`. Predecessor effort (same method,
patch 16): `generational/NOSCAN_VERIFICATION_LOG.md`.

---

## 1. The bug, and the plan's diagnosis

`check_and_darken_bounded` darkens the header at `v - 8` for a field value `v`. When
`v` is an infix pointer — into the middle of a closure, at a fake `Infix_tag` (249)
header — `v - 8` is that inner fake header, not the enclosing closure's own. The
closure is never darkened; if it is reachable only through infix pointers the sweep
frees it while live. Measured: 219 live infix pointers at the failing collection, one
full GC freed 53 still-referenced objects, and the program then jumped to a NULL code
pointer. `GC.Impl.MarkBounded` is bundled for both collectors, so `mark-and-sweep/`
carries it too.

The formal statement of the bug is `GC.Spec.Mark.pointer_field_resolve_identity`
(`mark-and-sweep/spec/GC.Spec.Mark.fsti:636`, proved at `.fst:4012`): resolution is
the identity on pointer-field targets. It is cited at `GC.Impl.MarkBounded.fst:975`
and `GC.Impl.Mark.fst:170` precisely to justify darkening `v - 8`. It rests on
`GC.Spec.Fields.wf_resolve_identity`, whose whole proof is
`wf_objects_non_infix g x; resolve_non_infix x g` — i.e. on the chain part2 (field
targets are in `objects`) + part4 (members of `objects` are never infix).

## 2. Step 1 does not work: weakening part 2 makes `field_write_preserves_wf` false

This is the one place where the plan's diagnosis is wrong, so it is recorded in full.

### What was tried

The plan's step 1 is to weaken `well_formed_heap_part2`
(`common/spec/GC.Spec.Fields.fst:717`) from

```
  ... exists_field_pointing_to_unchecked g src wz dst ==> Seq.mem dst (objects zero_addr g)
```

to

```
  ... ==> Seq.mem (GC.Spec.Object.resolve_object dst g) (objects zero_addr g)
```

Two edits towards that were already in the working tree when this session started
(`well_formed_heap_part2` itself, and the split of `wf_field_target_in_objects` into a
resolved and a non-infix form). They were not committed, and the repository's HEAD
advanced to `0deb730` mid-session, so they now exist only as a saved diff at
`/home/akhiltulluri/.claude/jobs/83b8072a/tmp/fields-part2-weakening-attempt.diff`
(217 lines, including the further repairs described below). Nothing was lost.

The cascade was then followed as far as it goes. Each of these repairs *worked*, and
they are recorded because they will be needed again if the model question below is
resolved in favour of weakening part 2. (Line numbers in this subsection are those of
the *attempt*, not of the reverted file. In the tree as it now stands:
`well_formed_heap_part2` is at `:716`, `wf_resolve_identity` `:842`,
`wf_field_target_in_objects` `:856`, `wf_field_target_resolves_into_objects` `:872`,
`field_pointer_target_in_objects` `:883`,
`field_pointer_target_resolves_into_objects` `:899`,
`points_to_target_in_objects` `:913`, `points_to_target_resolves_into_objects` `:921`,
`well_formed_heap_part2_from_field_closure` `:937`,
`write_word_field_pointing_self_implies` `:1725`, and `field_write_preserves_wf`
declared at `:1862` and defined at `:1872`.)

- `field_pointer_target_in_objects` (`:882`) and `points_to_target_in_objects`
  (`:911`) each split into a resolved form (unconditional, straight from the new
  part 2) and the old raw form, the latter gaining `~(is_infix dst g)` in its
  `requires`. This follows the convention already set for
  `wf_field_target_in_objects`: keep an existing name attached to its existing
  meaning, and point callers that want the resolved form at a new name.
- `well_formed_heap_part2_from_field_closure` (`:925`) gained
  `well_formed_heap_part4 g` in its `requires`. Its `field_closure` hypothesis
  supplies the *raw* conclusion, and transporting that across `resolve_object`
  needs exactly part 4. All three of its callers
  (`GC.Gen.PromoteUpdate.Field.fst:416`, `GC.Gen.CheneyPreservation.fst:1714`,
  `spot/GC.SPOT.ConcreteMajor.fst:492`) already prove part 4 for the same heap, so
  this is cheap; `CheneyPreservation.fst:1731` already calls
  `cheney_promote_preserves_wfh_part4` immediately before.
- `write_word_field_pointing_self_implies` (`:1725`, private) moved to the resolved
  conclusion. Its modified-field branch has `v == dst` and `Seq.mem dst objs` from the
  precondition, so one added `wf_resolve_identity g dst` closes it; its
  unmodified-field branch and its recursion need nothing. With that, and with the
  above, **`GC.Spec.Fields` reached 1 failing fragment**.

### The failure

```
* Error 19 at common/spec/GC.Spec.Fields.fst(1917,6-1952,9):
  - See also common/spec/GC.Spec.Fields.fst(1916,13-1916,47)
Verified module: GC.Spec.Fields
```

`1916` is the `ensures` of `aux2`, the part-2 obligation inside
`field_write_preserves_wf` (`common/spec/GC.Spec.Fields.fst:1872`, declared at
`:1862`). Restating `aux2`'s conclusion in the resolved form —
`Seq.mem (resolve_object dst g') (objects zero_addr g')`, where
`g' = write_word g addr v` — leaves the same fragment failing. That is the whole
obstacle: the old conclusion `Seq.mem dst (objects zero_addr g')` does not mention
`g'` at all, so the proof never had to transport it across the write. The resolved
conclusion does mention `g'`, and `resolve_object dst g'` reads *dst's own header*,
which for an infix target lives inside another object's body — exactly where field
writes land.

### Why it is false, not hard

Concretely. Let `g` contain two enumerated objects: a closure `A` with `wosize 4`, and
an object `S`.

- `A`'s field 1 (at address `A + 8`) holds a fake infix header: tag 249, wosize field
  2. So `is_infix (A + 16) g` holds and
  `parent_closure_addr_nat (A+16) g = (A+16) - 2*8 = A`.
- `S`'s field 0 holds the infix pointer `A + 16`.

All four conjuncts hold: part 1 and part 4 are about `A` and `S` only; part 3
(`infix_wf`) is satisfied because the parent `A` is an enumerated closure; and the
weakened part 2 is satisfied because `resolve_object (A+16) g == A`, which is in
`objects`.

Now apply `field_write_preserves_wf g A (A+8) 0UL` — a write of `0UL` into `A`'s
field 1, which is inside `A`'s body, so the address precondition holds, and `0UL` is
not `is_pointer_field`, so the value precondition
`is_pointer_field v ==> Seq.mem v (objects zero_addr g)` holds vacuously. In `g'` the
word at `A + 8` is `0`, so `is_infix (A+16) g'` is false, so
`resolve_object (A+16) g' == A+16`, which is not in `objects` (the enumeration steps
from `A` straight to `A + 5*8`). `S` still points to `A+16`. Weakened part 2 fails for
`g'`. So the lemma's conclusion `well_formed_heap g'` is false while its hypotheses
hold.

This is not an artefact of the particular formulation. Any conjunct of
`well_formed_heap` that certifies the *contents* of an infix header is falsifiable by
a write to that word, because an infix header is by construction a word inside another
object's body, and `field_write_preserves_wf` permits writes to any body word. Two
alternatives were worked through and rejected for this reason:

- Restating part 2's conclusion as "dst is an object start, or dst is interior to an
  enumerated object" — heap-dependent only on *members'* headers, which object
  separation protects, so it *is* preserved by body writes with no side condition, and
  it is true of real heaps. But it does not give mark what mark needs. Mark computes
  `dst - offset*8` from the word at `dst - 8`; to know that lands on the enclosing
  object, the offset has to be trustworthy, and that claim is again a claim about a
  clobberable word. Knowing only that `dst` is interior to *some* closure leaves the
  implementation darkening an arbitrary bounds-checked address, which is a soundness
  failure, not merely an incompleteness.
- Moving the certification into part 3 (`infix_wf`) instead of part 2, per the plan's
  step 2. Same outcome: `field_write_preserves_infix_wf`
  (`common/spec/GC.Spec.Fields.fst:1805`, private) breaks instead of `aux2`.

### The side condition, and why the sweeper cannot supply it

The needed hypothesis is minimal and easy to name: `~(is_infix (f_address addr) g)`,
i.e. the word being overwritten is not currently an infix header. It is exactly
sufficient — the only `dst` whose resolution can change is `dst = addr + 8`, since
`hd_address dst == addr` iff `dst == addr + 8`; and for that `dst`, if it is not infix
in `g` then part 2 gives `Seq.mem dst objs`, whereupon `aux4` (already in the proof,
`:1888`) shows `hd_address dst <> addr` by object separation, a contradiction. So the
case is vacuous under the side condition.

It is also correct modelling: OCaml never writes over a live infix header.

But it is not dischargeable at the three call sites, all of which thread the free
list by writing field 0 of a block, so that the affected word is the block's field 1:

- `mark-and-sweep/spec/GC.Spec.Sweep.fst:145` — `field_write_preserves_wf g obj obj fp`
  inside `sweep_object_preserves_wf`. `obj` is white and about to be freed; its field 1
  is arbitrary old payload, which may well have low byte `0xf9`.
- `mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.Core.fst:146` — the same shape on the
  free-list predecessor.
- `mark-and-sweep/impl/GC.Impl.Sweep.Lemmas.fst:501` — `sweep_white_write_preserves`.

Nor does reachability help. Part 2 quantifies over *all* `src` in `objects`,
including white garbage; a garbage cycle in which one dead object holds an infix
pointer into another dead closure is a real configuration, and the sweeper frees them
one at a time in address order. So there is no "nothing points into this block"
invariant to appeal to, even in principle, without first restricting part 2 to live
sources — which cannot be done, because `well_formed_heap` is also required before
marking, when every object is white.

Discharging the side condition therefore means a new invariant in the mark-and-sweep
sweeper, threaded through `sweep_object_preserves_wf` (19 call sites across
`GC.Spec.Sweep.fst`, `GC.Spec.SweepCoalesce.fst` and `GC.Spec.Correctness.fst`) and
its loop invariant. That is a change about the allocator, of roughly the size the plan
assigns to the `no_scan_invariant` deletion, and it is not about patch 14.

### What was left in the tree

Per "if something is false rather than hard, stop and report", step 1 was **reverted**
and steps 2 and 3 were not attempted. `common/spec/GC.Spec.Fields.fst` keeps part 2 in
its original raw-target form, and gains:

- a comment at `:700` recording that part 2 is known over-strong, that it is the formal
  statement of patch 14's bug, and that the weakening was attempted and reverted, with
  a pointer to this section;
- three resolved-form companion lemmas, `wf_field_target_resolves_into_objects`
  (`:872`), `field_pointer_target_resolves_into_objects` (`:899`) and
  `points_to_target_resolves_into_objects` (`:921`). Under the present part 2 each is
  strictly weaker than its raw sibling and each is proved in two lines
  (`<raw lemma>; wf_resolve_identity g dst`). They exist because they are the form the
  mark implementation actually needs, and the only form that would survive a weakening
  of part 2: with them in place, a future step 1 changes their *proofs* and no caller.

`GC.Spec.Fields` verifies, 0 failed fragments, no flag change (it builds under the bare
`common/spec/%` rule, `Makefile:134` — no `--split_queries`, no rlimit bump).

The consequence for the rest of the work: `pointer_field_resolve_identity` stays
**true**, so it is not deleted. What changes instead is that nothing *relies* on it:
the bounded spec and the implementation both resolve, so the two citations at
`GC.Impl.MarkBounded.fst:975` and `GC.Impl.Mark.fst:170` go away. The generated C
carries patch 14's resolution either way; the honest caveat, recorded here rather than
papered over, is that under the current part 2 that resolution is verified as a no-op.

---

## Progress

### Step 5 — a functional postcondition for the executable resolve

`mark-and-sweep/impl/GC.Impl.Closure.fst` / `.fsti`. This is the step the plan
identified as newly possible after `02d1743`, and it went through unchanged.

New ghost definition in the `.fsti` (so the `.fst` must not repeat it — F* rejects a
`let` in both with "Duplicate top-level names", which is how the first attempt failed):

```
let parent_closure_of_infix_spec
      (s: heap_state) (infix_addr: hp_addr{U64.v infix_addr + U64.v mword < heap_size})
  : GTot (option hp_addr)
  = let x = SpecHeap.f_address infix_addr in
    let pn = SpecObject.parent_closure_addr_nat x s in
    if pn >= U64.v mword && pn < heap_size && pn % U64.v mword = 0
    then Some (SpecHeap.hd_address (U64.uint_to_t pn))
    else None
```

Three signatures gained postconditions, and all three gained
`{U64.v _ + U64.v mword < heap_size}` on their address parameter. The refinement is on
the *parameter type* rather than in `requires`, deliberately: a `pure` clause in
`requires` does not scope over `ensures`, so `SpecHeap.f_address infix_addr` would not
typecheck in the postcondition otherwise. A refinement is erased at extraction, so this
costs nothing in the C.

- `is_infix_object`: `b == SpecObject.is_infix (SpecHeap.f_address h_addr) 's`.
  Proof: `getTag_eq`, `hd_f_roundtrip`, `tag_of_object_spec`, `is_infix_spec`. The two
  `infix_tag` constants are both transparent `249UL`
  (`GC.Impl.Object.fst:68`, `GC.Spec.Object.fsti:43`), so no reveal is needed.
- `parent_closure_of_infix_opt`:
  `parent_opt == parent_closure_of_infix_spec 's infix_addr`. The four defensive `None`
  branches line up one-for-one with the three-conjunct guard in the ghost definition —
  `f_addr < offset_bytes` covers `pn < 0`, then `< mword`, `>= heap_size`,
  `% mword <> 0`. Proof needs `getWosize_eq`, `f_address_spec`, `hd_f_roundtrip`,
  `wosize_of_object_spec`, `parent_closure_addr_nat_spec`, and on the `Some` branch
  `hd_address_spec` plus `U64.v_inj` to identify the runtime `hd_address`
  (`U64.sub _ mword`, `GC.Impl.Heap.fst:416`) with the abstract `SpecHeap.hd_address`.
- `parent_closure_of_infix`: the `Some`/`None` collapse of the above.
- `resolve_object`:
  `resolved == SpecHeap.hd_address (SpecObject.resolve_object (SpecHeap.f_address obj) 's)`.

One new spec lemma was needed. `GC.Spec.Object` exposed `resolve_non_infix`
(requires `~is_infix`) and `resolve_infix_spec` (requires `is_infix` *and* a valid
parent), but nothing for "infix with an invalid recorded offset", where the ghost
`resolve_object` is defensive and returns its input. That case is reachable in the
executable function — it is exactly what its `None` branches produce — so
`common/spec/GC.Spec.Object.fsti` gained

```
val resolve_infix_invalid : (addr: obj_addr) -> (g: heap) ->
  Lemma (requires is_infix addr g /\
                  ~(let p = parent_closure_addr_nat addr g in
                    p >= 8 /\ p < heap_size /\ p % 8 == 0))
        (ensures resolve_object addr g == addr)
```

proved by `()` in `GC.Spec.Object.fst`. A private bridge
`resolve_object_infix_agrees` in `GC.Impl.Closure.fst` then discharges the infix branch
in both arms (`resolve_infix_spec` for `Some`, `resolve_infix_invalid` for `None`).

Results: `GC.Spec.Object` interface and implementation 0 failed;
`GC.Impl.Closure` interface and implementation 0 failed. No flag changes (Closure
builds under the `mark-and-sweep/impl/%` rule, `Makefile:155`:
`--split_queries always --z3refresh`).

### Steps 4 and 6 — the bounded spec and the implementation both resolve

`mark-and-sweep/impl/GC.Impl.MarkBounded.fsti:45`:

```
-     darken_if_white_bounded_spec g st (U64.sub v mword) cap
+     darken_if_white_bounded_spec g st
+       (SpecHeap.hd_address (SpecObject.resolve_object (v <: obj_addr) g)) cap
```

The coercion `v <: obj_addr` is discharged by the guard already on the branch
(`U64.v v >= U64.v zero_addr + U64.v mword && U64.v v < heap_size &&
U64.v v % U64.v mword = 0`), which is exactly `obj_addr`'s refinement plus more.

`GC.Impl.MarkBounded.fst`, in `check_and_darken_bounded` (`:1081`), the edit that puts
patch 14 into the generated C:

```
    f_address_eq target_hdr;
    assert (pure (SpecHeap.f_address target_hdr == (v <: obj_addr)));
    let resolved = Closure.resolve_object heap target_hdr;
    darken_if_white_bounded heap st resolved cap;
```

plus `module Closure = GC.Impl.Closure`. This is what makes `GC.Impl.Closure` reachable
from `ROOT_MODULES` — the plan's side benefit — since `GC.Impl.MarkBoundedRootLemmas`
is a root and depends on `GC.Impl.MarkBounded`. `GC.Impl.Closure` is already listed in
`generational/Makefile:131`'s `ALL_KRML_MODS` and is caught by the
`GC.Gen.Impl+...=GC.Gen.Impl.*,GC.Impl.*[rename=GC_Gen_Impl]` bundle
(`generational/Makefile:179`), so no extraction-configuration change is needed.

### The fallout from steps 4 and 6, and how each piece was repaired

The blast radius of the `check_and_darken_bounded_spec` change is exactly two files —
`GC.Impl.MarkBounded.fst` and `GC.Impl.MarkBoundedRootLemmas.fst` — because the bounded
*implementation* spec lives in `GC.Impl.MarkBounded.fsti` and nothing else mentions it.
(`GC.Gen.Impl` and `mark-and-sweep/impl/GC.Impl` use `darken_roots_bounded_spec` and its
preservation lemmas, whose statements did not change.)

**One new spec lemma, replacing the identity appeal.**
`GC.Spec.Mark.check_and_darken_field_preserves_wf` (`.fsti:618`) is stated over the raw
target `v`, so it no longer applies. Rather than bridge with
`pointer_field_resolve_identity`, `GC.Spec.Mark` gained
`check_and_darken_resolved_field_preserves_wf`, the same statement for
`resolve_object (v <: obj_addr) g`. Its proof uses
`GC.Spec.Fields.wf_field_target_resolves_into_objects` — i.e. only "the resolved field
target is an enumerated object", the one fact that would survive a weakening of part 2 —
and then `color_change_preserves_wf`. `GC.Spec.Mark` verifies, 0 failed.

`GC.Impl.MarkBounded.fst:196` (`check_and_darken_bounded_preserves_inv`) now cites that
instead, so **the citation of `pointer_field_resolve_identity` at
`GC.Impl.MarkBounded.fst:975` is gone.** The lemma itself is untouched and still true;
it simply has one fewer caller (`GC.Impl.Mark.fst:170` remains, on which see below).

**Seventeen structural proof sites.** Eleven in `GC.Impl.MarkBounded.fst` and six in
`GC.Impl.MarkBoundedRootLemmas.fst` mirrored the old spec with

```
    let h = U64.sub v mword in
    if U64.v h + U64.v mword < heap_size then
      let target = SpecHeap.f_address h in
```

and were rewritten mechanically to

```
    let rv = SpecObject.resolve_object (v <: obj_addr) g in
    let h = SpecHeap.hd_address rv in
    SpecHeap.hd_address_bounds rv;
    SpecHeap.f_hd_roundtrip rv;
    if U64.v h + U64.v mword < heap_size then
      let target = SpecHeap.f_address h in
```

`hd_address_bounds` makes the inner bounds test vacuously true now — the address handed
to `darken_if_white_bounded_spec` is always the header of a genuine `obj_addr` — and
`f_hd_roundtrip` gives `target == rv`.

One site had to be reverted: `root_points_to_object_transfer`
(`GC.Impl.MarkBounded.fst:508`) mirrors `root_points_to_object`, not the darken spec, so
its `U64.sub v mword` is correct and must stay. It showed up as
`Error 72 ... Identifier not found: g` because that lemma's heaps are named `g0`/`g1` —
a useful accident, since a silent success there would have been wrong.

**A shared root-resolution lemma rather than five copies.** Four of the rewritten
lemmas need the darkened target to be an enumerated object, which they used to get for
free (the target *was* `v`). New, exported from `GC.Impl.MarkBounded.fsti`:

```
val root_resolves_to_itself (g: heap_state) (v: U64.t)
  : Lemma (requires well_formed_heap g /\ <v is pointer-shaped> /\
                    root_points_to_object g v)
          (ensures Seq.mem (v <: obj_addr) (objects zero_addr g) /\
                   SpecObject.resolve_object (v <: obj_addr) g == (v <: obj_addr))
```

`root_points_to_object` puts `v` in `objects`; part 4 makes it non-infix; hence
`wf_resolve_identity`. This is the honest statement of what is true of *roots*: a root
that is a genuine infix pointer is not an enumerated object, and for such a root it is
correctly the parent closure, not the root value, that gets darkened and pushed.
Exported rather than duplicated in `MarkBoundedRootLemmas`, deliberately — this project
has been bitten before by a proof copy-pasted into a module where a symbol resolves
elsewhere.

Called from `check_and_darken_bounded_spec_preserves_wf`, `..._preserves_bsp`,
`..._preserves_no_pointer_to_blue`, `..._preserves_no_scan_invariant` in
`GC.Impl.MarkBounded.fst`, and from
`check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root` and
`..._preserves_stack_roots` in `MarkBoundedRootLemmas.fst`.

Three signatures gained `well_formed_heap g` as a consequence, each recorded at the
site:

- `GC.Impl.MarkBounded.check_and_darken_bounded_spec_preserves_bsp` — private; its only
  caller `..._preserves_bounded_mark_inv` already gets wf from
  `bounded_mark_inv_elim_wfh`.
- `MarkBoundedRootLemmas.check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root`
  and `..._preserves_stack_roots` — both exported, both with no in-tree caller (they are
  part of a root module's deliverable surface). `preserves_stack_roots` also gained
  `MarkBounded.root_points_to_object g v`: without it, "everything on the stack is a
  root value" is false, because for an infix root it is the parent closure that lands on
  the stack.

**Three `_preserves_read_word` statements changed, and one new preservation triple.**
The requires of `check_and_darken_bounded_spec_preserves_read_word` and its two
`darken_roots_*` versions said `U64.sub v mword <> slot`; the written word is now
`SpecHeap.hd_address (SpecObject.resolve_object (v <: obj_addr) g)`, so that is what
they say. The prefix version then needs to transport the hypothesis, stated at `g`, to
the intermediate heap after `idx0` darkenings. New in the `.fsti`/`.fst`:

```
val check_and_darken_bounded_spec_preserves_resolve   (g) (st) (v) (cap) (x: obj_addr)
val darken_roots_bounded_prefix_preserves_resolve     (g) (st) (roots) (idx) (cap) (x)
```

both `resolve_object x <after> == resolve_object x g`, discharged by
`GC.Spec.Object.color_change_preserves_resolve` — darkening changes colour bits only,
and resolution reads tag and wosize. Shaped after the existing `_preserves_wosize`
triple.

**An ordering error worth noting.** F* rejected the first placement of
`val root_resolves_to_itself` with

```
Error 233: Expected the definition of root_resolves_to_itself to precede
           [check_and_darken_bounded_spec_preserves_read_word]
```

— the order of `val`s in a `.fsti` must match the order of their definitions in the
`.fst`. Moving the `val` after the read_word block fixed it. No proof content involved.

No solver-option changes anywhere in this step: every `#push-options` in
`GC.Impl.MarkBounded.fst` and `MarkBoundedRootLemmas.fst` is as it was, and both files
still build under the Makefile's own flags
(`--z3rlimit 300 --split_queries always --z3refresh` for `GC.Impl.MarkBounded.fst`,
`Makefile:152`; `--split_queries always --z3refresh` for the rest of
`mark-and-sweep/impl`, `Makefile:155`).

### Orphan set

`make orphans` reported 35 unreachable files before this work. A fresh
`fstar.exe --dep full` from `ROOT_MODULES` now reports **33**: `GC.Impl.Closure.fst`
and `.fsti` have become reachable through `GC.Impl.MarkBounded`, exactly as the plan
predicted, and they are therefore now checked by `make verify` and CI. The remaining
non-`spot/` orphans are `GC.Impl.Mark.fst`/`.fsti`, `GC.Impl.Sweep.fst`/`.fsti` and
`GC.Spec.SeqMemLemmas.fst`.

### Diagnostic history for steps 4 and 6, in the order the failures came

Kept because the sequence is the useful part: each error named exactly one thing, and
none of them needed a rlimit increase.

1. `GC.Impl.MarkBounded.fst(203,49-203,60)` — `check_and_darken_bounded_preserves_inv`.
   Fixed by the new `check_and_darken_resolved_field_preserves_wf`.
2. Seventeen structural sites, found by grep rather than by the solver, rewritten in one
   pass.
3. `Error 72 ... Identifier not found: g` at `root_points_to_object_transfer` — the one
   site the blanket rewrite should not have touched. Reverted.
4. `(548,8-548,14)` — `assert (Seq.mem target (objects zero_addr g))` in
   `check_and_darken_bounded_spec_preserves_wf`. Fixed by `root_resolves_to_itself`.
5. `Error 233` — `.fsti` `val` order vs `.fst` definition order. Moved the `val`.
6. `(647,4-647,27)` — the `root_resolves_to_itself g v;` call in `..._preserves_bsp`
   itself failed, because that lemma's `requires` had `bounded_stack_props` but not
   `well_formed_heap`, and part 4 needs wf. Added wf to the `requires`.
7. `(1106,15-1106,45)` — `push_children_bounded_step`. This is the good one: the appeal
   to `pointer_field_resolve_identity` was replaced by `hd_address_bounds` +
   `f_hd_roundtrip` on `resolve_object v g`, i.e. the two specifications now agree
   because they resolve the same way, not because resolution is claimed to be a no-op.
8. `(1243,4-1243,44)` — `Failed to prove pure property: U64.v resolved + U64.v mword <
   heap_size`, the precondition of `darken_if_white_bounded` at the new call site. One
   `SpecHeap.hd_address_bounds (SpecObject.resolve_object (v <: obj_addr) 's);`.

Then: `Verified module: GC.Impl.MarkBounded`, all verification conditions discharged.

### Per-module results (single-file runs, Makefile flags, before the full run)

| module | result |
|---|---|
| `GC.Spec.Fields` (`.fst`, no `.fsti`) | verified, 0 failed |
| `GC.Spec.Object` `.fsti` / `.fst` | verified, 0 failed |
| `GC.Spec.Mark` `.fsti` / `.fst` | verified, 0 failed |
| `GC.Impl.Closure` `.fsti` / `.fst` | verified, 0 failed |
| `GC.Impl.MarkBounded` `.fsti` / `.fst` | verified, 0 failed |
| `GC.Impl.MarkBoundedRootLemmas` `.fsti` / `.fst` | verified, 0 failed |

### `GC.Impl.Mark` — the remaining latent site, deliberately not touched

`GC.Impl.Mark.fst:170` still cites `pointer_field_resolve_identity` to justify its
unbounded `check_and_darken_spec` darkening `v - mword`, so it carries patch 14's bug.
It was left alone for two reasons. It is an orphan — unreachable from `ROOT_MODULES`,
so `make verify` does not check it — and, more to the point, it does not reach the C:
`grep check_and_darken` finds only `check_and_darken_bounded` in both
`generational/snapshot/GC_Gen_Impl.c` (`:1889`) and
`mark-and-sweep/snapshot/GC_Impl.c` (`:178`), so KaRaMeL drops the unbounded version as
unreachable. Fixing it would mean the same treatment for `check_and_darken_spec` and its
own preservation chain, in a module nothing builds.

### Full clean-cache verification

Every `*.checked` under `common`, `generational`, `mark-and-sweep` and `spot` was
deleted, `.depend` and `.depend.raw` removed, then `make -j4 verify` from the repo root
(not `generational/` — that Makefile has no rules for `../common/*.checked`).

**192 modules, `All verification conditions discharged successfully` 192 times,
0 errors, `=== all modules verified ===`, and 192 `.checked` files written.** Two more
modules than the 190 the plan's baseline records, which is `GC.Impl.Closure.fst` and
`.fsti` joining the verified set.

`--report_assumes warn` produced no project-level assumption: every "admitted without an
implementation" line names an F* library interface (`FStar.All`, `FStar.Char`,
`FStar.Reflection.Typing.Builtins`, …). The only `Warning 288`s are the pre-existing ones
in `GC.Impl.Heap.fst:402` and `GC.Gen.Impl.MinorHeap.fst:148-149`. No `admit`, `assume`,
`magic`, `admit_smt_queries` or `--lax` was added anywhere, and no solver option was
changed in any file.

### Files changed

```
 common/spec/GC.Spec.Fields.fst                          |  55 +
 common/spec/GC.Spec.Object.fst                          |   6 +
 common/spec/GC.Spec.Object.fsti                         |  11 +
 mark-and-sweep/spec/GC.Spec.Mark.fst                    |  39 +
 mark-and-sweep/spec/GC.Spec.Mark.fsti                   |  27 +
 mark-and-sweep/impl/GC.Impl.Closure.fst                 |  72 +-
 mark-and-sweep/impl/GC.Impl.Closure.fsti                |  60 +-
 mark-and-sweep/impl/GC.Impl.MarkBounded.fst             | 188 ++-
 mark-and-sweep/impl/GC.Impl.MarkBounded.fsti            |  66 +-
 mark-and-sweep/impl/GC.Impl.MarkBoundedRootLemmas.fst   |  41 +-
 mark-and-sweep/impl/GC.Impl.MarkBoundedRootLemmas.fsti  |  11 +
 11 files changed, 529 insertions(+), 47 deletions(-)
```

Nothing is committed and nothing is staged.

### Step 7 — ready, not run

`make extract` / `make snapshot` were not run, by instruction. Two things to expect when
they are:

- The generated resolution will not look like patch 14's three inline lines.
  `Closure.resolve_object` calls `parent_closure_of_infix`, which calls
  `parent_closure_of_infix_opt`, which returns `option hp_addr` — KaRaMeL will emit an
  `FStar_Pervasives_Native_option__uint64_t` by-value struct and a couple of small
  functions inside the `GC_Gen_Impl` bundle. Semantically it subsumes patch 14 (same
  body-to-body offset, same defensive bounds tests, and the tests are now the *reason*
  `resolve_object` is total rather than an unproven precaution), but the diff against the
  hand-patched copy will not be a clean superset, so patch 14's hunk should be judged
  removed on the strength of the postcondition rather than by textual containment.
- The patch file's remaining hunks will need rebuilding against the new baseline, as in
  `0deb730`: `check_and_darken_bounded` is at
  `generational/snapshot/GC_Gen_Impl.c:1889` and `mark-and-sweep/snapshot/GC_Impl.c:178`
  today, and inserting a call plus two helpers there will shift everything after it.

The runtime evidence the plan asks for — `make coldstart` from clean, `make test`,
`make test-native`, `make world.opt`, then the testsuite against
`ci/expected-failures.txt` — has not been gathered, since it needs the regenerated C.

---

## Step 8 — the Closure_tag confirmation, and what the spot build turned up

### 8.1 The generated resolution was weaker than the hand patch

Extraction succeeded and `resolve_object` came out clean, but comparing it against the
hand patch showed a missing check:

| check | hand patch 14 | generated (first cut) |
|---|---|---|
| tag at `v-8` is 249 | yes | yes |
| computed parent in-heap | yes | yes |
| parent's tag is `Closure_tag`(247) | **yes** | **no** |

The hand patch's own comment called this "the same soundness condition as HAND PATCH
15": `is_infix` is applied to a word that is *not known to be a header*. A field value
only has to pass `is_pointer` — alignment plus range, nothing else — to reach
`check_and_darken_bounded`, and an OCaml integer whose low byte is `0xf9` passes that.
Without the parent check such a word gets "resolved" by subtracting a garbage offset.

This is not the same as patch 16's dropped `!= 249` conjunct, which really was dead
code: there, queue entries provably came from `minor_objects`, and
`minor_objects_not_infix` settles it. Here the only thing standing between a non-pointer
and an arbitrary heap address is `no_scan_invariant` — the assumption the core dump
falsifies. So the check is load-bearing in a way patch 16's was not, and shipping
without it would have made the collector strictly weaker than the patch being retired.

### 8.2 Putting it in verified source

The check cannot be *added to the implementation alone*: `resolve_object`'s
postcondition ties it to the ghost `GC.Spec.Object.resolve_object`, and the executable
has only `is_heap` in its precondition — no well-formedness with which to prove the
check passes. So the ghost definition had to gain the same condition:

```
let resolve_object (addr: obj_addr) (g: heap) : GTot obj_addr =
  if is_infix addr g then
    let p = parent_closure_addr_nat addr g in
    if p >= 8 && p < heap_size && p % 8 = 0 then
      (let pa : obj_addr = U64.uint_to_t p in
       if is_closure pa g then pa else addr)
    else addr
  else addr
```

`resolve_object` is `val`-declared in the `.fsti`, which kept the blast radius small:
downstream modules see it only through lemmas, so the only statement that had to change
was `resolve_infix_spec`'s precondition (gaining `is_closure (U64.uint_to_t p) g`), and
it has exactly one call site — in `GC.Impl.Closure.fst`, the file being edited anyway.
Three further adjustments inside `GC.Spec.Object`:

- `resolve_infix_not_closure`, new, for the third rejection case (valid parent address,
  wrong tag → return the input). `resolve_infix_invalid` needed no change: its
  precondition negates the *old* guard, which still implies the new one.
- `resolve_object_in_objects` now calls `infix_wf_elim` — `infix_wf` already promised
  `is_closure` of the parent, so the new condition was already available, just not
  brought into scope.
- `color_change_preserves_resolve` needed the two `wosize_*` helpers moved above it and
  a `color_change_preserves_is_closure` call on the parent. Colours change neither tag
  nor wosize, so all three guard conditions are stable.

On the executable side, `is_closure_object` was dead code with no postcondition; it now
mirrors `is_infix_object` exactly, and `parent_closure_of_infix_opt` calls it on the
computed parent's header. `f_hd_roundtrip` bridges the address it reports on back to
`parent_f_addr`. `resolve_object_infix_agrees` became a three-way case split.

Full run from the existing caches: **224 modules, 0 failures.**

### 8.3 Runtime: coldstart, and the A/B

- With the generated resolution: `make coldstart` exits 0. Twice.
- With `resolve_object` neutered in the C to `return obj`: exits 2,
  `camlinternalFormat.cmo` — **Segmentation fault (core dumped)**. The original failure.

That is the cleanest available evidence that the generated code is what carries patch
14, rather than something else having changed underneath it.

### 8.4 The patch file

`0001-infix-handling.patch` went 104 → 75 lines: patch 14's hunk is gone, 15/15b were
re-applied to the new baseline at three sites (`addr`, `r`, `child`), and the round trip
was checked both ways — `verify-snapshot-patches` reports present, and re-applying from
the pristine extraction reproduces the patched snapshot byte-for-byte.

### 8.5 Three spot files were broken, and the build could not see it

`make extract` failed with `Module GC.SPOT.Preconditions cannot be found`. The cause was
not the module — it is right there in `spot/` — but the root `Makefile`'s `INCLUDES`,
which never had `--include spot`. `spot/%.checked` was therefore unbuildable from the
root, and `make verify` never asked for it, so the whole SPOT campaign was outside CI.
It only surfaced now because invalidating `GC.Spec.Object` made every stale cache need
rebuilding.

With `--include spot` added, three of the 28 files failed — and two of the three failed
**because of commit `0cc9932`**, this task's own earlier work:

- `ConcreteScenarios.fst` (4 assertions) and `ConcreteFull.fst` (1) — patch 14 added a
  `well_formed_heap` hypothesis to the root lemmas, and restated
  `darken_roots_bounded_spec_preserves_read_word`'s frame condition over
  `hd_address (resolve_object v g)`. The scenarios supplied neither.

  Awkwardly, `GC.Gen.CheneyCorrectness` only preserves `well_formed_heap_part1` across a
  minor collection, and says so explicitly. But the *full* predicate does follow from
  the concrete collection heap shape via
  `CheneyPreservation.cheney_collect_preserves_wfh_from_shape`, which
  `ConcreteScenarios` was already calling — 130 lines *after* the first site that needed
  it. Hoisting that call fixed all four. Two lemmas became exports to serve
  `ConcreteFull`: `spot_post_minor_major_wf` and
  `spot_post_minor_roots_point_to_objects`, plus
  `MarkBounded.check_and_darken_bounded_spec_preserves_wf`, which existed in the `.fst`
  but was not in the interface.

  `ConcreteFull`'s local `no_root_header` had to be restated in the resolved form and
  reduced back via `root_resolves_to_itself`. Its guard also had to be widened to put
  the address bounds in scope — the `ensures` states them as hypotheses of an
  implication, which does not make them available to the proof body.

- `ConcreteMinor.fst:292` was **not** caused by this work: `spot_minor2_field_zero`
  simply needs more than the default rlimit. It passes at `--z3rlimit 40`, now set as a
  per-file override.

### 8.6 Build-graph fixes worth keeping

`--include spot` alone was not enough to make `make` build spot: `.depend` is generated
from `ROOT_MODULES` only, so make had no ordering information and fired the files
arbitrarily, whereupon F* declines to write a cache whose dependencies have none. Adding
`$(SPOT_SRC)` to a new `DEP_ROOTS` fixes the ordering.

The same reasoning applies to `GC.Impl.Mark` and `GC.Impl.Sweep`: both are in the
generational bundle's `ALL_KRML_MODS` yet unreachable from `ROOT_MODULES`, which is why
`make extract` failed with `Module GC.Impl.Mark.fst was not checked` and needed a manual
pre-step. They are now `EXTRACT_ONLY_ROOTS` in the dep scan.

`ROOT_MODULES` itself is unchanged, so `make orphans` still measures what is unreachable
from the real entry points. **Orphans: 33 → 1** (`GC.Spec.SeqMemLemmas.fst`), and the
verify set went 192 → 224 modules.
