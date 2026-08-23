# Retiring hand patch 16 into verified source — working log

Branch `akhil/infix`, off `native`. Goal: express the `No_scan_tag` guard in the
verified source so `patches/snapshot/0001-infix-handling.patch` can drop patch 16's
hunk. Nothing here is committed yet, by request.

This file is a running record. Sections 1–4 are history (complete); section 5 is
appended to as the reachability work proceeds.

---

## 1. The bug being fixed

`make world.opt` on the verified GC failed intermittently — roughly once per 2000
`ocamlopt` invocations, so ~40% of full builds, at a different compilation unit each
time and never reproducible on a fixed input (0/30, 0/20, 0/25 on the units that had
failed). Two `coredumpctl` cores of real build failures — one bytecode (`ocamlrun`),
one native (`ocamlopt.opt`) — faulted at the *same* instruction, `scan_loop+0x25c`.

Chain, reconstructed from the cores:

1. `scan_loop` examined the fields of a `Custom_tag` block (a boxed `Int64`), whose
   payload is raw data, not values.
2. The payload `0xcd180` (840 064) is 8-aligned and inside `[8, 2 MiB)`, so it passed
   the collector's pointer heuristic and was enqueued as an object.
3. Its "header", read from `payload − 8`, was really `&caml_int64_ops` (`0x44ede0`),
   which decodes as tag 224 / wosize 4411 — passing the existing bounds checks.
4. So ~35 KB of unrelated nursery was over-scanned, hitting `0x7a6500f9` — an
   *ordinary odd OCaml integer* whose low byte is `0xf9` = 249. Read as an infix
   header it claimed the parent was 2 005 312 words back: 15.3 MiB against a 2 MiB
   nursery. The subtraction underflowed and the read left the mapping.

Two properties worth recording. The `Int64`'s two raw words fail *differently*: the
ops pointer is 8-aligned but numerically far above the nursery, so the range check
rejects it; the payload is a small even number and passes everything. And forwarding
*writes back*, so this could silently corrupt an `Int64`'s value rather than crash —
a build that succeeded under the old code is not evidence its output was correct.

Instrumented, one compilation of `middle_end/flambda/inline_and_simplify.ml`:
`no-scan objects skipped=31370  bogus children prevented=3028`.

A/B on a targeted reproducer (`ocaml-integration/tests/noscan_stress.ml`):
**40/40 segfaults pre-fix, 0/40 post-fix**, pre-fix crash at the same `+0x25c`.

## 2. Commits on this branch

- **`02d1743` — infix offset convention.** `parent_closure_addr_nat` computed
  `v − 8 − wosize*8`, following its own doc comment ("offset runs to the infix
  *header*"). OCaml measures body-to-body (`mlvalues.h:229`,
  `major_gc.c:288` `v -= Infix_offset_val(v)`, a value address on both sides), so the
  correct form is `v − wosize*8`. Both existing implementations —
  `GC.Impl.Closure.parent_closure_of_infix_opt` and the hand-patched C — already used
  body-to-body; only the spec disagreed. Machine-checked before changing anything, by
  making OCaml's convention an explicit hypothesis and letting F\* do the arithmetic
  under each reading; both typecheck, so the spec was coherent with the wrong
  convention. Verified across its full blast radius (5 modules), 0 failed fragments.
  No extracted C changes — `GTot`, erased.
- **`dde4b57` — dead second heap enumeration removed.** `GC.Spec.Object` exported its
  own `objects` walk plus `allocated_blocks`, `hp_to_obj`, `objects_addresses_ge_8`
  and two private lemmas. `GC.Spec.Fields` opens that module and *redefines* `objects`
  with a tighter element type, and that is the copy everything uses: 314 references
  against 0. −167 lines. Done before the interesting work so new lemmas could not be
  proved against a dead copy.

## 3. Uncommitted, verified: the spec-side guard (A1 + A2)

All of the following verify with **0 failed fragments**.

- `common/spec/GC.Spec.Object.fsti/.fst` — tag constants `closure_tag`/`infix_tag`/
  `no_scan_tag` made transparent (were abstract `val`s). Deviates from the original
  plan, which said to move them to `GC.Spec.Base`: the reveal lemmas have 6 live
  callers, 3 qualified, and abstract constants would make
  `minor_tag ms addr = U64.v infix_tag` opaque, forcing a reveal lemma through the ~30
  modules that rely on `= 249` reducing. Transparency achieves the same end in one
  line. The ~18 pre-existing hardcoded `249` literals in `MinorHeap` were left alone
  deliberately — most sit in refinement types propagating into 30 modules' signatures.
- `generational/spec/GC.Gen.MinorHeap.fsti` — `module SpecObj = GC.Spec.Object` plus
  `minor_is_no_scan ms addr = minor_tag ms addr >= U64.v SpecObj.no_scan_tag`. Cannot
  reuse `GC.Spec.Object.is_no_scan`, which is typed over the major `heap`; only the
  constant is genuinely shared.
- `generational/spec/GC.Gen.Cheney.fst` + `.fsti` — the guard itself:
  ```
  let cs' = if minor_is_no_scan minor obj then cs
            else cheney_forward_fields minor cs obj 0 (minor_wosize minor obj) in
  ```
  with `cheney_scan_step`'s `ensures` updated in both files.
- **27 preservation-proof sites** across `Cheney.fst` (8), `CheneyBFS.fst`,
  `Cheney.SimOne.fst` and all six `CheneyPreservation.*.fst` (19). Mostly a one-line
  mirror of the branch in the proof's own `cs'` binding. One site,
  `cheney_scan_preserves_source_inv` in `CheneyPreservation.Injectivity.fst`, needed
  explicit `if/else` branches: at `--ifuel 0` the solver would not case-split a
  conditional inside a `let` to discharge nine preconditions.

Module results: `GC.Spec.Object` 152, `MinorHeap` 133, `Cheney` 174, `CheneyBFS` 58,
`Cheney.SimOne` 60, `Injectivity` 113, plus `CheneyPreservation`, `.Fields`,
`.Forwarding`, `.Frame`, `.NonBlueOrigin` — all 0 failed.

## 4. The blocker, diagnosed

`generational/impl/GC.Gen.Impl.Cheney.fst` — the Pulse `scan_loop`, the module that
actually generates the C. A no-scan arm was added to its existing cascade of guards
(`read_minor_tag minor obj >= SpecObj.no_scan_tag` → advance `scan`), plus an assert
bridging the runtime test to the ghost predicate. It does not verify.

With `--split_queries always` added temporarily, **exactly one** VC fails out of the
whole loop invariant:

```
scanned_prefix_closed (Mkminor_state 'md 'mb) __cs_s (SZ.v (__sv + 1))
```

under `not __oom_s`. Everything else passes, including the impl-matches-spec equation
`cheney_scan … == cheney_scan …`. The bridging assert *works* — it appears in the
failing query's hypotheses and does collapse the `match minor_is_no_scan …` inside
`cheney_scan_step`'s equation.

So the goal is **false as stated**, not hard: no hint, restructuring, `--ifuel 1` or
rlimit increase can prove it. `scanned_prefix_closed` (`CheneyBFS.fst:449`) requires
every `minor_successors` child of every entry below `scan` to be forwarded; advancing
over a *skipped* entry therefore demands that entry's successors be forwarded, and the
no-scan arm forwards nothing. `minor_successors ms obj = collect_minor_successors ms
obj 0 (minor_wosize ms obj)` (`Reachability.fst:41`) walks all `wosize` fields
regardless of tag, so a raw payload word coinciding numerically with a live nursery
body address is a genuine member. **The specification's reachability relation
over-approximates OCaml semantics; the guarded collector is correct.**

### Diagnostic history worth keeping, because two readings were wrong

- Predicted `scanned_prefix_closed`/`minor_successors` from reading the invariant —
  correct, but asserted before checking.
- Then read the pre-arm diagnostic, saw the `cheney_scan` equation failing, and
  presented that as a correction. It was accurate *for the pre-arm state* — with no
  guard in the impl, the C did forwarding the spec forbade — but the failure moved once
  the arm landed. Two different questions, reported as one being wrong.
- The real answer only came from splitting the query. The lesson: this file has
  `--z3rlimit 80 --fuel 0 --ifuel 0` and no `--split_queries`, so F\* prints the entire
  invariant conjunction and the culprit is invisible. Split first, infer never.

### Rejected shortcut, recorded because it is tempting

Adding a well-formedness conjunct like "no field of a no-scan minor block is in
`minor_objects`" would make the obligation provable with no definitional change. It
was rejected: the claim is *false* (a raw `Int64` payload word can numerically equal a
live nursery body address) and is morally an `assume`. This is the same trap as
`no_scan_invariant` (`GC.Spec.Fields.fst:742`), which asserts no-scan payloads are
never `is_pointer`-shaped and which the core dump directly falsifies.

## 5. The fix in progress: guarding minor-side reachability

The major side already does exactly this, and has since the module was written
(`09b932f "Add combined graph vocabulary"` — born guarded, never retrofitted):

```
CombinedGraph.fst:155   major_object_edges ... = if is_no_scan obj major then Seq.empty else ...
CombinedGraph.fst:131   minor_object_edges ... = minor_field_edges ms major obj wz 0     <- no guard
```

Symbol counts are near-symmetric with the guarded major side (`minor_object_edges`
25 mentions/1 file vs `major_object_edges` 23/1; `minor_edge_elim` 8/5 vs
`major_edge_elim` 7/5), so each minor-side repair has a structurally parallel
major-side proof that already works — a template, though not a retrofit precedent.

Planned steps:

- **(a)** `Reachability.fst:41` — `minor_successors ms obj = if minor_is_no_scan ms obj
  then Seq.empty else collect_minor_successors ...`. `collect_minor_successors`
  untouched. `minor_reachable_aux` expands via `minor_successors`, so `minor_reachable`
  inherits the guard and every `minor_reachable_*` lemma keeps its statement.
- **(b)** Same file: case-splits in `minor_successors_valid` and
  `minor_successors_length`; new `minor_successors_no_scan`.
- **(c)** `Reachability.fsti:67` — `minor_successors_char`'s RHS gains
  `~(minor_is_no_scan ms x)`. Two of its three callers use only the elimination
  direction and are unaffected; `ReachabilityBridge.fst:355` uses introduction.
- **(d)** *Required, not optional.* Guard `minor_object_edges`
  (`CombinedGraph.fst:131`) and add `~(minor_is_no_scan ms src)` to
  `minor_field_edge_intro`'s `requires` and `minor_edge_elim`'s `ensures`. Without
  this, `ReachabilityBridge.reachability_bridge` (`combined_reachable ⊆ live_set`,
  `live_set = minor_reachable`) becomes **false** and (c)'s caller is unfixable. So
  (a) and (d) must land together; expect a window where the tree is broken.
- **(e)** `ReachabilityBridge.fst:355` then gets `~(minor_is_no_scan minor src)` from
  the strengthened `minor_edge_elim`.
- **(f)** New `CheneyBFS.scanned_prefix_step_no_scan` — from
  `scanned_prefix_closed minor cs scan`, `scan < |cs_queue|` and
  `minor_is_no_scan minor (Seq.index cs.cs_queue scan)`, conclude
  `scanned_prefix_closed minor cs (scan+1)`. Reveal the opaque at both indices;
  `k < scan` by hypothesis, `k = scan` vacuous via `minor_successors_no_scan`.
- **(g)** One call to (f) in the impl's no-scan arm. The only impl-side change.

Re-verification set: `Reachability`, `CombinedGraph`, `ReachabilityBridge`,
`CheneyBFS`, then transitively `MinorCollectForwarding.*`, `CheneyCorrectness`,
`GC.Gen.Impl.*`, and `spot/GC.SPOT.ConcreteForwarding.fst` (`make verify` does cover
`spot/` — `ALL_SRC` includes `SPOT_SRC` even though it is not reachable from
`ROOT_MODULES`).

### Alternatives ruled out

- Weakening only `scanned_prefix_closed` and `fwd_closed` (`CheneyBFS.fsti:42`) with
  `~(minor_is_no_scan minor x)` keeps the change inside `CheneyBFS` but breaks
  `fwd_well_formed_covers_reachable` (`CheneyBFS.fsti:62`), whose conclusion
  quantifies over `minor_reachable`. It relocates the problem into reachability.
- Dropping `fwd_closed` from `scan_loop`'s postcondition is not viable: it feeds
  `cheney_no_oom_from_loop_posts` → `cheney_no_oom`, a deliverable at
  `GC.Gen.Impl.fst:823,836`.

### Environment note

Every `.checked` cache for the modified modules is stale (sources 08-19, caches
08-07), so each verification run re-elaborates from source. Results are trustworthy
but slow; a `make verify` pass to repopulate is worth doing before this work. A faster
probe (single held-open MCP session, `verify-to-position`, untruncated diagnostics,
~100 s for the `scan_loop` fragment) is at `scratchpad/probe.py`.

### Progress

_(appended as the work proceeds)_

#### Step 0 — cache repopulation, and a find that changes the risk profile

`make -j4 verify` from the repo root (not `generational/`: that Makefile has no rules
for `../common/*.checked`, and those are exactly the stale ones). `make -n` counted 174
`fstar.exe` invocations, i.e. `GC.Spec.Object` being stale invalidates most of the tree.

Result: **169 modules verified, 2 failures**, ~1 h 15 min wall at `-j4`.

- `generational/impl/GC.Gen.Impl.Cheney.fst(730,6-730,26)` — the known blocker,
  `scan := SZ.add s 1sz` in the no-scan arm. Section 4 already has the split-query
  diagnosis. Worth noting the Makefile compiles this file with
  `--z3rlimit 160 --split_queries always` (`Makefile:181`), and the in-file
  `#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"` does not mention
  `--split_queries`, so the command-line setting stays in force. Splitting does not
  break up a Pulse `pure` conjunction, though, so the printed goal is still the whole
  loop invariant.
- `generational/spec/GC.Gen.CheneyPreservation.Injectivity.fst(1058,2-1079,39)` —
  `Assertion failed`. **Not previously known.** Section 3 records this module as
  verifying with 113 fragments, 0 failed. It does not, under the flags the build
  actually uses. Its `.fsti` verified, so everything downstream of it is checked
  against a sound interface and the 169 successes stand; but the module's own proof
  has an unproven obligation, and its `.fst.checked` is still the stale 2026-08-07
  file. Chased below before touching the reachability work — an incomplete proof in
  the same subsystem is not something to build on top of.

While it ran, a read-only survey of the (d)/(e) blast radius turned up two things the
plan did not know about.

**`minor_no_scan_invariant` already exists** (`Promote.fsti:752`): for every
`obj ∈ minor_objects` with `minor_tag ≥ 251` and every `j < minor_wosize`,
`~(is_pointer_field (minor_read_field minor obj j))` and
`~(is_minor_pointer (to_minor_offset (minor_read_field minor obj j)))`. It is a
conjunct of `minor_heap_shape` / `collection_heap_shape` (`HeapInvariant.fst:80`) and
is asserted as a precondition of the top-level entry point
(`GC.Gen.Impl.fsti:154`, established by the lemma at `GC.Gen.Impl.fst:97`).

This is *exactly* the conjunct section 4 rejected as "false and morally an `assume`",
and the project already assumes it — for the minor heap, not just the major one. The
core dump falsifies it directly: the `Int64` payload `0xcd180` **is**
`is_minor_pointer`-shaped. Recording that as a finding, not acting on it here.

**It is already used to prove the fact (e) needs.**
`MinorCollectForwarding.NormalEdges.fst:214` `minor_source_edge_not_no_scan` derives
`minor_tag minor src < 251` from nothing but `collection_heap_shape` and
`CG.mem_ce (MinorV src, dst) (build_combined_graph minor major)` — by
`minor_edge_elim`, then a contradiction against `minor_no_scan_invariant` in both the
`MinorV` and `MajorV` cases (lines 233–254).

Two consequences.

1. There is a cheaper route to the goal than (a)–(g): leave every definition alone,
   prove `minor_successors ms obj == Seq.empty` for no-scan `obj` *from*
   `minor_no_scan_invariant`, and thread that invariant into `scan_loop`'s `requires`
   up to `GC.Gen.Impl.fst`, where it is already in hand. Three lemmas and a
   precondition, no `minor_successors` change, no `CombinedGraph` change. **Not
   taking it.** It buys the obligation with the same false assumption the guard exists
   to stop relying on, and it leaves `minor_reachable` over-approximating. Worth
   knowing it exists, because it is the fallback if (d) turns out to be false rather
   than merely hard.
2. It de-risks (d) considerably. Under `minor_no_scan_invariant` a no-scan minor
   block has *no* classifiable field at all — `classify_minor_field` returns `None`
   for each — so `minor_object_edges` is already `Seq.empty` for such a block. Adding
   the guard therefore cannot make `reachability_bridge` false; it makes
   unconditional something the model already implied. The invariant is not in scope
   inside `CombinedGraph` (`build_combined_graph_wf` requires only
   `well_formed_heap major /\ minor_wf ms`), which is precisely why the guard has to
   be definitional rather than derived.

Also confirmed by inspection, so (a) is mechanical: everything in `Reachability.fst`
treats `minor_successors` opaquely except `minor_successors_valid` (:80),
`minor_successors_length` (:350) and `minor_successors_char` (:381).
`minor_reachable_aux` (:92) expands the worklist via `minor_successors`, so
`minor_reachable` inherits the guard with no change to any `minor_reachable_*`
statement or proof. `no_scan_tag = 251UL` (`GC.Spec.Object.fsti:44`), so
`minor_tag minor x < 251` and `~(minor_is_no_scan minor x)` are the same fact.

#### Step 0b — the Injectivity failure, diagnosed and fixed

`--query_stats` on `GC.Gen.CheneyPreservation.Injectivity.fst` localises it: the
fragment splits into 57 sub-queries and **query 46 of `cheney_scan_preserves_inj_inv`
fails with `{reason-unknown=unknown because canceled}` after 76 s, using rlimit
180.000 of 180**. Its neighbour, query 47, succeeds but spends 28 s and rlimit 74.8.
The "Assertion failed / See also Prims.fst(419)" wording is misleading — nothing is
wrong with the one `assert (fuel' < fuel)` in that body; F\* labels the exhausted
sub-goal that way.

Cause: an omission in the 27-site pass of section 3, not a new problem.
`cheney_scan_preserves_inj_inv` (`Injectivity.fst:1043`) still carried the guard as a
conditional binding

```
let cs' = if minor_is_no_scan minor obj then cs
          else cheney_forward_fields minor cs obj 0 wz in
cheney_scan_preserves_inj_inv minor cs' (scan + 1) fuel'
```

while its sibling `cheney_scan_preserves_source_inv` (`:1149`), 100 lines below in the
same file, had already been rewritten into explicit `if`/`else` branches for exactly
this reason — section 3 records that rewrite, but it was applied to one of the two
functions. Ten preconditions on `cs'`, each its own sub-query, each needing the solver
to case-split an ITE under `--ifuel 0`.

Fix: mirror the sibling. `Injectivity.fst:1057-1085` now branches on
`minor_is_no_scan minor obj` and passes `cs` unchanged in the no-scan branch, so each
branch has a syntactically concrete state and no ITE reaches Z3. The five
`cheney_forward_fields_preserves_*` calls moved inside the `else`, where they are the
only place they are needed. No flag changes: still `--z3rlimit 180 --fuel 1 --ifuel 0
--split_queries always`, and the rlimit was *not* raised.

Verifies clean in 4 min 00 s, 0 failed. The lesson generalises: with the guard written
as a conditional `let`, `--ifuel 0` makes cost scale with the number of preconditions,
and it degrades into a timeout rather than a clean "could not prove". Any remaining
site of this shape in the 27 is a latent timeout. Two are now known to have needed the
explicit form; both are `cheney_scan_preserves_*` recursions with ten-conjunct
`requires`.

#### Steps (a)–(c) — guarding `minor_successors`

`generational/spec/GC.Gen.Reachability.fst`:

- `minor_successors` (`:44`) is now
  `if minor_is_no_scan ms obj then Seq.empty else collect_minor_successors ms obj 0 (minor_wosize ms obj)`.
  `collect_minor_successors` untouched.
- New `private mem_of_len_zero` (`:51`): `Seq.length s == 0 ==> ~(Seq.mem x s)`, proved
  as `Classical.move_requires (Seq.mem_index x) s`. Written this way on purpose —
  `Seq.mem` is `count x s > 0` and unfolding `count` needs fuel, whereas `mem_index`
  plus `length s == 0` is fuel-free. Three call sites want it and two of them sit at
  file-default fuel.
- `minor_successors_valid`, `minor_successors_length`, `minor_successors_char` each
  gained a two-way case split; the no-scan branch is `mem_of_len_zero` or `()`.
- New `minor_successors_no_scan ms obj y : ~(Seq.mem y (minor_successors ms obj))`
  under `minor_is_no_scan ms obj`. One line: `minor_successors_char ms obj y`. Stated
  point-wise in `y` rather than as `== Seq.empty` so callers never have to reason about
  `Seq.empty` membership.

`generational/spec/GC.Gen.Reachability.fsti`: `minor_successors_char`'s right-hand side
gained `~(minor_is_no_scan ms x) /\ ...`, and `minor_successors_no_scan` was exposed.

Nothing else in the module needed touching, as predicted. Both files verify, 0 failed;
the `.fst` in 11 s.

#### Step (d) — guarding `minor_object_edges`

`generational/spec/GC.Gen.CombinedGraph.fst`, six edits, each the mirror of an existing
major-side line:

- `minor_object_edges` (`:131`) → `if minor_is_no_scan ms obj then Seq.empty else ...`.
- `all_minor_edges_wf` (`:465`) → `if minor_is_no_scan ms obj then () else minor_field_edges_wf ...`,
  copying `all_major_edges_wf`'s shape.
- `minor_field_edge_intro` (`:611`) gained `~(minor_is_no_scan ms src)` in `requires`,
  which is what makes its step-2 assertion
  `minor_object_edges ms major src == minor_field_edges ms major src wz 0` hold. Same
  as `major_field_edge_intro`.
- `minor_object_edges_no_major` (`:952`) → case split.
- `edge_source_decomposition`'s `MinorV` branch (`:1000`) gained
  `assert (~(minor_is_no_scan ms obj))`, discharged the way the `MajorV` branch already
  does it: membership in a `Seq.empty` is a contradiction, visible at `--fuel 1`.
- `minor_edge_elim` (`:1040`) gained `~(minor_is_no_scan ms src)` in `ensures` plus the
  same `assert`.

`.fsti` mirrors the two signature changes. No flag changes anywhere in the module; the
existing `--fuel 1 --ifuel 1 --z3rlimit 20` blocks suffice. Verifies 0 failed.

One wrinkle worth knowing: after changing `Reachability.fsti`, a direct `fstar.exe` run
on `CombinedGraph` reports 0 errors but refuses to write its `.checked`, because
`GC.Gen.Promote.fsti.checked` is stale by dependence hash. Going through `make
<target>.checked` rebuilds the chain in order and does write. Use make, not bare
`fstar.exe`, once an interface has moved.

#### Step (e) — `ReachabilityBridge`: no change needed

`GC.Gen.ReachabilityBridge` verifies untouched, 0 failed in 3.6 s. The introduction-
direction use of `minor_successors_char` at `:355` gets `~(minor_is_no_scan minor src)`
straight out of the `minor_edge_elim` call nine lines above it, at `:346`. This was the
concentrated risk in the plan and it cost nothing.

#### Step (f) — `scanned_prefix_step_no_scan`

`generational/spec/GC.Gen.CheneyBFS.fst` + `.fsti`, inserted before
`scanned_prefix_step_oom`. From `scanned_prefix_closed minor cs scan`,
`scan < |cs_queue|` and `minor_is_no_scan minor (Seq.index cs.cs_queue scan)`, conclude
`scanned_prefix_closed minor cs (scan + 1)` — same `cs`. Reveal the opaque at both
indices; the `k = scan` case is `minor_successors_no_scan minor parent y`, the
`k < scan` cases are `()`. Plus an OOM-guarded wrapper
`scanned_prefix_step_no_scan_oom`, shaped like the existing
`scanned_prefix_step_oom` so the impl's invariant conjunct
`not oom ==> scanned_prefix_closed ...` matches without reshaping. No new flags;
inherits the block's `--z3rlimit 80 --fuel 0 --ifuel 0`. 0 failed.

#### Step (g) — the impl, and the goal

`generational/impl/GC.Gen.Impl.Cheney.fst`, in the no-scan arm, before
`scan := SZ.add s 1sz`:

```
let oom_now = !oom_ref;
CheneyBFS.scanned_prefix_step_no_scan_oom ({data='md; bump='mb} <: minor_state)
  (reveal cs_cur) (SZ.v s) oom_now;
```

`oom_ref` is read only to name the current flag for the lemma — this arm does not
allocate, so it cannot set it. The other two hypotheses were already established
earlier in the loop body: `SZ.v s < Seq.length cs_cur.cs_queue` and
`obj == Seq.index cs_cur.cs_queue (SZ.v s)` together with the existing
`assert (pure (minor_is_no_scan ... obj))`.

**`Verified module: GC.Gen.Impl.Cheney` / All verification conditions discharged
successfully.** 12 min 53 s for the target including its rebuilt prerequisites. No
`admit`, no `assume`, no added axiom, and no solver-option change in this module — it
still carries `--z3rlimit 80 --fuel 0 --ifuel 0` in the `scan_loop` `#push-options`,
with the Makefile's `--z3rlimit 160 --split_queries always` on the command line as
before. The runtime test `U64.gte (read_minor_tag minor obj) SpecObj.no_scan_tag` is
untouched and still the arm's condition, so it still extracts.

Hypothesis 2 from section 5 was therefore necessary and sufficient, and the
`minor_no_scan_invariant` fallback recorded in step 0 was not needed anywhere.

#### The one downstream break: `MinorCollectForwarding.Reflection`

A full `make -j4 verify` after (a)–(g) gave **71 verified, one module failed** — and it
was not one of the four the plan named. `GC.Gen.MinorCollectForwarding.Reflection.fst`:

```
* Error 19 at ...Reflection.fst(214,13-214,35): Assertion failed
  - See also generational/spec/GC.Gen.CombinedGraph.fsti(201,20-201,46)
* Error 19 at ...Reflection.fst(253,13-253,35): Assertion failed
  - See also generational/spec/GC.Gen.CombinedGraph.fsti(201,20-201,46)
* Error 19 at ...Reflection.fst(122,3-295,7): Assertion failed
```

`CombinedGraph.fsti:201` is the `~(minor_is_no_scan ms src)` clause step (d) added to
`minor_field_edge_intro`. This is the *introduction* direction, in the proof that a
post-collection major-heap edge out of a promoted image reflects a pre-collection
combined-graph edge out of the minor source. There is no edge in hand to read the fact
off, so the fact has to come from somewhere else.

Two ways to supply it:

- **Tag preservation.** The lemma already establishes
  `is_no_scan fwd_src_obj prom.major_final = false` (`Reflection.fst:174`), and
  `promote_object` sets the target's tag from `minor_tag minor obj`
  (`Promote.fsti:115-117`), so morally `minor_tag minor src < 251` follows. But the
  existing lemma in that direction,
  `cheney_promote_fwd_target_not_no_scan_of_minor_tag_lt`
  (`CheneyPreservation.Fields.fst:813`), is a full BFS-invariant preservation proof
  threaded through `cheney_forward_roots` and `cheney_scan` via
  `fwd_target_not_no_scan_state`. Getting the converse means mirroring that whole
  invariant chain — the same shape of work as the 27-site pass. Assumption-free, and
  expensive.
- **`minor_no_scan_invariant`,** which is already in scope at all six call sites (both
  enclosing lemmas call `GenInv.minor_heap_shape_elim minor`, at `:132` and `:328`).

Took the second, with the reliance made explicit at the call site rather than hidden in
a precondition. New `MCFNE.minor_field_source_not_no_scan` in
`GC.Gen.MinorCollectForwarding.NormalEdges.fst/.fsti`: from `minor_no_scan_invariant`,
`src ∈ minor_objects`, `i < minor_wosize src` and
`classify_minor_field ... == Some dst`, conclude `~(minor_is_no_scan minor src)`. The
body is the contradiction argument lifted verbatim out of
`minor_source_edge_not_no_scan` — same module, so every symbol
(`classify_minor_field_inv_minor/_major`, `objects_addresses_gt_start`,
`is_pointer_field`) resolves to the same definition it did before. Deliberate: this
project has been bitten by copy-pasting a proof into a module where `is_pointer_field`
resolves elsewhere. Same flags as its source, `--z3rlimit 40 --fuel 0 --ifuel 1
--split_queries always`.

`Reflection.fst` then gets one line before each of the six
`CG.minor_field_edge_intro` calls (`:214, :254, :280, :416, :433, :459`). Only two of
the six actually errored; the other four are in branches that end in `assert False` or
where the fact was already derivable. Inserted at all six anyway — a site that happens
to be discharged today by an incidental hypothesis is a latent break, and uniformity
costs six lines. `NormalEdges.fst` 0 failed in 48 s, `Reflection.fst` (interface and
implementation) 0 failed in 1 min 30 s.

Where this leaves the assumption. The correctness of *skipping* — the thing the C guard
does — now rests on the definitional guards in `minor_successors` and
`minor_object_edges` and on nothing else. `minor_no_scan_invariant` is used in exactly
one place, to show the model's graph is rich enough to reflect post-collection heap
edges, which is a claim about the graph's completeness rather than about the
collector's soundness. Net, uses of the invariant went *down*: see below.

#### Cleanup: one use of `minor_no_scan_invariant` removed

With the graph guarded, `MCFNE.minor_source_edge_not_no_scan`
(`NormalEdges.fst:214`) no longer needs any of its old machinery. It used to call
`collection_heap_shape_elim`, `minor_heap_shape_elim`, assert
`minor_no_scan_invariant`, obtain a field index by indefinite description, and derive a
contradiction in both the `MinorV` and `MajorV` cases — 30 lines. It is now one line,
`CG.minor_edge_elim minor major src dst`, because that lemma's `ensures` already
carries `~(minor_is_no_scan minor src)` and `no_scan_tag = 251UL`. Signature unchanged,
so no caller moved. 0 failed in 47 s.

#### Doc comments corrected

`minor_reachable` genuinely means something different now, so three comment blocks were
updated rather than left to mislead: the module header and the `minor_successors`
doc in `Reachability.fsti`, the `fwd_closed` doc in `CheneyBFS.fsti`, and the
`cheney_promotes_all_reachable` doc in `CheneyCorrectness.fsti` — the last being the
top-level statement "every reachable minor object is forwarded", which now quantifies
over reachability through scannable fields only. Comment-only, but they change the
interface digests, so they force a rebuild of everything downstream; batched
deliberately with the final full run rather than done piecemeal.

#### Checked: the added `!oom_ref` read does not reach the C

Step (g) reads `oom_ref` purely to name the flag for a lemma, which raises the question
of whether it costs a load per skipped no-scan block (~31 000 per compilation unit, by
the instrumented count in section 1). It does not. The Pulse `scan_loop` already
contains five such ghost-only reads — `GC.Gen.Impl.Cheney.fst:762, 821, 823, 837, 853`
— and the corresponding C function in the current snapshot
(`generational/snapshot/GC_Gen_Impl.c:913-1105`) contains **no** reads of `oom_ref`
at all, only the two `*oom_ref = true;` writes. KaRaMeL drops reads whose results are
used only in erased positions. The sixth read behaves the same way.

So no reshaping was needed. The alternative considered and dropped was to restate the
lemma with the OOM flag as an implication in the `ensures`
(`scanned_prefix_closed minor cs scan ==> scanned_prefix_closed minor cs (scan+1)`),
which needs no flag value at all; it would have been slightly cleaner but costs another
`CheneyBFS.fsti` signature change and hence another full-tree rebuild, for no effect on
the generated code. Recorded in case someone later wonders why the read is there.
