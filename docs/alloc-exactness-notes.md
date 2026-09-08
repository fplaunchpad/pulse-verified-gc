# Allocator size-exactness: investigation notes

Working notes for retiring hand patch 17 (`generational/patches/snapshot/0001-alloc-exact-wosize.patch`,
on branch `native`, marked `UNVERIFIED`) by fixing the F* source instead.

Status: **Steps 0 and 1 complete, no code changed yet.** Branch `alloc-exactness`, off
`main` (`8bd4559`); toolchain on the pinned F* nightly-2026-08-15.

Baseline is green and cached: root `gmake -j16` — 105 modules, 0 errors, 0 Warning 247,
190 `.checked`; `gmake -C spot` — 26 modules, 0 errors. The only "admits" are 36
`Interface X is admitted without an implementation`, the normal F*/Pulse interface-stub
pattern (library modules plus `GC.Spec.ZeroAddr`, `GC.Impl.ArrayWord`). **No proof admits
in the baseline** — so any that appear later are mine.

---

## 1. The bug, stated at the spec level

The allocator may hand out a block declaring **one word more** than requested. This is not
an implementation slip — it is a proved theorem.

`generational/spec/GC.Gen.AllocProps.fst:125` `alloc_from_block_wosize_lemma`:

```fstar
  : Lemma (requires U64.v (getWosize hdr) >= wz)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    U64.v (wosize_of_object obj g') >= wz /\
                    U64.v (wosize_of_object obj g') <= wz + 1))
```

Source, `mark-and-sweep/spec/GC.Spec.Allocator.fsti:85` `alloc_from_block`, terminal branch
(`:122-127`):

```fstar
    else begin
      // Exact fit (or leftover = 1, use whole block)
      let alloc_hdr = make_header (U64.uint_to_t block_wz) white_bits 0UL in
```

`block_wz`, not `requested_wz`. The `leftover >= 2` guard above it is forced by the
free-list representation: a *linked* free block needs a header **plus a body word** for the
link (`rem_field = rem_hd + 8` ← `next_fp`), so a 1-word remainder cannot be a cell.

### Why the F* argument is sound and still wrong

Promotion compensates by zeroing the extra word (`zero_promote_padding`,
`GC.Gen.Promote.fsti:77`, writes literal `0UL`), and the spec's own traversals are happy:
`is_pointer` (`GC_Gen_Impl.c:167`) is a range check, `v >= zero_addr + 8`, so `is_pointer(0)`
is **false** — the verified collector skips the word.

OCaml disagrees. `Is_block(x)` is `((x) & 1) == 0` (`mlvalues.h:71`), so `0` is
pointer-shaped, and specifically NULL. The two predicates disagree *exactly* on the value
the spec chose as filler:

| | `is_pointer(0)` | `Is_block(0)` |
|---|---|---|
| verdict | false — skipped | true — followed to NULL |

`is_pointer(v) ⟹ Is_block(v)` (8-aligned implies even), never the converse. They answer
different questions: `Is_block` is about value *encoding*; `is_pointer` is about address
*classification*. Stock keeps these separate (`mlvalues.h` vs `address_class.h`) and
conjoins them at use sites — `caml_darken` is `if (Is_block(v) && Is_in_heap(v))`
(`major_gc.c:283`). So `is_pointer ≈ Is_block && Is_in_heap`, with alignment folded in.

`0` is uniquely bad: rejected by `is_pointer`, accepted by `Is_block`, and not a valid
immediate either (`Val_long(x) = (x << 1) + 1`, so `Val_int(0) == 1`). Hence "0 is not a
representable OCaml value".

### What actually crashes — no GC traversal required

The dominant mechanism is not a traversal at all. The size is **program-visible**:

```c
/* array.c:39 */  return Wosize_val(array);                                     // Array.length
/* array.c:56 */  if (idx < 0 || idx >= Wosize_val(array)) caml_array_bound_error();
```

Both read the header, so the bounds check is computed from the same inflated size — the
safety net is defeated by the same lie. Then `stdlib/hashtbl.ml:355` (and `:504`):

```ocaml
(H.hash h.seed key) land (Array.length h.data - 1)
```

valid only for a power-of-two length, which `Hashtbl` guarantees by construction. Declare a
`2^n` bucket array as `2^n + 1` and the mask becomes `2^n`, so the index can *be* `2^n`: in
bounds per the header, past the real payload. It reads the phantom `0`, matches it as a
`Cons` block, and dereferences `0 - 8`. That is the `ast-invariants` SIGSEGV, and
`ocamlcommon` is full of `Hashtbl`s.

Secondary (live, but not what surfaced it): stock structural traversals take
`len = Wosize_val(v)` and iterate every field — `compare.c:282-283`, `hash.c:266,289`. We
replaced the collector, not the rest of the runtime.

**Correction to a claim in `PATCHES.md`:** it lists "the collector's own field scan" among
the things that dereference the phantom word. That is wrong — `is_pointer(0)` is false, so
the verified collector is the one reader that is immune.

**Rejected shortcut (already tried):** writing `Val_long(0)` = `1` into the pad instead of
`0`. Per `native:generational/PATCHES.md`, it appeared to fix native only because `1` is
`Hashtbl`'s `Empty`, so the phantom bucket read as empty by luck; bytecode still crashed and
a poison pad (`Val_long(0xBAD)`) showed the interpreter reading padding as data. *The size,
not the pad value, is the bug.*

---

## 2. What stock OCaml does — the model we adopt

`runtime/freelist.c:113` `nf_allocate_block`, three cases; case 1 is ours:

> *"The free block is 1 word longer than the requested size. Detach the block from the free
> list. The remaining word cannot be linked: turn it into an empty block (header only), and
> return the rest."*

implemented as `Hd_op (cur) = Make_header (0, 0, Caml_white)`.

Two details that matter:

- The fragment is **white**, not blue. That is deliberate: it routes the word into
  `case Caml_white: caml_fl_merge_block(...)` in the sweeper (`major_gc.c:883-930`), which
  is how stock reclaims it.
- Stock **right-justifies**: `return &Field (cur, Wosize_hd (h) - wh_sz)`. The blue block
  shrinks in place, keeping its address *and* its link, so the free list is never touched on
  a split.

Stock also debits `caml_fl_cur_wsz` by the whole block, i.e. the fragment word is
explicitly accounted as *not free*. The verified spec has no analogue of that counter.

Best-fit merge (`freelist.c:1636-1703`) absorbs a wosize-0 white block size-agnostically
(`wosz = Wosize_whsize(cur - start)`), and when a whole run is one word it does exactly what
verified `flush_blue` does — header, no insert — except stock writes white.

---

## 3. Reclamation is already proved (no coalescer change needed)

This was the open question ("does the coalescing spec claim the word back?"). Answer: yes,
structurally, and it is wosize-agnostic.

- `fused_aux` (`mark-and-sweep/spec/GC.Spec.SweepCoalesce.Defs.fst:30`) branches on
  `is_black obj g0` vs **everything else**, so a wosize-0 fragment is accumulated like any
  garbage block regardless of its colour: `fused_aux g0 g rest new_fb (rw + ws + 1) fp`.
- Run geometry, `GC.Spec.Coalesce.fst:862`:
  `first_blue - mword + run_words * mword == start`. The accumulate branch adds `ws + 1`
  while the walk advances `(ws+1)*8`, so it is preserved for **any** `ws`, including `0`.
  Same invariant in the Pulse loop, `GC.Impl.FusedSweepCoalesce.fst:110-116`.
- Conservation is `walk_end`-shaped, not a size sum. `coalesce_dense`
  (`GC.Spec.Coalesce.Dense.fst:251`); helper `merged_block_walk_end` (`:36`) takes
  `run_words: pos`, so run_words = 1 is in scope. Wired into
  `GC.Gen.PostCollectionShape.fst:183`. There is no `caml_fl_cur_wsz` analogue anywhere in
  the repo.
- `objects` (`common/spec/GC.Spec.Fields.fst:185`) puts no lower bound on `wz` — a wosize-0
  block advances exactly 8 bytes and is enumerated normally.

What is *missing* is a citable lemma, not a proof. Plan step 5.

### Colour of the fragment: blue, not white (corrected)

Initially recommended **white**, following stock literally. That is wrong for this codebase.
Make the fragment **blue**.

`flush_blue` (`GC.Spec.Coalesce.fst:75-88`) already *specifies* exactly this shape — it
writes `makeHeader wz_u64 Blue 0UL` unconditionally and the `if wz >= 1` guard then skips
the link write, returning `(g1, fp)` (note `fp` unchanged: the block is not even made the
list head):

```fstar
        let hdr = makeHeader wz_u64 Blue 0UL in
        let g1 = write_word g hd hdr in
        if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
          ... set_field g1 fb 1UL fp ...
        end
        else
          (g1, fp)          // wz = 0: blue header, never linked
```

It is deliberate, not incidental: `flush_blue_impl_wz0`
(`GC.Impl.Coalesce.Lemmas.fsti:93`) is a named bridge lemma for exactly this case, one of
three siblings alongside `_wz1`, concluding `flush_blue g fb 1 fp == (g1, fp)`.

**But the branch is currently unreachable — do not overstate this.** `fused_aux`
accumulates `rw + ws + 1`, so `run_words = 1` requires exactly one accumulated block with
`ws = 0`, and nothing today creates an *enumerated* wosize-0 block: grepping
`makeHeader 0UL` / `make_header 0UL` across the tree returns only that bridge lemma and the
new allocator code. So the shape is specified, with proof scaffolding and a documented
rationale, but dead. Our change makes an anticipated branch live rather than inventing a new
shape — which is worth something, but less than "already produced".

(0UL headers *do* already exist in the heap, as interior words of large blocks —
`SweepInv.fst:62` calls them "phantom wosize-0 objects not in the global enumeration". They
are never walked as blocks because they are not in `objects zero_addr g`.)

| | **blue** | white (stock's literal choice) |
|---|---|---|
| `alloc_spec_new_objects_blue_part1` (+3 consumers) | preserved | **broken** |
| `major_gc_unreachable_final_blue` (`Correctness.fsti:417`) | satisfied | at risk |
| `fl_valid` / `fl_cell` (require wosize ≥ 1) | not a cell, unaffected | unaffected |
| reclaimed by `fused_aux` (non-black ⇒ accumulated) | yes | yes |
| `no_pointer_to_blue` (`Mark.fsti:233`) | vacuous — nothing points at a fragment | vacuous |
| shape already produced here | yes (`flush_blue`) | novel |

The decisive constraint — and the leg the choice actually rests on, since the `flush_blue`
argument above is about specification rather than behaviour — is
`alloc_spec_new_objects_blue_part1` (`GC.Spec.Allocator.Lemmas.fsti:314`): *every* object
created by allocation is blue.
A white fragment falsifies it, taking down its three consumers
(`GC.Gen.CheneyPreservation.fst:484`, `GC.Gen.PromoteUpdate.BlueProm.fst:495`,
`GC.Gen.CheneyPreservation.NonBlueOrigin.fst:273`).

**A third argument for blue: it keeps `sweep_object`'s latent bug latent.** `sweep_object`
(`GC.Spec.Sweep.fsti:39-50`) dispatches `is_infix` -> `is_white` -> `is_black` -> fall-through,
and colours are mutually exclusive. A **blue** fragment is none of the first three, so it
lands in the final `else (g, fp)`: untouched, `fp` unchanged. It never reaches the white
branch where the `ws = 0` hazard lives.

A **white** fragment would hit that branch exactly: the link write is skipped
(`if U64.v ws > 0` fails) yet the block is still returned as the new `fp`, so the entire
existing free list is dropped and `fl_next` on the new head reads `hd + 8`, which for a
wosize-0 block is the *next block's header*. White would therefore turn an unreachable
defect into a live one **inside the spec's own model** -- not vacuity, but a genuinely wrong
free list.

So blue costs only vacuity of the (unconsumed) sweep-exactness theorems, via `fl_complete`
(every blue object is a cell -- the unlinked fragment is a direct counterexample) and
`linkable_heap` (violated whatever the colour). `fl_sound` survives either way, since it
quantifies over cells and the fragment is not one.

Why stock differs: its sweeper dispatches on colour
(`major_gc.c:883` `case Caml_white: caml_fl_merge_block(...)`), so white is *how* stock
routes the fragment to reclamation. `fused_aux` dispatches on `is_black` vs everything-else,
so blue is reclaimed identically. Different mechanism, so the colour need not match — we
match stock's *handling* (an empty header-only block), not its colour.

Do not change `flush_blue`'s colour either.

---

## 4. What mark-and-sweep fails to handle at wosize 0

All three in `sweep_object`'s white branch (`mark-and-sweep/spec/GC.Spec.Sweep.fsti:39-50`).
This is precisely what `linkable_heap` exists to exclude.

1. **Blue but not a cell.** `makeBlue obj g'` runs unconditionally while the link write is
   guarded by `if U64.v ws > 0 && …`. So the block is blue with an unwritten link.
   `fl_cell` requires blue ∧ wosize≥1 → blue-yet-not-a-cell → falsifies `fl_complete`.
2. **The existing free list is dropped.** It returns `(g'', obj)` regardless, so `obj`
   becomes the head without ever receiving the incoming `fp`; everything already on the list
   becomes unreachable.
3. **A header is followed as a link.** `fl_next g a = read_word g a`
   (`GC.Spec.FreeList.fst:42`), and the link is written by `set_field g obj 1UL fp` →
   `hd_address(obj) + mword*1` = `obj` itself. For a wosize-0 block, spanning only
   `[hd, hd+8)`, that word **is the next block's header**.

**None of it is reachable.** Verified:
- Nothing consumes `snd (sweep …)`. The only three references repo-wide are proof-internal:
  `GC.Spec.FreeList.Sweep.fst:93,149` (asserts) and `GC.Spec.Sweep.fst:692`.
- Every composed theorem uses `Coalesce.coalesce (fst (sweep h_mark fp))`
  (`GC.Spec.Correctness.fsti:313,466,476,486,500,506`) — heap only, free pointer discarded —
  and `coalesce` restarts from `0UL`.
- The shipped pipeline is `fused_sweep_coalesce` (`mark-and-sweep/impl/GC.Impl.fst:87`),
  with a bridge lemma proving `fused_sweep_coalesce == coalesce (fst (sweep …))`.
  `sweep_object` does not appear in extracted C at all (`grep` on
  `generational/snapshot/GC_Gen_Impl.c`: 0 hits; the only sweeper is
  `fused_sweep_coalesce` at `:251`).

So `GC.Spec.Sweep.sweep` is reference semantics for an equivalence proof, not shipped code.
Weakening `linkable_heap` **cannot introduce a runtime bug**; the exposure is re-proving a
leaf module. `GC.Spec.FreeList.fst` is imported by nothing (only the weaker
`.Descending` is), and `fl_exact` / `sweep_preserves_fl_exact` are not consumed by
`GC.Spec.Correctness` or anything under `impl/`.

Separate follow-up, not in scope here: fix `sweep_object` to not return an unlinked head.

---

## 4b. Step 1 result — `linkable_heap` is assumed, never established

Machine-checked on the clean baseline. `linkable_heap` is:

- **defined** at `GC.Spec.FreeList.fst:140`
- a **hypothesis** at `GC.Spec.FreeList.fst:147` (`linkable_is_fl_node`) and at all ten
  `GC.Spec.FreeList.Sweep.fst` sites (`:34,60,84,141,189,205,235,262,285`)
- **concluded** in exactly one place, `sweep_object_preserves_linkable`
  (`FreeList.Sweep.fst:207`) — which is *preservation*, not establishment

Nothing derives it from `well_formed_heap` or from any concrete heap, and
`fl_exact` / `sweep_preserves_fl_exact` / `sweep_establishes_fl_exact` have **no consumers
outside the leaf** (grep confirms). So:

> **The change breaks no proof.** It makes `linkable_heap` false of heaps the real allocator
> produces, which makes the sweep-exactness theorems *vacuous* for those heaps. That is a
> meaningfulness problem, not a build failure — the hypothesis is never discharged anywhere,
> so nothing fails to typecheck.

That reframes Step 1 from "repair 12 broken proofs" to "keep a leaf theorem meaningful".

### The weakening a *blue* fragment needs (correcting the plan)

The plan said "restrict `linkable_heap` to blue objects". **That does not work now that the
fragment is blue** — it is blue with wosize 0, so it still violates the restricted form.

For a blue fragment, two predicates in the same leaf file need to change:

| predicate | current | needed |
|---|---|---|
| `linkable_heap` (`FreeList.fst:140`) | every *object* has wosize ≥ 1 | every *free-list cell* has wosize ≥ 1 |
| `fl_complete` (`FreeList.fst:~124`) | blue ⟹ on the chain | blue **∧ wosize ≥ 1** ⟹ on the chain |

`fl_complete` must move too, because a blue-but-unlinked fragment is a direct
counterexample to "every blue object is a cell". `fl_cell`
(`FreeList.Descending.fsti:39`) already carries the `wosize >= 1` conjunct, so the
restricted forms are consistent with what the allocator side already assumes
(`fl_valid_gives_wosize`).

Contrast, for the record:

| | blue fragment | white fragment |
|---|---|---|
| `linkable_heap` | weaken to cells | weaken to blue objects |
| `fl_complete` | weaken to wosize ≥ 1 | unchanged |
| `alloc_spec_new_objects_blue_part1` + 3 live consumers | **untouched** | **broken** |
| where breakage lands | entirely in the dead leaf | dead leaf **+ live Cheney/promotion proofs** |

Blue therefore remains the right choice: it confines every consequence to the unconsumed
leaf module. The reason is different from what I first wrote, though — not "blue keeps
`linkable_heap` satisfiable" (it does not), but "blue keeps the *live* proofs intact".

---

## 5. Design chosen: right-justify, as stock does

Let `hd = hd_address obj`, `leftover = block_wz - requested_wz`.

| | remainder at `hd` | allocated header | free list |
|---|---|---|---|
| `leftover = 0` | none | `hd`, wosize `wz` | block detached |
| `leftover = 1` | wosize 0, **blue**, unlinked | `hd + 8`, wosize `wz` | block detached |
| `leftover >= 2` | wosize `leftover - 1`, blue, link untouched | `hd + leftover*8`, wosize `wz` | **unchanged** |

One uniform formula covers all three: `obj_out = f_address (hd + leftover * 8)`.

Why this over patch 17's "fragment after the object": for `leftover >= 2` the blue block
keeps its address and link, so `alloc_spec_preserves_fl_valid_part1` /
`_fl_chain_terminates_part1` (`GC.Spec.Allocator.Lemmas.fsti:209,217`) become near-trivial,
the "a new object appeared" reasoning in `alloc_from_block_rem_in_objects_part1` /
`alloc_from_block_objects_backward_part1` disappears, and `fl_descending` holds trivially.

**Ruled out:** making leftover=1 a split with a wosize-0 **blue** remainder. `alloc_spec`'s
`fp_out` would *be* that remainder, so `fl_valid r.heap_out r.fp_out` is flatly false —
`fl_valid` (`GC.Spec.Allocator.Lemmas.Common.fst:15`) requires `wosize >= 1` of every cell.

---

## 6. Step 0 results — build re-verifiability

**Stale `.checked` files are NOT inert — delete them before building.** This was my first
conclusion and it was wrong. They do not get *used*, but F* still finds them along the
`--include` paths, judges them corrupt (they were emitted by a different F* and so carry a
different cache version), and that **blocks writing the new cache**. The first cold build
reported, once per module:

```
* Warning 247 at generational/spec/GC.Gen.PostCollectionShape.fst(0,0-0,0):
  - Checked file _cache/GC.Gen.PostCollectionShape.fst.checked was not written.
  - Reason: checked file generational/spec/GC.Gen.FreeListShape.fsti.checked is corrupt
```

Verification still *succeeded* (exit 0, "all modules verified") — but `_cache/` stayed
empty, so every subsequent build would be a full cold re-verify. For a change touching 172
modules in the allocator's closure, that is the difference between an iterable loop and an
unusable one.

**And `.depend` must go with them, in that order.** Deleting the `.checked` files alone is
not enough. `.depend` is keyed on sources only (`Makefile:124`), so removing build artifacts
does not invalidate it — and the copy generated during the first build had *mixed layouts*:
the target in `_cache/`, the prerequisites in the old per-directory paths, because F* points
a dependency at wherever it found an existing checked file.

```make
_cache/GC.Spec.FreeList.fst.checked: \
	mark-and-sweep/spec/GC.Spec.FreeList.fst \
	common/spec/GC.Spec.Fields.fst.checked \     # old layout -- never created again
	common/spec/GC.Spec.Base.fsti.checked
```

With those prerequisites gone and no rule to remake them, the ordering collapsed and
Warning 247 came back with a new reason — `checked file _cache/GC.Spec.Base.fsti.checked
does not exist` — so still nothing cached.

Full recipe, once:

```sh
find . -path ./fstar -prune -o -path ./_cache -prune -o \
       \( -name '*.checked' -o -name '*.checked.lax' \) -print0 | xargs -0 rm -f
rm -f .depend generational/.depend mark-and-sweep/.depend spot/.depend
gmake -j$(nproc)
```

224 stale `.checked`, all matched by `.gitignore:1`, none tracked. Do **not** touch
`fstar/`'s own 1151 `.checked` files — those are the toolchain's — and leave the `.depend`
files under `generational/ocaml-integration/ocaml-4.14-*/`, which are OCaml's own.

After this: Warning 247 count **0**, `.depend` consistently `_cache/`-rooted, and the cache
populates normally.

The rest of the original finding stands, and explains why deleting them is safe:

- The build writes `.checked` into `$(CACHE_DIR)` = `_cache` (`Makefile:47,175,189,215`).
- Every existing `.checked` sits *next to its source* — the old per-directory layout — so
  the current build ignores all of them.
- `_cache/` does not exist, so a build starts cold and regenerates everything.
- Zero `.checked` are tracked by git; `.gitignore:1` covers `*.checked`, `:26` covers
  `_cache/`.
- The committed `.depend` is untracked, mtime **Aug 24**, while the newest sources are
  **Aug 31**, and it references modules whose sources no longer exist. It is stale and gets
  regenerated by the `--dep full` scan.

**Toolchain mismatch — needs a decision before verifying.**

| | pinned | local |
|---|---|---|
| F* | nightly-**2026-08-15** (`setup.sh:28`, `verify.yml` cache key) | **2026.05.17** (`fstar/version.txt`) |
| Z3 | 4.15.3 | `fstar/lib/fstar/z3-4.15.3/` present |
| cache | `_cache/` | absent |

`setup.sh:68-78` compares versions and on mismatch does `rm -rf "$FSTAR_DIR"` and
reinstalls — so running it **destroys the working local F* install** and re-downloads.
`.checked` cache version differs between the two (nightly-2026-08-15 emits version 89), so
old artifacts are unusable regardless.

Also note: `which fstar.exe` resolves to `~/.local/bin/fstar.exe`, a different install. The
Makefiles ignore `PATH` and use `$(CURDIR)/fstar` / `../fstar`, so that one is not in play.

Use `gmake`, not `make` — the Makefile uses `private` on a target-specific variable,
needing GNU Make ≥ 3.82.

---

## 7. Cost and coupling

- **172 `.checked` files** in the allocator's reverse-dependency closure.
- `GC.Spec.Allocator` is the worst cost-per-line in the repo: **188 lines, 370 s**
  (`PROOF_COMPLEXITY.md:294`). Needs `smt.qi.eager_threshold 100` or it hangs >15 min
  (`Makefile:26-38`).
- `GC.Spec.Allocator.Lemmas.Part2.fst` is **3,381 lines**, a 2 (split vs exact) × 3 × 7
  product of ~30 hand-written inductions, with measured >90 min hangs under Z3 4.15.3
  (`Makefile:66-79`). **The split-vs-exact axis is exactly what changes** — this is the
  schedule risk; size it first.
- `alloc_from_block_exact` (`GC.Spec.Allocator.fsti:290`) is the one lemma whose *statement*
  changes shape: **32 call sites**, 19 of them in `Lemmas.Part2.fst`.
- **118** case-split sites on `leftover` vs `2`, across 11 files.
- Full verify ~12-13 min on 24 cores warm (`PROOF_COMPLEXITY.md:1266`); CI is multi-hour
  (360 min timeout). `--retry 3` is on by default and hides instability — re-run before
  concluding a change is green.

**Coupling with `origin/sheera/coalesce-exact`** (active, last commit 2026-09-04, 4 admits).
Its walk-invariant clause 5, `run_words > 0 ==> run_words >= 2`, exists specifically to
*rule out the wosize-0 flush*, and derives from `linkable_heap`. Its admitted
`flush_preserves_linkable` is directly affected. This is the one item needing another
person's agreement rather than just proof effort.

---

## 8. Payoff beyond the crash fix

Exact allocation makes `promote_object_extra_field_not_pointer` (`GC.Gen.Promote.fsti:499`)
**vacuous** — `field_idx >= wz /\ field_idx < wosize` becomes unsatisfiable. That retires:

- `zero_promote_padding` and its 9 lemmas (`GC.Gen.Promote.fsti:150,156,161,167,175,181,191,
  231,247`); the two largest have 26 and 19 call sites.
- 3 padding-only private helpers (`Cheney.Dense.fst:233`, `CheneyPreservation.fst:130,601`).
- Pulse `zero_padding_step` (`generational/impl/GC.Gen.Impl.Promote.fst:182`, called `:306`,
  `inline_for_extraction` → 7 copies in the C).
- The whole `fwd_target_extra_fields_state` chain
  (`CheneyPreservation.Fields.fst:917-1136`) and its 5 consumers.

It also closes half of the documented "Known gap" in
`.github/copilot-instructions.md:216-219` — *"objects grows by exactly the remainder"* — by
forcing `alloc_from_block_exact_objects_eq_part1` (`GC.Gen.AllocProps.fst:780`) to be
restated as a case split (it is **false as stated** once `leftover = 1` adds a fragment).

---

## 9. Docs that are now wrong and need updating

- `DESIGN_AND_IMPL.md` (~lines 990-1005) documents the over-allocation as correct-by-design
  and describes `zero_promote_padding` as load-bearing. Blob `334b7525`, **byte-identical on
  `ci`, `native-integration`, `native`, `main` and `msr/main`** — so even `native`, which
  carries patch 17, contradicts its own design doc.
- `generational/PATCHES.md` patch 17 section: the "collector's own field scan" claim (see §1)
  and, once this lands, the whole section becomes closed rather than OPEN.

---

## 10. Step 2 progress — the root module is done

`GC.Spec.Allocator.{fsti,fst}` both verify with the right-justified definition.

**`GC.Spec.Allocator.fst`: OK in 20.8 s.** `PROOF_COMPLEXITY.md:294` records the previous
definition at **369.5 s** for 188 lines — the worst cost-per-line in the repository. The new
geometry is ~18x cheaper because the split case performs two writes instead of three (the
remainder keeps its link, so there is no third write) and the two high-end bounds cases
disappear. If that holds downstream it materially changes the cost estimate for this work.

### Changes that were not in the plan

- **`alloc_from_block_exact` had to split in two.** It covered `leftover < 2`, and those two
  cases now differ. Narrowed to `leftover = 0`; new `alloc_from_block_frag` covers
  `leftover = 1`. Its 32 call sites each sit in an `if bwz - wz < 2` arm and must now
  dispatch on 0 vs 1.
- **The two `_oob` lemmas collapsed into one.** `_split_rem_hd_oob` / `_split_rem_obj_oob`
  existed only because the remainder sat at the high end and could run past `heap_size`.
  With the remainder at `hd` there is a single way to fail — the object header — so
  `alloc_from_block_oob` replaces both. 17 call sites in `GC.Gen.AllocProps.fst` and
  `GC.Gen.PromoteUpdate.BlueAlloc.fst` need rewriting.
- **`alloc_split_normal_read_rem_field` changed meaning.** It used to say the fresh
  remainder's field was set to `next`. The remainder now keeps `hd` and its link at `hd + 8`
  is never written, so it is a *preservation* fact: `read_word g' obj == read_word g obj`.
  This is what makes the free list bit-identical across a split.
- **`alloc_split_normal_pre` lost a conjunct** — only `hd + leftover * 8 < heap_size` is
  needed now, not the two old high-end bounds.
- **A `leftover < 0` guard was required.** `alloc_from_block` has no precondition tying
  `requested_wz <= block_wz`; the old code fell into the exact-fit arm harmlessly, but the
  new code computes `hd + leftover * 8` and needs non-negativity to typecheck. Defensive
  arm returns `(g, next_fp)`; `alloc_search` and every unfolding lemma establish
  `bwz >= wz`, so it is unreachable.

### Measured iteration cost

`tools/try-module.sh <mod> --z3smtopt '(set-option :smt.qi.eager_threshold 100)'` — the
eager-QI flag is mandatory for this module (`Makefile:26-38`; without it, >15 min hang).
A *failing* run costs 130-410 s because `--retry 3` retries; a passing one is 20 s.

---

## 11. Downstream fallout — measured, and much smaller than feared

Full `gmake -k RETRY= -j16` after the root change. **6 modules reported errors, 12 lines
total** — and `GC.Spec.Allocator.Lemmas.Part2.fst`, the 3,381-line schedule risk, showed
only **2**.

| module | errors | note |
|---|---|---|
| `GC.Spec.Allocator.Lemmas.Core.fst` | 3 | exact-fit arm |
| `GC.Gen.AllocProps.fst` | 3 | all at one lemma (61,2-77,5) |
| `GC.Spec.Allocator.Lemmas.Part2.fst` | 2 | exact-fit arm (432-463) |
| `GC.Gen.MinorCollectForwarding.fst` | 2 | **flake — see below** |
| `GC.Spec.Allocator.Lemmas.Part1.fst` | 1 | 147-177 |
| `GC.Impl.Allocator.fst` | 1 | the Pulse impl |

**`RETRY=` produces false failures.** `MinorCollectForwarding.fst` reported two
`FStar.UInt.size (src + x * 8) 64` overflow obligations under `RETRY=`, and passes cleanly
(**OK 75.6 s**) with `--retry 3` restored. Use `RETRY=` only to *enumerate* the frontier,
never to judge whether a module is fixed. Real list: **5 modules**.

Caveat: `make -k` cannot build anything whose prerequisites failed, so 32 of 105 modules
verified and the rest were skipped. More may surface behind these five.

### The recurring repair, and where it snags

Every failure is the same shape: an `else` arm covering `leftover < 2`, which must now
dispatch on `leftover = 0` (one write at `hd`, `alloc_from_block_exact`) versus
`leftover = 1` (two writes — fragment at `hd`, object header at `obj` —
`alloc_from_block_frag`).

Applying that split to `Lemmas.Core.fst:120` took it from **3 errors to 1**. The survivor is
instructive: `alloc_from_block_frag`'s precondition `bwz - wz == 1`, which follows from
three enclosing branch conditions by pure linear arithmetic, **times out**.

- Asserting it explicitly does not help — the assert itself times out.
- Raising `--z3rlimit` 50 → 200 does not help either: the run goes 80 s → 335 s and still
  fails. That is a non-converging query, not an underfunded one — the pathology
  `Makefile:26-38` documents for Z3 4.15.3.
- The eager-QI flag is *not* the fix here: `Lemmas.Core.fst` is not in `EAGER_QI_CHECKED`
  (`Makefile:264`), so `tools/try-module.sh` with no extra flags already matches what the
  Makefile does. (`GC.Spec.Allocator.fst`, `Lemmas.Part2.fst` and `GC.Impl.Allocator.fst`
  *are* in that list and must be run with `$(EAGER_QI)`.)

Z3 is being swamped by the surrounding `alloc_search` invariant before it reaches a trivial
goal. The repo's own idiom for this is to extract the arm into a private helper lemma whose
context is small — which is what `alloc_exact_preserves_wfh_part1` and friends already do in
`Lemmas.Part2.fst`. That is the next step, and it is the shape the remaining four repairs
will most likely need too.
