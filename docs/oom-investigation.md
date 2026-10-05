# The binarytrees / count_change out-of-memory failure

Spike 3 (`spike/parallel/SPIKE.md`, "Programs") found that `binarytrees 10` in a
300,000-word major heap aborts with

```
verified gen GC: promotion failed — major heap full (2 MB)
Fatal error: verified gen GC: out of memory (major heap too small)
```

and that larger `count_change` runs fail the same way. It also does so without
the spike code. This note records why. Nothing was fixed.

## Answer

**There is no collector bug here. The heap is too small for the program's live
data.** The premise that "the live set is a few thousand words" is off by two
orders of magnitude. It is a few thousand *objects*, but every `binarytrees` node
carries a fresh 128-element array:

- `mk () = Array.make 128 (Some 0)` is 129 words (the `Some 0` is a shared
  constant), and the `Node` block is 4 words. So each node is 133 words.
- The stretch tree, depth 11, has 4,095 nodes, so **544,635 words** are live at
  once while `check (make stretch_depth)` runs. Measured: the first major
  collection in an 800k-word heap keeps **526,308 words**.
- A 300,000-word heap cannot hold that on any collector.

At every failing allocation, the free list holds all of the free memory. No free
block is stranded, so no lemma was violated.

| Question | Finding |
|---|---|
| 1. Does the built collector include the `sweep_object` fix and `coalesce_complete`? | **No.** Neither is in this branch, `main`, `origin/main` or `fork/main`. Both are in Akhil's unmerged series `fork/pr/1..7`, and both leave the extracted C byte-identical. Re-run against PR 6's extracted collector: same result. |
| 2. Does stock OCaml 4.14.2 pass? | It passes, but **not in 300,000 words.** Stock grows its heap, and it peaked at 1.3M–1.5M words for `binarytrees 10`. Stock 4.14 has no maximum-heap setting, so a run with the same fixed heap size cannot be done. Stock never peaked below the verified collector's minimum heap (table below). |
| 3. Free list against the heap at the failing allocation | Total free (blue) words **equal** the words reachable from the free list in every failing run and after every traced collection. Zero blocks are stranded. At the failure the heap is at least 99.99% white objects. |

## 1. Which collector is built

- `ocaml-4.14-verified-gen/runtime/verified_gc` is a symlink to
  `generational/ocaml-integration/verified_gc`. Its `libvergc_gen.a` is built
  from `generational/snapshot/GC_Gen_Impl.c` in this tree, which was last
  changed in 133ca96 (Spike 3's `#ifdef`, which is off in the default build).
  That runtime is the one that fails.
- `sheera/spike-parallel` branches from the local `main` at **04f6028
  (2026-05-11)**. **No commit by Akhil Tulluri is an ancestor of `HEAD`.**
  `git log --all -S coalesce_complete` finds the name only in 2365a34.
- The series is on the fork, unmerged as of this writing. It is not in
  `origin/main` (8874bd9) or `fork/main`:

  | Branch | Commit | Content |
  |---|---|---|
  | `fork/pr/1-sweep-object-orphan` | c979e2f | `sweep_object` must not make an unlinkable (wosize 0) block the list head |
  | `fork/pr/2-delete-linkable-heap` | e80dbaa | delete `linkable_heap`; weaken `fl_complete` to wosize ≥ 1 |
  | `fork/pr/4-right-justify-allocator` | f10a927 | right-justified allocation; **changes the extracted C** |
  | `fork/pr/6-coalesce-complete` | 2365a34 | `coalesce_complete`: the coalescer's free list is complete |

- c979e2f and 2365a34 each state "extracted C byte-identical". So on their own
  they cannot change runtime behaviour. PR 4 does change the C.
- **Control on PR 6.** The same diagnostic (below) was built against
  `fork/pr/6-coalesce-complete`'s extracted collector (`generational/snapshot`),
  linked with this branch's `alloc_gen.c` and runtime. That branch's
  `alloc_gen.c` adds native-code glue and needs its own runtime patch, so it
  was not used. The headers' API is identical.
  - It fails at the same points.
  - It has the same minimum heaps, to within the search's 1,000-word step.

## 2. Stock OCaml 4.14.2

`ocaml-4.14-unchanged` (tag `4.14.2`, the tree `make setup` builds) runs the same
`.byte` files. Stock has the same default minor heap, 256k words.

- Stock's `h=` sets only the *initial* major heap, and stock grows the heap from
  there. OCaml 4.14 has no option to cap it.
- So the requested comparison, with the same program and the same 300,000-word
  heap, cannot be run as stated. Stock's peak heap (`top_heap_words`, from
  `OCAMLRUNPARAM=v=0x400`) is compared instead against the smallest
  `MIN_EXPANSION_WORDSIZE` the verified runtime passes with. That minimum was
  found by bisection to within 1,000 words.

| Program | Verified: smallest passing heap (words) | Stock peak, `o=1` | Stock peak, `o=80` | Stock peak, default |
|---|---:|---:|---:|---:|
| `binarytrees 10` | 800,603 | 1,515,008 | 1,317,376 | 1,489,920 |
| `binarytrees 12` | 4,060,062 | 3,506,688 | 4,033,024 | — |
| `count_change 100` | 415,934 | 430,080 | 430,080 | — |
| `count_change 200` | 18,232,203 | 18,768,384 | 18,768,384 | — |

(Stock runs used `h=4096,a=2`, with `a=2` the best-fit policy, except the
default column, which uses `h=300000`. `binarytrees 12` with `o=1` also did one
forced major collection.)

- Every heap size spike 3 tried is below the verified minimum:
  - `binarytrees` 10, 12 and 14 at 300k, 1M and 3M words;
  - `count_change` 200 at 4M and 8M words, and `count_change` 300 at 20M words.
- Stock needs as much or more. The one case where stock's peak is lower is
  `binarytrees 12` at `o=1`, by 13%. Stock's peak heap is an upper bound on what
  it needs, not a minimum, so that is not evidence of a defect.

## 3. Free-list state at the failing allocation

### Method

A scratch copy of `GC_Gen_Impl.c` was made, with three definitions renamed,
`allocate`, `allocate_part1` (the allocator Cheney promotion uses) and `gen_gc`,
and wrapped. The wrapper code is in the appendix.

- **When it records.** On the first allocation that returns 0, after every
  collection that fails, and with `DIAG_EVERY_GC=1` after every major
  collection.
- **What it records.**
  - **The free list**, walked from `fp`, with cycle detection: length, words
    (whole size), largest block, and any non-blue or wosize-0 entries.
  - **The whole heap**, walked header by header from `zero_addr1` to
    `heap_size_u640`: number of blue blocks (the fragments), blue words,
    largest blue block, and adjacent blue pairs.
  - **Blue blocks not on the list**, and their words.
  - Totals for white, gray and black.
  - Whether the walk ends exactly at the heap's end.

The repo's sources were not modified. The build linked this tree's
`prims.o` and `libcamlrun.a` with Apple clang 12, on x86_64.

### Results: this branch's collector

| Run | Where it failed | Request (whsize) | FL length | FL words | Largest FL block | Blue blocks (fragments) | Blue words | **Blue not on FL** | White words |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `binarytrees 10`, 300k | promotion, major GC #2 | 129 | 1 | 128 | 128 | 1 | 128 | **0** | 299,872 |
| `binarytrees 12`, 1M | promotion, major GC #2 | 129 | 1 | 103 | 103 | 1 | 103 | **0** | 999,897 |
| `binarytrees 14`, 3M | promotion, major GC #2 | 129 | 1 | 46 | 46 | 1 | 46 | **0** | 2,999,954 |
| `count_change 100`, 300k | promotion, major GC #8 | 3 | 0 | 0 | 0 | 0 | 0 | **0** | 300,000 |
| `count_change 200`, 8M | promotion, minor GC after major GC #12 | 3 | 31 | 62 | 2 | 31 | 62 | **0** | 7,999,938 |
| `count_change 300`, 20M | promotion, minor GC after major GC #12 | 3 | 69 | 138 | 2 | 69 | 138 | **0** | 19,999,862 |

- **Every run.** Free words in the heap equal free-list words. There are no gray
  or black objects, no cycles, no non-blue list entries, no wosize-0 blocks, and
  every heap walk ends exactly at the end of the heap.
- **binarytrees.** The free list *is* the whole free space: one block, 46 to 128
  words, smaller than a 129-word array. The failure is not fragmentation.
- **count_change.** The free space is 31 and 69 two-word blocks, against a
  three-word request. Here fragmentation decides which allocation fails, but the
  free space totals 62 words of 8M (0.0008%), so it cannot be what makes the
  heap too small.
- **The two count_change 200/300 runs** failed in a plain minor collection
  (`do_minor_gc_core`), not inside `gen_gc`. That is why they have no
  "after major GC" line.

### Why the live data does not fit

`DIAG_EVERY_GC=1` traces show white words after each sweep, which is the data
that survived marking:

- **`count_change 100`, 300k heap.**
  - The survivors grow by about 41k words every collection: 46,962, 88,436, …,
    293,247 after #7, leaving 6,753 free.
  - The promotion in #8 then has nowhere to go.
  - The program accumulates its result list (`acc`), so all of that data is
    live.
  - In a 420k heap it finishes with 414,843 live words after #10, which matches
    the 415,934-word minimum.
- **`count_change 200`, 8M heap.** 7,788,786 words survive #12, so the heap is
  97% live when it fails.
- **`binarytrees 10`, 300k heap.**
  - #1 keeps all 264,165 words it promoted, which leaves one 35,835-word block.
  - #2 must promote up to 262,143 more words of the still-growing stretch tree.
- **`binarytrees 10`, 800,603-word heap (the minimum).**
  - #1 keeps 526,308 words, and later collections keep 278k–443k.
  - The minimum is about the peak live data plus one minor heap (526,308 +
    262,144 = 788,452).
  - The reason: `gen_gc` runs `minor_collect_full` (promotion into the major
    heap) **before** `collect_with_roots` (mark and sweep). The major heap must
    therefore hold the last collection's survivors, plus everything promoted
    since, plus the minor heap's survivors, all at once. This is the design
    (`generational/snapshot/GC_Gen_Impl.c`, `gen_gc`), not a bug.

  The abort's hint, "Set MIN_EXPANSION_WORDSIZE=600000", is only a doubling
  heuristic (`fatal_promotion_failed` in `alloc_gen.c`). For `binarytrees 10`
  it is too small.

In every trace on this branch's collector, at every collection, `blue not on FL`
was 0.

### Results: PR 6's collector (right-justified allocator)

- **Same failure points, same minimum heaps.** `binarytrees 10`: 800,603 words.
  `count_change 100`: 415,934 words.
- **One difference: one-word blue fragments (wosize 0) that are not on the
  list.**
  - 115 words at the `count_change 100` failure, and 6,877 of 8M words at the
    `count_change 200` failure.
  - In a 420k heap they build up slowly: 0, 0, 19, 32, …, 166 words after
    collections 1 to 10.
- **This is the intended behaviour, not a stranded block.**
  - On PR 6, `fl_complete` covers only blue objects with wosize ≥ 1.
  - 2365a34 describes the wosize-0 fragment as "free space that is deliberately
    not a cell". A one-word block cannot hold any object, because the smallest
    request is two words (whsize 2), so it reduces no allocation's chances.
  - This branch's allocator never produces such fragments (0 observed). When
    the leftover would be under two words, it gives the whole block to the
    object instead.

## For the proofs

**No stranded block was found, so no lemma was contradicted.** It is still worth
recording which statement covers this, because on this branch that statement is
assumed, not proved.

- **The property checked**, at each observation point: every blue object is
  reachable from `fp`. That is `GC.Spec.FreeList.fl_complete`
  (`mark-and-sweep/spec/GC.Spec.FreeList.fst:125`).
- **On this branch, nothing proves `fl_complete` about any heap the collector
  produces.**
  - It appears only inside `fl_exact` (line 131), and that only as a hypothesis
    of the `GC.Spec.FreeList.Sweep` preservation lemmas.
  - Those lemmas also assume `linkable_heap`.
  - c979e2f and 2365a34 explain why both assumptions are a gap. On this branch's
    unweakened form, a wosize-0 fragment is a counterexample.
- **Had free memory been missing from the list after a sweep, the lemma that
  should have ruled it out is `coalesce_complete`** (PR 6,
  `mark-and-sweep/spec/GC.Spec.Coalesce.Complete.fst`):

  ```
  coalesce_complete (g: heap)
    : Lemma (requires post_sweep g)
            (ensures (let r = coalesce g in FL.fl_complete (fst r) (snd r)))
  ```

  Together with `coalesce_fl_entry` (the chain holds only cells and ends), it
  gives free-list exactness for what `fused_sweep_coalesce` returns, through
  the byte-equality bridge `GC.Spec.SweepCoalesce`.
- **Stranding during allocation or promotion is a separate obligation.** A
  free block could also be dropped between collections, by `allocate` or
  `allocate_part1` splitting a block.
  - That needs a lemma that allocation preserves `fl_exact`. No such lemma
    exists, on this branch or in the series: `fl_exact` and `fl_complete` occur
    only in `GC.Spec.FreeList`, `GC.Spec.FreeList.Sweep` and (on PR 5)
    `GC.Spec.Partition`.
  - The nearest statement is PR 5's `alloc_from_block_accounting`
    (`fork/pr/5-exactness-and-accounting`, 23c2d8a). It conserves words in a
    split but says nothing about the list.
  - The checks at the failing allocations cover this path, and found nothing.
- **What the measurements give the proofs:** on this branch's collector, the
  property `coalesce_complete` states (in its unweakened form, since no wosize-0
  fragments occur) held empirically after every traced collection.

## Reproducing

1. **Reproduce the failure**, from `generational/ocaml-integration/tests` after
   `make setup`:

   ```sh
   MIN_EXPANSION_WORDSIZE=300000 ../ocaml-4.14-verified-gen/runtime/ocamlrun binarytrees.byte 10
   ```

2. **Stock comparison:**

   ```sh
   OCAMLRUNPARAM='h=4096,o=1,a=2,v=0x400' ../ocaml-4.14-unchanged/runtime/ocamlrun binarytrees.byte 10
   ```

3. **Diagnostic runtime.** Make a copy of `GC_Gen_Impl.c` with three
   definitions renamed:

   ```sh
   sed -e 's/^K___uint64_t_uint64_t allocate(heap_t heap, uint64_t fp, uint64_t wosize)$/K___uint64_t_uint64_t allocate_real(heap_t heap, uint64_t fp, uint64_t wosize)/' \
       -e 's/^K___uint64_t_uint64_t allocate_part1(heap_t heap, uint64_t fp, uint64_t wosize)$/K___uint64_t_uint64_t allocate_part1_real(heap_t heap, uint64_t fp, uint64_t wosize)/' \
       -e 's/^gen_gc($/gen_gc_real(/' generational/snapshot/GC_Gen_Impl.c > GC_Gen_Impl_diag.c
   cat appendix.c >> GC_Gen_Impl_diag.c       # the code below
   ```

   Build it like `spike/parallel/build_sweep.sh`'s plain build, with
   `GC_Gen_Impl_diag.c` in place of `GC_Gen_Impl.c` and without the probe
   files. Then run with `MIN_EXPANSION_WORDSIZE=<words>`, and optionally
   `DIAG_EVERY_GC=1`.

### Appendix: the diagnostic wrappers

```c
#include <stdio.h>
#include <stdlib.h>
static unsigned long diag_alloc_fail = 0, diag_gc = 0;
static int diag_verbose_gc = -1;
typedef unsigned long long ull;
static void diag_dump(const char *why, uint64_t fp, uint64_t req)
{
  uint64_t lo = zero_addr1, hi = heap_size_u640, nw = (hi - lo) / 8;
  unsigned char *onfl = calloc(nw, 1);
  uint64_t fl_len = 0, fl_words = 0, fl_max = 0, fl_cycle = 0, fl_nonblue = 0, fl_wz0 = 0;
  for (uint64_t cur = fp; cur >= lo + 8 && cur < hi && cur % 8 == 0; ) {        /* free list */
    uint64_t hd = *(uint64_t *)(uintptr_t)(cur - 8), wz = hd >> 10, idx = (cur - 8 - lo) / 8;
    if (onfl[idx]) { fl_cycle = 1; break; }
    onfl[idx] = 1;
    if (((hd >> 8) & 3) != 2) fl_nonblue++;
    if (wz == 0) fl_wz0++;
    fl_len++; fl_words += wz + 1; if (wz + 1 > fl_max) fl_max = wz + 1;
    cur = *(uint64_t *)(uintptr_t)cur;
  }
  uint64_t nblue = 0, bluew = 0, bluemax = 0, off = 0, offw = 0, offmax = 0, wz0 = 0, adj = 0;
  uint64_t whitew = 0, blackw = 0, grayw = 0, objs = 0, p = lo; int prev_blue = 0;
  while (p + 8 <= hi) {                                                          /* heap walk */
    uint64_t hd = *(uint64_t *)(uintptr_t)p, wh = (hd >> 10) + 1, c = (hd >> 8) & 3;
    objs++;
    if (c == 2) {
      nblue++; bluew += wh; if (wh > bluemax) bluemax = wh; if (wh == 1) wz0++;
      if (prev_blue) adj++;
      if (!onfl[(p - lo) / 8]) { off++; offw += wh; if (wh > offmax) offmax = wh; }
      prev_blue = 1;
    } else {
      prev_blue = 0;
      if (c == 0) whitew += wh; else if (c == 3) blackw += wh; else grayw += wh;
    }
    p += wh * 8;
  }
  fprintf(stderr, "[diag %s] heap=%llu words, request whsize=%llu\n"
    "  free list: length=%llu words=%llu largest=%llu non-blue=%llu wosize0=%llu cycle=%llu\n"
    "  heap walk: objs=%llu blue blocks=%llu blue words=%llu largest blue=%llu adjacent-blue=%llu wosize0 blue=%llu\n"
    "  blue NOT on free list: blocks=%llu words=%llu largest=%llu\n"
    "  white=%llu w black=%llu w gray=%llu w walk_end=%s\n",
    why, (ull)nw, (ull)req, (ull)fl_len, (ull)fl_words, (ull)fl_max, (ull)fl_nonblue, (ull)fl_wz0,
    (ull)fl_cycle, (ull)objs, (ull)nblue, (ull)bluew, (ull)bluemax, (ull)adj, (ull)wz0,
    (ull)off, (ull)offw, (ull)offmax, (ull)whitew, (ull)blackw, (ull)grayw,
    p == hi ? "exact" : "OVERRUN");
  free(onfl);
}
#define DIAG_WRAP(name)                                                              \
  K___uint64_t_uint64_t name(heap_t heap, uint64_t fp, uint64_t wosize) {            \
    K___uint64_t_uint64_t r = name##_real(heap, fp, wosize);                         \
    if (r.snd == 0ULL && diag_alloc_fail++ == 0) {                                   \
      fprintf(stderr, "[diag] first failing allocation (" #name "), during GC #%lu\n", \
              diag_gc + 1);                                                          \
      diag_dump("at failing allocation", fp, (wosize ? wosize : 1) + 1);             \
    }                                                                                \
    return r;                                                                        \
  }
DIAG_WRAP(allocate)
DIAG_WRAP(allocate_part1)
K___uint64_t_bool gen_gc(gen_heap_t gh, uint64_t *roots, size_t nroots, uint64_t *fwd_arr,
  uint64_t *queue, uint64_t *slots, size_t nslots, gray_stack_rec st)
{
  if (diag_verbose_gc < 0) diag_verbose_gc = getenv("DIAG_EVERY_GC") != NULL;
  uint64_t bump = *gh.minor.bump_ref;
  K___uint64_t_bool r = gen_gc_real(gh, roots, nroots, fwd_arr, queue, slots, nslots, st);
  diag_gc++;
  if (diag_verbose_gc || !r.snd) {
    char why[96];
    snprintf(why, sizeof why, "after major GC #%lu (%s, minor bump %llu w)", diag_gc,
             r.snd ? "ok" : "PROMOTION FAILED", (ull)(bump / 8));
    diag_dump(why, *gh.fp_ref, 0);
  }
  return r;
}
```

(The tables above came from a version with the two allocation wrappers written
out by hand. The folded version above was rebuilt and gives the same output for `binarytrees 10` at 300k.)
