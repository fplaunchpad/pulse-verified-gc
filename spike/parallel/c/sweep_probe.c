/* Spike 3: par_env inside a real verified-GC collection, on the real major heap.

   Called from collect_with_roots (generational/snapshot/GC_Gen_Impl.c, under
   SPIKE_SWEEP_PROBE) after mark_loop_bounded and before fused_sweep_coalesce:
   marking is done, nothing is swept, and the mutator is stopped.

   1. The main thread walks the heap once, exactly as fused_sweep_coalesce
      does, counting objects and whole words.  A second cursor trails it,
      one object for every two the walk passes, so it ends on the header of
      object number objs / 2: segment A is [start, mid), segment B is
      [mid, stop), and both boundaries are object headers.  (Splitting at the
      byte midpoint instead left B empty: one free block spans it.)
   2. par_env runs walk_segment on each segment, one on a new thread and one
      on the calling thread.  The workers only load heap words and write
      their own result slot; they call no OCaml runtime function.
   3. The two results must add up to the sequential walk, and the two
      branches must have run on different threads.  Otherwise: abort.

   Spike 2's par_env and its `half` record are reused unchanged:
     arr = first word of the segment, lo..hi = word indices into it,
     v   = result slot (0 or 1).

   SPIKE_PROBE_RACE=1 is the negative control for ThreadSanitizer: branch g
   also rewrites (with the same value) the header segment A starts with,
   while branch f reads it. */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include "Spike_ParEnv.h"

extern uint64_t zero_addr1;     /* same bounds fused_sweep_coalesce uses */
extern uint64_t heap_size_u640;

typedef struct { uint64_t objs, words; pthread_t tid; } seg_result;

static seg_result res[2];
static uint64_t *race_target;
static unsigned long probes;

static void walk_segment(Spike_ParEnv_half e)
{
  uint64_t objs = 0, words = 0;
  for (size_t i = e.lo; i < e.hi; ) {
    uint64_t whsize = (e.arr[i] >> 10) + 1;   /* wosize + header */
    objs++;
    words += whsize;
    i += whsize;
  }
  res[e.v] = (seg_result){ objs, words, pthread_self() };
}

static void walk_segment_racy(Spike_ParEnv_half e)
{
  *(volatile uint64_t *)race_target = *(volatile uint64_t *)race_target;
  walk_segment(e);
}

static void report(void)
{
  fprintf(stderr, "sweep-probe: %lu collections checked, all matched, two threads each\n",
          probes);
}

void spike_sweep_probe(uint8_t *base)
{
  uint64_t start = zero_addr1, end = heap_size_u640;
  uint64_t cur = start, mid = start, objs = 0, words = 0;
  while (cur + 8 < end) {
    uint64_t whsize = (*(uint64_t *)(base + cur) >> 10) + 1;
    objs++;
    words += whsize;
    cur += whsize * 8;
    if (objs % 2 == 0) mid += ((*(uint64_t *)(base + mid) >> 10) + 1) * 8;
  }
  uint64_t stop = cur;

  uint64_t *heap = (uint64_t *)(base + start);
  size_t m = (mid - start) / 8, n = (stop - start) / 8;
  Spike_ParEnv_half ea = { .arr = heap, .lo = 0, .hi = m, .v = 0 };
  Spike_ParEnv_half eb = { .arr = heap, .lo = m, .hi = n, .v = 1 };
  int race = getenv("SPIKE_PROBE_RACE") != NULL;
  race_target = heap;
  Spike_ParEnv_par_env(ea, eb, walk_segment, race ? walk_segment_racy : walk_segment);

  int ok = res[0].objs + res[1].objs == objs && res[0].words + res[1].words == words;
  int distinct = !pthread_equal(res[0].tid, res[1].tid);
  probes++;
  fprintf(stderr,
          "sweep-probe #%lu: %llu objs = %llu + %llu, %llu words = %llu + %llu, "
          "split at word %zu of %zu, threads %s\n",
          probes, (unsigned long long)objs, (unsigned long long)res[0].objs,
          (unsigned long long)res[1].objs, (unsigned long long)words,
          (unsigned long long)res[0].words, (unsigned long long)res[1].words,
          m, n, distinct ? "distinct" : "SAME");
  if (!ok || !distinct) {
    fprintf(stderr, "sweep-probe: FAIL\n");
    abort();
  }
  if (probes == 1) atexit(report);
}
