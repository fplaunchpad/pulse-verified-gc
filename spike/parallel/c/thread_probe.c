#include <pthread.h>
#include <stdio.h>
#include "Spike_FillHalves.h"
#include "thread_probe.h"

static pthread_t ran_on[3];

static void recording_fill_half(Spike_ParEnv_half e)
{
  ran_on[e.v] = pthread_self();
  Spike_FillHalves_fill_half(e);
}

bool thread_probe_fill(uint64_t *a, size_t n)
{
  Spike_ParEnv_half el = { .arr = a, .lo = 0, .hi = n / 2, .v = 1 };
  Spike_ParEnv_half er = { .arr = a, .lo = n / 2, .hi = n, .v = 2 };
  Spike_ParEnv_par_env(el, er, recording_fill_half, recording_fill_half);
  bool distinct = !pthread_equal(ran_on[1], ran_on[2]);
  printf("branch f ran on thread %p, branch g on thread %p: %s\n",
         (void *)ran_on[1], (void *)ran_on[2], distinct ? "distinct" : "SAME");
  fflush(stdout);
  return distinct;
}
