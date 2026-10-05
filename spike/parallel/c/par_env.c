#include <pthread.h>
#include <stdlib.h>
#include "Spike_ParEnv.h"

typedef struct { void (*f)(Spike_ParEnv_half); Spike_ParEnv_half e; } job;

static void *run(void *p) { job *j = p; j->f(j->e); return NULL; }

void Spike_ParEnv_par_env(Spike_ParEnv_half ef, Spike_ParEnv_half eg,
                          void (*f)(Spike_ParEnv_half), void (*g)(Spike_ParEnv_half))
{
  job j = { f, ef };
  pthread_t t;
  if (pthread_create(&t, NULL, run, &j) != 0) { f(ef); g(eg); return; }
  g(eg);
  if (pthread_join(t, NULL) != 0) abort();
}
