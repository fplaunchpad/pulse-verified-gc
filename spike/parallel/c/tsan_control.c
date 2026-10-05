/* Negative control, not verified: both branches write the WHOLE array, which
   the Pulse precondition of par_env forbids.  ThreadSanitizer must flag it. */
#include <stdio.h>
#include <stdlib.h>
#include "Spike_FillHalves.h"

int main(void)
{
  size_t n = 1000;
  uint64_t *a = calloc(n, sizeof *a);
  if (a == NULL) return 2;
  Spike_ParEnv_half e1 = { .arr = a, .lo = 0, .hi = n, .v = 1 };
  Spike_ParEnv_half e2 = { .arr = a, .lo = 0, .hi = n, .v = 2 };
  Spike_ParEnv_par_env(e1, e2, Spike_FillHalves_fill_half, Spike_FillHalves_fill_half);
  printf("control ran\n");
  free(a);
  return 0;
}
