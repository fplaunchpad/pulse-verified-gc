#include <stdio.h>
#include <stdlib.h>
#include "Spike_FillHalves.h"
#include "thread_probe.h"

static int check(const uint64_t *a, size_t n)
{
  for (size_t i = 0; i < n; i++)
    if (a[i] != (i < n / 2 ? 1 : 2)) { printf("FAIL at %zu\n", i); return 0; }
  return 1;
}

int main(void)
{
  size_t n = 1000001;
  uint64_t *a = calloc(n, sizeof *a);
  if (a == NULL) return 2;
  Spike_FillHalves_fill_halves(a, n);
  if (!check(a, n)) return 1;
  for (size_t i = 0; i < n; i++) a[i] = 0;
  if (!thread_probe_fill(a, n) || !check(a, n)) return 1;
  printf("ok: %zu elements, two threads\n", n);
  free(a);
  return 0;
}
