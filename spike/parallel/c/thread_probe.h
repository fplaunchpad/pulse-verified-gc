#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Fills the two halves of a through par_env, with branches that record the
   thread they ran on.  Prints both, and returns true iff they differ. */
bool thread_probe_fill(uint64_t *a, size_t n);
