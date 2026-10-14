/* custard_glue.c — see custard_glue.h.  Hand-written, not generated. */

#include "custard_glue.h"

void gc_init_globals(void)
{
  /* zero_addr / heap_size_u64 copies and the color constants. */
  custard_init_globals();

  /* The nursery size is configured at runtime by overwriting
   * minor_heap_size_u64, but Custard evaluates these three derived sizes from
   * the .fst value (2048) into static initialisers.  Recompute them from the
   * runtime value, which is what KaRaMeL's krmlinit_globals did. */
  minor_heap_size_sz = (size_t)minor_heap_size_u64;
  fwd_arr_size_sz    = (size_t)(minor_heap_size_u64 / 8ULL);
  queue_size_sz      = (size_t)(minor_heap_size_u64 / 8ULL);
}
