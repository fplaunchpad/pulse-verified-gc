/* Deterministic unit test for the allocator's one-word-leftover case.
 *
 * The pre-fix allocator, when a free block was exactly one word longer than
 * the request, handed over the whole block and wrote the header with the
 * BLOCK's wosize rather than the REQUESTED wosize, so the object declared a
 * field it did not own. `ast-invariants` catches that end to end, but only
 * sometimes: whether the free list ever holds a `wz + 1` block when a `wz`
 * request arrives depends on allocation history, so at the default 256 MB
 * major heap the testsuite result is a coin flip.
 *
 * This drives `allocate()` directly on a hand-built heap that *always*
 * presents the tight fit, so the case is exercised on every run.
 *
 *   build + run:  make -C generational/snapshot alloc-exact-test
 *
 * Header layout (GC_Gen_Impl.c:makeHeader): (wosize << 10) | (colour << 8) | tag
 * with White = 0, Gray = 1, Blue = 2, Black = 3.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "compat.h"
#include "GC_Gen_Impl.h"
#include "krmlinit.h"

#define MWORD        8ULL
#define COL_WHITE    0ULL
#define COL_BLUE     2ULL
#define HEAP_BYTES   (1024ULL * 1024ULL)

/* The first block starts one word in: address 0 is not a legal object
 * address in the verified model (`is_pointer` rejects 0). */
#define FIRST_HD     MWORD

static uint64_t mk_hdr(uint64_t wosize, uint64_t colour, uint64_t tag) {
    return (wosize << 10) | (colour << 8) | tag;
}
static uint64_t wosize_of(uint64_t hdr) { return hdr >> 10; }
static uint64_t colour_of(uint64_t hdr) { return (hdr >> 8) & 3ULL; }

static uint64_t peek(const uint8_t *d, uint64_t addr) {
    uint64_t v = 0;
    memcpy(&v, d + addr, sizeof v);
    return v;
}
static void poke(uint8_t *d, uint64_t addr, uint64_t v) {
    memcpy(d + addr, &v, sizeof v);
}

/* Walk the block tiling from FIRST_HD and check it covers the heap exactly,
 * with no gap and no overrun. A block at `hd` with wosize w spans
 * [hd, hd + (w+1)*8). */
static int tiling_is_exact(const uint8_t *d, uint64_t heap_bytes, uint64_t *blocks_out) {
    uint64_t at = FIRST_HD, blocks = 0;
    while (at < heap_bytes) {
        uint64_t w = wosize_of(peek(d, at));
        uint64_t next = at + (w + 1ULL) * MWORD;
        if (next <= at || next > heap_bytes) { *blocks_out = blocks; return 0; }
        at = next;
        blocks++;
        if (blocks > heap_bytes / MWORD) { *blocks_out = blocks; return 0; }
    }
    *blocks_out = blocks;
    return at == heap_bytes;
}

/* Build a heap whose free list is a single blue cell of wosize
 * `req + leftover`, then ask for `req` words. */
static int run_case(uint64_t req, uint64_t leftover, int *hard_fail)
{
    uint64_t block_wz = req + leftover;
    uint8_t *data = calloc(1, (size_t)HEAP_BYTES);
    if (!data) { fprintf(stderr, "out of memory\n"); exit(2); }

    /* The one free cell, at FIRST_HD. Its link word (field 0, at obj) is 0,
     * which terminates the chain. */
    uint64_t cell_obj = FIRST_HD + MWORD;
    poke(data, FIRST_HD, mk_hdr(block_wz, COL_BLUE, 0));
    poke(data, cell_obj, 0);

    /* A white filler block covering the rest, so the heap tiles exactly. */
    uint64_t after = FIRST_HD + (block_wz + 1ULL) * MWORD;
    uint64_t filler_wz = (HEAP_BYTES - after) / MWORD - 1ULL;
    poke(data, after, mk_hdr(filler_wz, COL_WHITE, 0));

    heap_t heap = { .data = data, .size = (size_t)HEAP_BYTES };
    K___uint64_t_uint64_t res = allocate(heap, cell_obj, req);

    uint64_t obj = res.snd;
    int ok = 1;

    if (obj == 0) {
        printf("  req=%-3llu leftover=%-2llu  FAIL  allocate() returned 0\n",
               (unsigned long long)req, (unsigned long long)leftover);
        free(data);
        *hard_fail = 1;
        return 0;
    }

    uint64_t hdr      = peek(data, obj - MWORD);
    uint64_t declared = wosize_of(hdr);

    uint64_t blocks = 0;
    int tiled = tiling_is_exact(data, HEAP_BYTES, &blocks);

    if (declared != req) ok = 0;
    if (!tiled)          ok = 0;

    printf("  req=%-3llu leftover=%-2llu  obj=%-6llu declared=%-3llu %s   tiling=%s  %s\n",
           (unsigned long long)req, (unsigned long long)leftover,
           (unsigned long long)obj, (unsigned long long)declared,
           declared == req ? "== req " : "!= req!",
           tiled ? "exact" : "BROKEN",
           ok ? "ok" : "FAIL");

    if (!ok) {
        printf("        header at %llu = 0x%016llx (wosize %llu, colour %llu)\n",
               (unsigned long long)(obj - MWORD), (unsigned long long)hdr,
               (unsigned long long)declared, (unsigned long long)colour_of(hdr));
        if (declared != req)
            printf("        the object declares %llu fields but only %llu were "
                   "requested: field %llu is not owned by this block\n",
                   (unsigned long long)declared, (unsigned long long)req,
                   (unsigned long long)req);
    }
    free(data);
    return ok;
}

int main(void)
{
    zero_addr = 0;
    heap_size_u64 = HEAP_BYTES;
    krmlinit_globals();

    printf("=== allocator size-exactness ===\n");
    printf("A free block of wosize req+leftover; we ask for req words.\n");
    printf("The allocated object must declare exactly req.\n\n");

    int hard_fail = 0, failures = 0;

    /* leftover 0 and >= 2 are controls: both allocators get these right, so a
     * failure there means the harness is wrong, not the allocator. */
    printf("controls (expected to pass on any allocator):\n");
    if (!run_case(3, 0, &hard_fail)) failures++;
    if (!run_case(3, 2, &hard_fail)) failures++;
    if (!run_case(7, 9, &hard_fail)) failures++;

    /* leftover == 1 is the bug. */
    printf("\nthe one-word leftover:\n");
    if (!run_case(3,  1, &hard_fail)) failures++;
    if (!run_case(1,  1, &hard_fail)) failures++;
    if (!run_case(64, 1, &hard_fail)) failures++;

    printf("\n%d case(s) failed\n", failures);
    if (failures) {
        printf("\nThe allocator is not size-exact: a block one word longer than\n"
               "the request is handed over whole, so the object declares a field\n"
               "it does not own. See docs/right-justification-notes.md.\n");
    }
    return failures ? 1 : 0;
}
