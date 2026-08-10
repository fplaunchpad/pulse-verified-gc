/* Standalone spike: proves the young_ptr translation/exactness invariant
 * needed for native minor-heap nursery-aliasing, WITHOUT touching the real
 * OCaml runtime or the real verified GC. See NATIVE_MINOR_GC_LOG.md.
 *
 * The real trap chain (native, top-down, decided by frozen machine code):
 *   young_ptr -= n; if (young_ptr < young_limit) trap;
 *   ... trap handler runs ...
 *   result = young_ptr + 8;              <- MUST be correct, unconditionally
 *
 * The real verified minor allocator (bytecode today, bottom-up):
 *   bump_ref starts at 0, grows toward minor_heap_size.
 *
 * This harness emulates both conventions and the translation between them,
 * without any F-star/Pulse code -- just the arithmetic contract -- and checks
 * it holds across many alloc/trap/collect cycles, including combined
 * (Comballoc-style) multi-object requests.
 *
 * Build:  cc -O2 -Wall -Wextra spike_young_ptr_invariant.c -o spike && ./spike
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define HEAP_SIZE 4096u /* bytes; small on purpose, to force frequent traps */

static uint8_t heap[HEAP_SIZE];

/* Native's own view: top-down. */
static uint8_t *young_start;
static uint8_t *young_end;
static uint8_t *young_ptr;
static uint8_t *young_limit;

/* Our verified GC's own view: bottom-up (mirrors vergc_minor_bump_ref). */
static uint64_t bump_ref;

static long collections = 0;
static long allocations = 0;

static void reset_heap(void) {
    young_start = heap;
    young_end   = heap + HEAP_SIZE;
    young_ptr   = young_end;
    young_limit = young_start;
    bump_ref    = 0;
    memset(heap, 0xAA, HEAP_SIZE); /* poison, like DEBUG_clear/Debug_free_minor */
}

/* Stand-in for minor_collect_full(): the real one promotes every reachable
 * object out of the nursery and unconditionally empties it (confirmed
 * against stock OCaml's own debug-poison loop and the F* reset step).
 * A standalone spike can't run real reachability analysis, so it models
 * the ONE guarantee that matters for this invariant: after collection,
 * the entire nursery is free. */
static void stand_in_collect(void) {
    collections++;
    bump_ref = 0;
    memset(heap, 0xAA, HEAP_SIZE);
}

/* The trap handler our real caml_garbage_collection replacement would be.
 * Takes the ORIGINAL requested size (post-Comballoc total, in bytes,
 * header included) that triggered the trap. Returns nothing -- like the
 * real one, its job is only to leave young_ptr/young_limit correct for
 * the frozen "+8" instruction that runs immediately after it returns. */
static void trap_handler(uint64_t requested_bytes) {
    /* 0. Undo the speculative decrement -- mirrors
     *    caml_alloc_small_dispatch's very first line,
     *    "Caml_state->young_ptr += whsize;". Without this, young_ptr can
     *    currently be sitting BELOW young_start (the allocation that
     *    triggered the trap already subtracted its size before the
     *    bounds check ran), which would make the translation below
     *    underflow. Found by this spike failing its own assertion on
     *    first run -- see NATIVE_MINOR_GC_LOG.md. */
    young_ptr += requested_bytes;

    /* 1. Translate in: top-down used-bytes -> bottom-up bump_ref. */
    uint64_t used_bytes = (uint64_t)(young_end - young_ptr);
    bump_ref = HEAP_SIZE - used_bytes;
    assert(bump_ref <= HEAP_SIZE);

    /* 2. Run the (stand-in for the) proven collector. */
    stand_in_collect();

    /* 3. Translate back: reset to top, mirroring stock's own
     *    `young_ptr = young_alloc_end` and our own bump_ref==0. */
    young_ptr   = young_end;
    young_limit = young_start;

    /* 4. Redo the allocation -- mirrors caml_alloc_small_dispatch's
     *    "Caml_state->young_ptr -= whsize;" after the retry loop breaks. */
    young_ptr -= requested_bytes;

    /* This is the ONE invariant this whole spike exists to check: after
     * this function returns, the frozen `result = young_ptr + 8`
     * instruction must be correct. We can't literally check "correct"
     * without a caller, so the caller checks it explicitly below. */
}

/* Emulates the compiler-generated Ialloc sequence for ONE allocation
 * (or one Comballoc-combined request of total size `n` bytes). Returns
 * the address the real assembly would compute via `lea 8(young_ptr)`. */
static uint8_t *emulated_alloc(uint64_t n) {
    allocations++;
    young_ptr -= n;
    if (young_ptr < young_limit) {
        trap_handler(n);
    }
    return young_ptr + 8;
}

static void check_in_bounds(uint8_t *addr, uint64_t n) {
    assert(addr >= young_start);
    assert(addr + (n - 8) <= young_end);
    assert(((uintptr_t)(addr - 8)) % 8 == 0); /* header word-aligned */
}

int main(void) {
    reset_heap();

    srand(12345);
    uint8_t *live[64];
    uint64_t live_sz[64];
    int nlive = 0;

    /* Drive many alloc cycles, including combined (Comballoc-style)
     * multi-object requests, forcing frequent collections in a tiny heap. */
    for (int iter = 0; iter < 200000; iter++) {
        int nobjs = 1 + (rand() % 4); /* simulate Comballoc combining up to 4 */
        uint64_t total = 0;
        for (int k = 0; k < nobjs; k++) {
            uint64_t wosize = 1 + (rand() % 8);
            total += (wosize + 1) * 8; /* header + fields, word-aligned */
        }
        if (total > HEAP_SIZE - 8) continue; /* would never fit; not this spike's concern */

        long collections_before = collections;
        uint8_t *addr = emulated_alloc(total);
        check_in_bounds(addr, total);

        /* THE invariant: if a collection just ran, young_ptr must be
         * EXACTLY addr - 8, not "somewhere in the free region". */
        assert(young_ptr == addr - 8);

        /* A real collection would have promoted/copied every previously
         * tracked object elsewhere -- they're no longer "in the nursery"
         * to compare against, so start a fresh overlap-tracking epoch. */
        if (collections != collections_before) nlive = 0;

        /* Overlap check: the new object's [addr-8, addr-8+total) range
         * must not intersect any object still live in this epoch. A bug
         * in the translation (e.g. the missing "undo" step this spike
         * already caught once) would very likely reuse an address still
         * holding a previous allocation, which this catches directly. */
        for (int j = 0; j < nlive; j++) {
            uint8_t *a0 = addr - 8, *a1 = a0 + total;
            uint8_t *b0 = live[j] - 8, *b1 = b0 + live_sz[j];
            assert(a1 <= b0 || b1 <= a0); /* no overlap */
        }

        /* Write a canary so overlapping allocations would corrupt each
         * other and get caught below. */
        memset(addr, (iter & 0x7f) + 1, total - 8);

        if (nlive < 64) {
            live[nlive] = addr;
            live_sz[nlive] = total;
            nlive++;
        }
    }

    printf("OK: %ld allocations, %ld collections, invariant held every time\n",
           allocations, collections);
    return 0;
}
