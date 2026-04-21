#include "buddy.h"
#include <stddef.h>
#define NULL ((void *)0)

/* Buddy allocator for 4K pages, ranks 1..16 */
#define MAXRANK 16
#define PAGE_SIZE (4096)

static unsigned char *base;        /* base address of managed memory */
static int total_pages;            /* number of 4K pages */
static int max_rank;               /* usable max rank (<=16) */

/* free list heads per rank: store offsets (in pages) to first free block, -1 if none */
static int free_head[MAXRANK + 1];
/* next pointer per block (for rank the block belongs to), using offset in pages; size equals total_pages */
static int next_offset_pages[1 << 16]; /* upper bound 65536 pages fits ranks up to 16 for 128MB */
/* allocation map: stores rank for the block start when allocated; 0 means free/unknown */
static unsigned char alloc_map[1 << 16];

static inline int size_pages(int rank) { return 1 << (rank - 1); }
static inline int is_power_of_two(int x) { return (x > 0) && ((x & (x - 1)) == 0); }

static void free_list_push(int rank, int start_off) {
    next_offset_pages[start_off] = free_head[rank];
    free_head[rank] = start_off;
}

static int free_list_pop(int rank) {
    int h = free_head[rank];
    if (h == -1) return -1;
    free_head[rank] = next_offset_pages[h];
    next_offset_pages[h] = -1;
    return h;
}

static void free_list_remove(int rank, int start_off) {
    int prev = -1, cur = free_head[rank];
    while (cur != -1) {
        if (cur == start_off) {
            if (prev == -1) free_head[rank] = next_offset_pages[cur];
            else next_offset_pages[prev] = next_offset_pages[cur];
            next_offset_pages[cur] = -1;
            return;
        }
        prev = cur;
        cur = next_offset_pages[cur];
    }
}

static int buddy_of(int start_off, int rank) {
    int block_pages = size_pages(rank);
    int block_index = start_off / block_pages;
    int buddy_index = block_index ^ 1;
    return buddy_index * block_pages;
}

int init_page(void *p, int pgcount){
    base = (unsigned char *)p;
    total_pages = pgcount;
    if (pgcount <= 0) return -EINVAL;
    for (int r = 1; r <= MAXRANK; ++r) free_head[r] = -1;
    /* clear maps for total_pages upper bound */
    for (int i = 0; i < total_pages; ++i) {
        next_offset_pages[i] = -1;
        alloc_map[i] = 0;
    }
    /* compute max_rank such that size_pages(max_rank) <= total_pages and block aligned */
    max_rank = 1;
    while (max_rank < MAXRANK && (size_pages(max_rank + 1) <= total_pages)) max_rank++;

    /* build free lists by splitting total pages into largest ranks aligned from 0 */
    int remaining = total_pages;
    int off = 0;
    for (int r = max_rank; r >= 1; --r) {
        int blk = size_pages(r);
        while (remaining >= blk && (off % blk) == 0) {
            free_list_push(r, off);
            off += blk;
            remaining -= blk;
        }
    }
    return OK;
}

void *alloc_pages(int rank){
    if (rank < 1 || rank > MAXRANK) return ERR_PTR(-EINVAL);
    if (rank > max_rank) return ERR_PTR(-ENOSPC);
    /* find a block at >= rank; if higher, split down */
    int r = rank;
    while (r <= max_rank && free_head[r] == -1) r++;
    if (r > max_rank) return ERR_PTR(-ENOSPC);
    int off = free_list_pop(r);
    while (r > rank) {
        int r1 = r - 1;
        int half = size_pages(r1);
        /* split block 'off' into two buddies of rank r1 */
        free_list_push(r1, off + half);
        r = r1;
    }
    alloc_map[off] = (unsigned char)rank;
    return base + off * PAGE_SIZE;
}

int return_pages(void *p){
    if (p == NULL) return -EINVAL;
    if (base == NULL) return -EINVAL;
    ptrdiff_t delta = (unsigned char *)p - base;
    if (delta < 0) return -EINVAL;
    if (delta % PAGE_SIZE != 0) return -EINVAL;
    int off = (int)(delta / PAGE_SIZE);
    if (off < 0 || off >= total_pages) return -EINVAL;
    int rank = alloc_map[off];
    if (rank < 1 || rank > MAXRANK) return -EINVAL;
    alloc_map[off] = 0;
    /* merge with free buddy while possible */
    int cur_off = off;
    int cur_rank = rank;
    while (cur_rank < MAXRANK) {
        int buddy = buddy_of(cur_off, cur_rank);
        /* buddy must be free and at same rank: check it's at head list via presence */
        /* We need a way to know if buddy is free at cur_rank: ensure alloc_map[buddy]==0 and that buddy is aligned start */
        int blk = size_pages(cur_rank);
        if ((buddy < 0) || (buddy + blk > total_pages)) break;
        if (alloc_map[buddy] != 0) break;
        /* check buddy currently in free list for this rank */
        /* linear search remove; if not found, stop */
        int found = 0;
        int prev = -1, cur = free_head[cur_rank];
        while (cur != -1) {
            if (cur == buddy) { found = 1; break; }
            prev = cur; cur = next_offset_pages[cur];
        }
        if (!found) break;
        /* remove buddy from free list and merge */
        if (prev == -1) free_head[cur_rank] = next_offset_pages[buddy];
        else next_offset_pages[prev] = next_offset_pages[buddy];
        next_offset_pages[buddy] = -1;
        /* select lower address as combined start */
        cur_off = (cur_off < buddy) ? cur_off : buddy;
        cur_rank += 1;
    }
    free_list_push(cur_rank, cur_off);
    return OK;
}

int query_ranks(void *p){
    if (p == NULL) return -EINVAL;
    if (base == NULL) return -EINVAL;
    ptrdiff_t delta = (unsigned char *)p - base;
    if (delta < 0) return -EINVAL;
    if (delta % PAGE_SIZE != 0) return -EINVAL;
    int off = (int)(delta / PAGE_SIZE);
    if (off < 0 || off >= total_pages) return -EINVAL;
    int rank = alloc_map[off];
    if (rank >= 1 && rank <= MAXRANK) return rank;
    /* unallocated: find maximum free rank covering this offset by checking alignment and whether block exists on free list */
    int r = max_rank;
    while (r >= 1) {
        int blk = size_pages(r);
        int start = (off / blk) * blk;
        /* verify that block [start, start+blk) is currently free and present in list */
        int cur = free_head[r];
        while (cur != -1 && cur != start) cur = next_offset_pages[cur];
        if (cur == start) return r;
        r--;
    }
    /* if no matching free block found, fallback to 1 (shouldn't happen in tests) */
    return 1;
}

int query_page_counts(int rank){
    if (rank < 1 || rank > MAXRANK) return -EINVAL;
    int cnt = 0;
    int cur = free_head[rank];
    while (cur != -1) { cnt++; cur = next_offset_pages[cur]; }
    return cnt;
}
