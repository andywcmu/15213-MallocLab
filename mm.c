/*
 * mm.c
 * hbovik - Harry Bovik
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) ((size + (ALIGNMENT-1)) & (~(ALIGNMENT-1)))

#define UINT32_T_SIZE (sizeof(uint32_t))
#define START_LEAP UINT32_T_SIZE

#define ONE_ELEM_BLOCK_SIZE (2 * UINT32_T_SIZE + ALIGNMENT)

#define SEG_BLOCK_GROUP_NUM 3
#define SEG_BLOCK_SPLIT_1 4
#define SEG_BLOCK_SPLIT_2 8
#define SEG_BLOCK_SPLIT_3 12
#define SEG_LIST_SIZE (SEG_BLOCK_SPLIT_1 + SEG_BLOCK_GROUP_NUM)

/* explicit free block list head
 * free_head[i] store the head of the free block link list with size
 * assigned as the following:
 *
 * 0 <= i < SEG_BLOCK_SPLIT_1:   size = i
 * SEG_BLOCK_SPLIT_k:        SEG_BLOCK_SPLIT_k <= size < SEG_BLOCK_SPLIT_(k+1)
 */

void *free_head[SEG_LIST_SIZE];

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void *align(void *p, unsigned char w) {
    return (void *)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte is_aligned
static inline int is_aligned(void *p) {
    return align(p, ALIGNMENT) == p;
}

// Return whether the pointer is in the heap.
static inline int in_heap(void *p) {
    return p <= mem_heap_hi() && p >= (void *) ((uintptr_t) mem_heap_lo() + START_LEAP);
}

// Return whether a header is valid
static inline int is_valid_label(void *header_ptr) {
    uint32_t header = *((uint32_t *) header_ptr);
    return (header & (~(ALIGNMENT - 1))) > 1;
}

// pack a size and a allocated status into a word
static inline uint32_t pack (uint32_t size, uint32_t alloc) {
    REQUIRES((size & (ALIGNMENT - 1)) == 0);
    REQUIRES(alloc <= 1);
    return size | alloc;
}

static inline uint32_t read_label(void *label_ptr) {
    return *((uint32_t *) label_ptr);
}

static inline uint32_t read_size (void *label_ptr) {
    REQUIRES(label_ptr != NULL);
    REQUIRES(in_heap(label_ptr));
    // REQUIRES(is_valid_label(label_ptr));
    uint32_t label = read_label(label_ptr);
    return label & (~(ALIGNMENT - 1));
}

static inline uint32_t read_alloc (void *label_ptr) {
    REQUIRES(label_ptr != NULL);
    REQUIRES(in_heap(label_ptr));
    // REQUIRES(is_valid_label(label_ptr));
    uint32_t label = read_label(label_ptr);
    return label & 0x1;
}

static inline void write_label(void *label_ptr, uint32_t label) {
    *((uint32_t *) label_ptr) = label;
}

static inline void *get_header_ptr (void *ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr - UINT32_T_SIZE);
}

static inline void *get_footer_ptr (void *ptr, uint32_t size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));
    REQUIRES(size >= UINT32_T_SIZE);

    return (void *)((uintptr_t) ptr + size - 2 * UINT32_T_SIZE);
}

static inline void *get_prev_footer_ptr (void *ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr - 2 * UINT32_T_SIZE);
}

static inline void *get_next_header_ptr (void *ptr, uint32_t size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr + size - UINT32_T_SIZE);
}

static inline void *get_prev_block (void *ptr, uint32_t prev_size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));
    return (void *)((uintptr_t) ptr - prev_size);
}

static inline void *get_next_block (void *ptr, uint32_t size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));
    return (void *)((uintptr_t) ptr + size);
}

static inline void *increment_pointer(void *ptr, uint32_t inc) {
    return (void *)((uintptr_t) ptr + inc);
}

static inline void write_header_footer(void *ptr, uint32_t size, uint32_t alloc) {
    REQUIRES(ptr != NULL);
    void *header = get_header_ptr(ptr);
    void *footer = get_footer_ptr(ptr, size);
    REQUIRES(in_heap(header));
    REQUIRES(in_heap(footer));
    uint32_t label = pack(size, alloc);
    write_label(header, label);
    write_label(footer, label);
    return;
}

static inline void swap_alloc (void *ptr) {
    REQUIRES(ptr != NULL);
    void *header = get_header_ptr(ptr);
    uint32_t size = read_size(header);
    void *footer = get_footer_ptr(ptr, size);
    REQUIRES(header != NULL);
    REQUIRES(in_heap(header) && in_heap(footer));
    REQUIRES(is_valid_label(header) && is_valid_label(footer));
    /* swap the header's alloc bit */
    *((uint32_t *) header) ^= 0x1;
    *((uint32_t *) footer) ^= 0x1;
    return;
}

static inline void *next_free_block (void *ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    int offset = (int) (*((intptr_t *) ptr)) & 0xFFFFFFFF;
    if (offset == 0) return NULL;
    return (void *) ((intptr_t) ptr + offset);
}

static inline void *prev_free_block (void *ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    int offset = (int) ((*((uintptr_t *) ptr)) >> 32);
    if (offset == 0) return NULL;
    return (void *) ((intptr_t) ptr + offset);
}

static inline void write_next_offset (void *ptr, void *next_ptr) {
    /* if ptr is NULL, we don't write anything */
    if (ptr == NULL) return;

    REQUIRES(in_heap(ptr));
    /* if the next_ptr is NULL, simply write the offset as NULL */
    if (next_ptr == NULL) {
        *((uintptr_t *) ptr) &= 0xFFFFFFFF00000000;
        return;
    }
    int next_offset = ((intptr_t) next_ptr) - ((intptr_t) ptr);
    /* write */
    *((uintptr_t *) ptr) &= 0xFFFFFFFF00000000;
    *((uintptr_t *) ptr) |= (uintptr_t) (unsigned) next_offset;
    return;
}

static inline void write_prev_offset (void *ptr, void *prev_ptr) {
    /* if ptr is NULL, we don't write anything */
    if (ptr == NULL) return;

    REQUIRES(in_heap(ptr));
    /* if the prev_ptr is NULL, simply write the offset as NULL */
    if (prev_ptr == NULL) {
        *((uintptr_t *) ptr) &= 0x00000000FFFFFFFF;
        return;
    }
    int prev_offset = ((intptr_t) prev_ptr) - ((intptr_t) ptr);
    /* write */
    *((uintptr_t *) ptr) &= 0xFFFFFFFF;
    *((uintptr_t *) ptr) |= ((uintptr_t) prev_offset << 32);
    return;
}

static inline int group_index (uint32_t size) {
    REQUIRES(size == ALIGN(size));
    uint32_t s = size / ALIGNMENT;
    if (s <= SEG_BLOCK_SPLIT_1) {
        return s - 1;
    }
    else if (s <= SEG_BLOCK_SPLIT_2) {
        return SEG_BLOCK_SPLIT_1;
    }
    else if (s <= SEG_BLOCK_SPLIT_3) {
        return SEG_BLOCK_SPLIT_1 + 1;
    }
    else {
        return SEG_BLOCK_SPLIT_1 + 2;
    }
    REQUIRES(0); // shouldn't reach here
    return -1;
}

static inline void print_heap (void) {
    void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi();
    dbg_printf("lo: %lx\thi: %lx\tsize: %zx\n", (uintptr_t) heap_lo, (uintptr_t) heap_hi, mem_heapsize());
    void *p = increment_pointer(heap_lo, UINT32_T_SIZE + START_LEAP);
    dbg_printf("|");
    while (p < heap_hi) {
        void *header = get_header_ptr(p);
        uint32_t size = read_size(header);
        dbg_printf(" %lx %x %d |", (uintptr_t) p, size, read_alloc(header));
        p = increment_pointer(p, size);
    }
    dbg_printf("\n");
    return;
}

static inline void print_free_list (void) {
    dbg_printf("free list:\n");
    void *p;
    void *p_prev;
    int i;
    for (i = 0; i < SEG_BLOCK_SPLIT_1 + SEG_BLOCK_GROUP_NUM; i++) {
        p = free_head[i];
        p_prev = NULL;
        dbg_printf("### %d ###\n", i);
        while (p != NULL) {
            // dbg_printf("%lx %lx -> ", (uintptr_t) p, *((uintptr_t *) p));
            dbg_printf("%lx -> ", (uintptr_t) p);
            p_prev = p;
            p = next_free_block(p);
        }
        dbg_printf("NULL\n");
        p = p_prev;
        while (p != NULL) {
            // dbg_printf("%lx %lx -> ", (uintptr_t) p, *((uintptr_t *) p));
            dbg_printf("%lx -> ", (uintptr_t) p);
            p = prev_free_block(p);
        }
        dbg_printf("NULL\n");
    }
    return;
}

static inline void disconnect_from_list (void *ptr, uint32_t size) {
    REQUIRES(ptr != NULL);
    void *prev_ptr = prev_free_block(ptr);
    void *next_ptr = next_free_block(ptr);
    write_next_offset(prev_ptr, next_ptr);
    write_prev_offset(next_ptr, prev_ptr);

    /* update free_head if needed */
    if (prev_ptr == NULL) {
        free_head[group_index(size)] = next_ptr;
    }

    return;
}

static inline void insert_into_list (void *ptr, uint32_t size) {
    REQUIRES(ptr != NULL);
    int gi = group_index(size);
    write_next_offset(ptr, free_head[gi]);
    write_prev_offset(ptr, NULL);
    write_prev_offset(free_head[gi], ptr);
    free_head[gi] = ptr;
    return;
}


/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    dbg_printf("initialize:\n");

    /* init free_head */
    int i;
    for (i = 0; i < SEG_BLOCK_SPLIT_1 + SEG_BLOCK_GROUP_NUM; i++) {
        free_head[i] = NULL;
    }

    /* init heap */
    if(mem_sbrk(START_LEAP) == 0) {
        dbg_printf("error: heap initialization failed");
        return -1;
    };

    checkheap(1);
    return 0;
}

void *find_free_block (uint32_t required_size) {
    REQUIRES(required_size >= 1);
    
    /* search through the segregated link list */
    void *p;
    int gi;
    for (gi = group_index(required_size); gi < SEG_LIST_SIZE; gi++) {
        p = free_head[gi];
        while (p != NULL) {

            /* ### WHY THIS WILL ACUALLY SLOW DOWN THE UTIL?? */
            /* ### WHY THIS WILL ACUALLY SLOW DOWN THE UTIL?? */
            /* ### WHY THIS WILL ACUALLY SLOW DOWN THE UTIL?? */
            /* ### WHY THIS WILL ACUALLY SLOW DOWN THE UTIL?? */
            if (gi < SEG_BLOCK_SPLIT_1) {
                swap_alloc(p);
                void *next_free = next_free_block(p);
                free_head[gi] = next_free;
                write_prev_offset(next_free, NULL);
                return p;
            }

            void *header = get_header_ptr(p);
            /* check that the block is indeed free */
            REQUIRES(!read_alloc(header));

            uint32_t block_size = read_size(header);
            void *next_free = next_free_block(p);
            void *prev_free = prev_free_block(p);
            if (block_size >= required_size) {
                /* found a free space that has enough space */
                if (block_size > required_size + ONE_ELEM_BLOCK_SIZE) {
                    /* we should split the block */
                    /* modify the header of the current block */
                    write_header_footer(p, required_size, 1);
                    /* write the header of the splitted block */
                    uint32_t remain_size = block_size - required_size;
                    void *splitted_ptr = increment_pointer(p, required_size);
                    write_header_footer(splitted_ptr, remain_size, 0);
                    
                    /* delete the block from the current link list */
                    write_next_offset(prev_free, next_free);
                    write_prev_offset(next_free, prev_free);
                    if (prev_free == NULL) {
                        free_head[gi] = next_free;
                    }

                    /* insert the block into the head of the new link list */
                    insert_into_list(splitted_ptr, remain_size);

                }
                else {
                    /* otherwise, we don't have to split */
                    /* modify the alloc of the current block */
                    swap_alloc(p);
                    /* delete the block from the link list */
                    write_next_offset(prev_free, next_free);
                    write_prev_offset(next_free, prev_free);
                    if (prev_free == NULL) {
                        free_head[gi] = next_free;
                    }
                }

                checkheap(1);
                
                return p;
            }
            /* the block is not large enough. go to the next free block */
            p = next_free;
        }
    }

    /* no free block */
    return NULL;
}

void *brk_new_block (uint32_t required_size) {
    void *brkp;
    if ((brkp = mem_sbrk(required_size)) == 0) {
        /* mem_sbrk failed */
        dbg_printf("error: mem_sbrk failed");
        return NULL;
    }

    void *p = increment_pointer(brkp, UINT32_T_SIZE);
    write_header_footer(p, required_size, 1);

    checkheap(1);
    
    return p;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    REQUIRES(size < (1l << 32));
    if (size == 0) return NULL;

    uint32_t required_size = ALIGN(size) + 2 * UINT32_T_SIZE;
    dbg_printf("malloc: %zx %x\n", size, required_size);
    
    /* check if there is any free block */
    void *p = find_free_block(required_size);
    if (p != NULL) return p;

    /* no free block, so brk for a new block */
    return brk_new_block(required_size);
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) return;
    dbg_printf("free: %lx\n", (uintptr_t) ptr);
    void *header = get_header_ptr(ptr);
    uint32_t size = read_size(header);
    void *prev_footer = get_prev_footer_ptr(ptr);
    void *next_header = get_next_header_ptr(ptr, size);
    
    /* if both prev and next are free */
    if ((in_heap(prev_footer) && !read_alloc(prev_footer)) &&
        (in_heap(next_header) && !read_alloc(next_header))) {
        uint32_t prev_size = read_size(prev_footer);
        uint32_t next_size = read_size(next_header);
        void *prev_ptr = get_prev_block(ptr, prev_size);
        void *next_ptr = get_next_block(ptr, size);

        /* write size header & footer */
        void *prev_header = get_header_ptr(prev_ptr);
        void *next_footer = get_footer_ptr(next_ptr, next_size);
        uint32_t new_size = size + prev_size + next_size;
        write_label(prev_header, new_size);
        write_label(next_footer, new_size);
        /* do not have to write_alloc since the lower bit is already 0 */

        /* delete the blocks from the link lists */
        disconnect_from_list(prev_ptr, prev_size);
        disconnect_from_list(next_ptr, next_size);

        /* insert the new free block into a new link list */
        insert_into_list(prev_ptr, new_size);
    }
    /* if only the prev is free */
    else if (in_heap(prev_footer) && !read_alloc(prev_footer)) {
        uint32_t prev_size = read_size(prev_footer);
        void *prev_ptr = get_prev_block(ptr, prev_size);

        /* write size header & footer */
        void *prev_header = get_header_ptr(prev_ptr);
        void *footer = get_footer_ptr(ptr, size);
        uint32_t new_size = size + prev_size;
        write_label(prev_header, new_size);
        write_label(footer, new_size);
        /* do not have to write_alloc since the lower bit is already 0 */

        /* delete the prev block from its link list */
        disconnect_from_list(prev_ptr, prev_size);

        /* insert the new free block into a new link list */
        insert_into_list(prev_ptr, new_size);
    }
    /* if only the next is free */
    else if (in_heap(next_header) && !read_alloc(next_header)) {
        uint32_t next_size = read_size(next_header);
        void *next_ptr = get_next_block(ptr, size);

        /* write size header & footer */
        void *next_footer = get_footer_ptr(next_ptr, next_size);
        uint32_t new_size = size + next_size;
        write_label(header, new_size);
        write_label(next_footer, new_size);
        /* do not have to write_alloc since the lower bit is already 0 */

        /* delete the prev block from its link list */
        disconnect_from_list(next_ptr, next_size);

        /* insert the new free block into a new link list */
        insert_into_list(ptr, new_size);

    }
    /* otherwise, only the current block is free */
    else {
        /* write alloc bit */
        swap_alloc(ptr);

        /* insert the free block into the head of the free list */
        insert_into_list(ptr, size);
    }

    checkheap(1);
    return;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *old_ptr, size_t size) {
    REQUIRES(size < (1l << 32));
    REQUIRES(old_ptr != NULL || size != 0);
    dbg_printf("realloc: %lx %zx\n", (uintptr_t) old_ptr, size);
    uint32_t old_size;
    void *new_ptr;
    /* If old_ptr is NULL, then this is just malloc */
    if (old_ptr == NULL) {
        return malloc(size);
    }
    /* If size == 0 then this is just free, and we return NULL */
    if (size == 0) {
        free(old_ptr);
        return NULL;
    }

    uint32_t required_size = ALIGN(size) + 2 * UINT32_T_SIZE;

    void *old_header = get_header_ptr(old_ptr);
    old_size = read_size(old_header);

    /* if new size is smaller than old size, split the original and
     * free the last part,
     */
    if (required_size <= old_size - ONE_ELEM_BLOCK_SIZE) {
        /* modify the size */
        write_header_footer(old_ptr, required_size, 1);

        /* split and free */
        uint32_t remain_size = old_size - required_size;
        void *splitted_ptr = increment_pointer(old_ptr, required_size);
        write_header_footer(splitted_ptr, remain_size, 0);

        /* insert into free list */
        insert_into_list(splitted_ptr, remain_size);

        return old_ptr;
    }
    /* not big enough to split */
    else if (required_size <= old_size) {
        return old_ptr;
    }
    else {
        void *next_ptr = get_next_block(old_ptr, old_size);
        void *next_header;
        uint32_t next_size;
        /* next block is free and is enough to extend the current block
         * using the next free block.
         */
        if (in_heap(next_ptr) &&
            !read_alloc(next_header = get_header_ptr(next_ptr)) &&
            ((next_size = read_size(next_header)) + old_size > required_size)) {
            /* split the remaining block */
            if (required_size <= next_size + old_size - ONE_ELEM_BLOCK_SIZE) {
                /* disconnect the free block from the list first */
                disconnect_from_list(next_ptr, next_size);

                /* write size header & footer */
                write_header_footer(old_ptr, required_size, 1);
                void *splitted_ptr = increment_pointer(old_ptr, required_size);
                uint32_t remain_size = next_size + old_size - required_size;
                write_header_footer(splitted_ptr, remain_size, 0);

                /* insert the remaining block into the list */
                insert_into_list(splitted_ptr, remain_size);
                return old_ptr;
            }
            /* don't split */
            else {
                disconnect_from_list(next_ptr, next_size);
                write_header_footer(old_ptr, next_size + old_size, 1);
                return old_ptr;
            }
        }
        /* there's no next block, or next block is not big enough */
        else {
            /* malloc a new block. return NULL if failed */
            if ((new_ptr = malloc(size)) == NULL) return NULL;
            memcpy(new_ptr, old_ptr, old_size);

            /* Free the old block. */
            free(old_ptr);
            return new_ptr;
        }
    }

    REQUIRES(0); // shouldn't reach here
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    nmemb = nmemb;
    size = size;
    return NULL;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    if (verbose) {
        print_heap();
        print_free_list();
        void *heap_lo = mem_heap_lo();
        void *heap_hi = mem_heap_hi();
        if (heap_hi < heap_lo) return 0;
        void *p = increment_pointer(heap_lo, UINT32_T_SIZE + START_LEAP);
        void *header, *footer;
        uint32_t size;
        uint32_t prev_free_flag = 0;
        /* traverse the heap */
        while (p < heap_hi) {
            header = get_header_ptr(p);
            size = read_size(header);
            footer = get_footer_ptr(p, size);
            /* check if p is in heap */
            if (!in_heap(p)) {
                dbg_printf("error: a pointer is out of bound\n");
                return -1;
            }
            /* check if each block's address is is_aligned */
            if (!is_aligned(p)) {
                dbg_printf("error: a block is not is_aligned\n");
                return -1;
            }

            /* check if the header is valid */
            if ((read_label(header) & (ALIGNMENT - 1)) > 1) {
                dbg_printf("error: header has invalid format\n");
                return -1;
            }

            /* check if the header is the same as the footer */
            if (read_label(header) != read_label(footer)) {
                dbg_printf("error: header is not the same as footer. header: %x, footer: %x\n", read_label(header), read_label(footer));
                return -1;
            }

            /* if the current block is free, the next block cannot be free */
            if (read_alloc(header)) {
                prev_free_flag = 0;
            } else {
                if (prev_free_flag == 1) {
                    dbg_printf("error: there are two consecutive free blocks\n");
                    return -1;
                }
                prev_free_flag = 1;
            }

            p = increment_pointer(p, read_size(header));
        }
        /* check if the pointer p ends at the end of the last block */
        if (p != (void *)((uintptr_t) heap_hi + 1 + UINT32_T_SIZE)) {
            dbg_printf("error: headers are corrupted\n");
            return -1;
        }

        /* traverse the free list from head to end */
        int i;
        for (i = 0; i < SEG_BLOCK_SPLIT_1 + SEG_BLOCK_GROUP_NUM; i++) {
            p = free_head[i];
            void *p_prev = NULL;
            while (p != NULL) {
                REQUIRES(p_prev == NULL || next_free_block(p_prev) == p);
                /* check if p is in heap */
                if (!in_heap(p)) {
                    dbg_printf("error: a free pointer is out of bound (1)\n");
                    return -1;
                }
                /* check if the free block is aligned */
                if (!is_aligned(p)) {
                    dbg_printf("error: a free block is not is_aligned\n");
                    return -1;
                }
                void *header = get_header_ptr(p);
                if (read_alloc(header)) {
                    dbg_printf("error: a pointer in free list is not pointed to a free block\n");
                    return -1;
                }
                p_prev = p;
                p = next_free_block(p);
            }
            p = p_prev;
            /* traverse the free list from end to head */
            while (p != NULL) {
                /* check if p is in heap */
                if (!in_heap(p)) {
                    dbg_printf("error: a free pointer is out of bound (2)\n");
                    return -1;
                }
                /* check if the free block is aligned */
                if (!is_aligned(p)) {
                    dbg_printf("error: a free block is not is_aligned\n");
                    return -1;
                }
                void *header = get_header_ptr(p);
                if (read_alloc(header)) {
                    dbg_printf("error: a pointer in free list is not pointed to a free block\n");
                    return -1;
                }
                p = prev_free_block(p);
            }
        }
    }
    
    return 0;
}

   