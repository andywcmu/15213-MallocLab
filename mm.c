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

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

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
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

// Return whether a header is valid
static inline int is_valid_label(void *header_ptr) {
    size_t header = *((size_t *) header_ptr);
    return (header & (~(ALIGNMENT - 1))) > 1;
}

// pack a size and a allocated status into a word
static inline size_t pack (size_t size, size_t alloc) {
    REQUIRES((size & (ALIGNMENT - 1)) == 0);
    REQUIRES(alloc <= 1);
    return size | alloc;
}

static inline size_t read_label(void *label_ptr) {
    return *((size_t *) label_ptr);
}

static inline size_t read_size (void *label_ptr) {
    REQUIRES(label_ptr != NULL);
    REQUIRES(in_heap(label_ptr));
    REQUIRES(is_aligned(label_ptr));
    REQUIRES(is_valid_label(label_ptr));
    size_t label = read_label(label_ptr);
    return label & (~(ALIGNMENT - 1));
}

static inline size_t read_alloc (void *label_ptr) {
    REQUIRES(label_ptr != NULL);
    REQUIRES(in_heap(label_ptr));
    REQUIRES(is_aligned(label_ptr));
    REQUIRES(is_valid_label(label_ptr));
    size_t label = read_label(label_ptr);
    return label & 0x1;
}

static inline void write_label(void *label_ptr, size_t label) {
    *((size_t *) label_ptr) = label;
}

static inline void *get_header_ptr (void *ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr - SIZE_T_SIZE);
}

static inline void *get_footer_ptr (void *ptr, size_t size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));
    REQUIRES(size >= SIZE_T_SIZE);

    return (void *)((uintptr_t) ptr + size - 2 * SIZE_T_SIZE);
}

static inline void *get_prev_footer_ptr (void *ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr - 2 * SIZE_T_SIZE);
}

static inline void *get_next_header_ptr (void *ptr, size_t size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr + size - SIZE_T_SIZE);
}

static inline void *get_prev_header_ptr (void *ptr, size_t prev_size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr - prev_size - SIZE_T_SIZE);
}

static inline void *get_next_footer_ptr (void *ptr, size_t size, size_t next_size) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    REQUIRES(is_aligned(ptr));

    return (void *)((uintptr_t) ptr + size + next_size - 2 * SIZE_T_SIZE);
}




static inline void *increment_pointer(void *ptr, size_t inc) {
    return (void *)((uintptr_t) ptr + inc);
}



static inline void write_header_footer(void *ptr, size_t size, size_t alloc) {
    REQUIRES(ptr != NULL);
    void *header = get_header_ptr(ptr);
    void *footer = get_footer_ptr(ptr, size);
    REQUIRES(in_heap(header));
    REQUIRES(is_aligned(header));
    REQUIRES(in_heap(footer));
    REQUIRES(is_aligned(footer));
    size_t label = pack(size, alloc);
    write_label(header, label);
    write_label(footer, label);
    return;
}



static inline void print_heap (void) {
    void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi();
    dbg_printf("lo: %lx\thi: %lx\tsize: %zx\n", (uintptr_t) heap_lo, (uintptr_t) heap_hi, mem_heapsize());
    void *p = increment_pointer(heap_lo, SIZE_T_SIZE);
    dbg_printf("|");
    while (p < heap_hi) {
        void *header = get_header_ptr(p);
        size_t size = read_size(header);
        dbg_printf(" %lx %zx %zd |", (uintptr_t) p, size, read_alloc(header));
        p = increment_pointer(p, size);
    }
    dbg_printf("\n");
    return;
}

static inline void swap_alloc (void *ptr) {
    REQUIRES(ptr != NULL);
    void *header = get_header_ptr(ptr);
    size_t size = read_size(header);
    void *footer = get_footer_ptr(ptr, size);
    REQUIRES(header != NULL);
    REQUIRES(in_heap(header) && in_heap(footer));
    REQUIRES(is_aligned(header) && is_aligned(footer));
    REQUIRES(is_valid_label(header) && is_valid_label(footer));
    /* swap the header's alloc bit */
    *((size_t *) header) ^= 0x1;
    *((size_t *) footer) ^= 0x1;
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
    // // print_heap_info();
    // void *heap_lo = mem_heap_lo();
    // size_t heap_size = mem_heapsize();
    // *((size_t *) heap_lo) = pack(heap_size, 0);
    // checkheap(1);
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    checkheap(1);  // Let's make sure the heap is ok!
    /* check if there is any free block */
    void *p = increment_pointer(mem_heap_lo(), SIZE_T_SIZE);
    size_t required_size = ALIGN(size) + 2 * SIZE_T_SIZE;
    dbg_printf("malloc: %zx %zx\n", size, required_size);
    /* search through the heap */
    while (p < mem_heap_hi()) {
        void *header = get_header_ptr(p);
        size_t block_size = read_size(header);
        if (!read_alloc(header) && block_size >= required_size) {
            /* found a free space that has enough space */
            write_header_footer(p, required_size, 1);
            /* split the block */
            if (block_size > required_size) {
                size_t remain_size = block_size - required_size;
                write_header_footer(increment_pointer(p, required_size), remain_size, 0);
            }

            checkheap(1);
            // print_heap();
            return p;
        }
        /* increment p */
        p = increment_pointer(p, block_size);
    }
    /* no free block */
    void *brkp;
    if ((brkp = mem_sbrk(required_size)) == 0) {
        /* mem_sbrk failed */
        dbg_printf("error: mem_sbrk failed");
        return NULL;
    }

    p = increment_pointer(brkp, SIZE_T_SIZE);

    write_header_footer(p, required_size, 1);
    
    // dbg_printf("get: %lx\n", (uintptr_t) p);
    checkheap(1);
    // print_heap();
    return p;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) return;
    dbg_printf("free: %lx\n", (uintptr_t) ptr);
    void *header = get_header_ptr(ptr);
    size_t size = read_size(header);
    void *prev_footer = get_prev_footer_ptr(ptr);
    void *next_header = get_next_header_ptr(ptr, size);
    /* if both prev and next are free */
    if ((in_heap(prev_footer) && !read_alloc(prev_footer)) &&
        (in_heap(next_header) && !read_alloc(next_header))) {
        size_t prev_size = read_size(prev_footer);
        size_t next_size = read_size(next_header);
        void *prev_header = get_prev_header_ptr(ptr, prev_size);
        void *next_footer = get_next_footer_ptr(ptr, size, next_size);
        size_t label = size + prev_size + next_size;
        write_label(prev_header, label);
        write_label(next_footer, label);
    }
    /* if only the prev is free */
    else if (in_heap(prev_footer) && !read_alloc(prev_footer)) {
        size_t prev_size = read_size(prev_footer);
        void *prev_header = get_prev_header_ptr(ptr, prev_size);
        void *footer = get_footer_ptr(ptr, size);
        size_t label = size + prev_size;
        write_label(prev_header, label);
        write_label(footer, label);
    }
    /* if only the next is free */
    else if (in_heap(next_header) && !read_alloc(next_header)) {
        size_t next_size = read_size(next_header);
        void *next_footer = get_next_footer_ptr(ptr, size, next_size);
        size_t label = size + next_size;
        write_label(header, label);
        write_label(next_footer, label);
    }
    /* otherwise, only the current block is free */
    else {
        swap_alloc(ptr);
    }
    // print_heap();
    return;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    REQUIRES(oldptr != NULL || size != 0);
    dbg_printf("realloc: %lx %zx\n", (uintptr_t) oldptr, size);
    size_t oldsize;
    void *newptr;
    /* If oldptr is NULL, then this is just malloc */
    if (oldptr == NULL) {
        return malloc(size);
    }
    /* If size == 0 then this is just free, and we return NULL */
    if (size == 0) {
        free(oldptr);
        return NULL;
    }
    /* If realloc() fails the original block is left untouched */
    if ((newptr = malloc(size)) == NULL) return NULL;
    
    /* Copy the old data. */
    void *old_header = get_header_ptr(oldptr);
    oldsize = read_size(old_header);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);
    // print_heap();

    return newptr;
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
    void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi();
    if (heap_hi < heap_lo) return 0;
    if (heap_hi < increment_pointer(heap_lo, SIZE_T_SIZE)) {
        dbg_printf("error: heap size is smaller than double word\n");
        return -1;
    }
    void *p = increment_pointer(heap_lo, SIZE_T_SIZE);
    void *header, *footer;
    size_t size;
    size_t prev_free_flag = 0;
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
            dbg_printf("error: header is not the same as footer. header: %zx, footer: %zx\n", read_label(header), read_label(footer));
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
    if (p != (void *)((uintptr_t) heap_hi + 1 + SIZE_T_SIZE)) {
        dbg_printf("error: headers are corrupted\n");
        return -1;
    }
    // dbg_printf("hi: %lx\tp: %lx\n", (uintptr_t) heap_hi + 1 + SIZE_T_SIZE, (uintptr_t) p);

    verbose = verbose;
    return 0;
}
