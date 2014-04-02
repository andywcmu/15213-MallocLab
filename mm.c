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
static inline int is_valid_header(void *header_ptr) {
    size_t header = *((size_t *) header_ptr);
    return (header & (~(ALIGNMENT - 1))) > 1;
}


/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Return the size of the given block in multiples of the word size
// static inline unsigned int block_size(const uint32_t* block) {
//     REQUIRES(block != NULL);
//     REQUIRES(in_heap(block));

//     return (block[0] & 0x3FFFFFFF);
// }

// Return true if the block is free, false otherwise
// static inline int block_free(const uint32_t* block) {
//     REQUIRES(block != NULL);
//     REQUIRES(in_heap(block));

//     return !(block[0] & 0x40000000);
// }

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
// static inline void block_mark(uint32_t* block, int free) {
//     REQUIRES(block != NULL);
//     REQUIRES(in_heap(block));

//     unsigned int next = block_size(block) + 1;
//     block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
//     block[next] = block[0];
// }

// Return a pointer to the memory malloc should return
// static inline uint32_t* block_mem(uint32_t* const block) {
//     REQUIRES(block != NULL);
//     REQUIRES(in_heap(block));
//     REQUIRES(is_aligned(block + 1));

//     return block + 1;
// }

// Return the header to the previous block
// static inline uint32_t* block_prev(uint32_t* const block) {
//     REQUIRES(block != NULL);
//     REQUIRES(in_heap(block));

//     return block - block_size(block - 1) - 1;
// }

// Return the header to the next block
// static inline uint32_t* block_next(uint32_t* const block) {
//     REQUIRES(block != NULL);
//     REQUIRES(in_heap(block));

//     return block + block_size(block) + 1;
// }

// pack a size and a allocated status into a word
static inline size_t pack (size_t size, size_t alloc) {
    REQUIRES((size & (ALIGNMENT - 1)) == 0);
    REQUIRES(alloc <= 1);
    return size | alloc;
}

static inline void *get_header_ptr (void *ptr) {
    return (void *)((uintptr_t) ptr - SIZE_T_SIZE);
}

static inline size_t get_header (void *ptr) {
    REQUIRES(ptr != NULL);
    void *header_ptr = get_header_ptr(ptr);
    REQUIRES(is_valid_header(header_ptr));
    return *((size_t *) header_ptr);
}

static inline size_t get_size (void *ptr) {
    REQUIRES(ptr != NULL);
    size_t header = get_header(ptr);
    return header & (~(ALIGNMENT - 1));
}

static inline size_t get_alloc (void *ptr) {
    REQUIRES(ptr != NULL);
    size_t header = get_header(ptr);
    return header & 0x1;
}

static inline void *increment_pointer(void *ptr, size_t inc) {
    return (void *)((uintptr_t) ptr + inc);
}

static inline void write_header(void *ptr, size_t size, size_t alloc) {
    REQUIRES(ptr != NULL);
    void *header_ptr = get_header_ptr(ptr);
    REQUIRES(in_heap(header_ptr));
    REQUIRES(is_aligned(header_ptr));
    *((size_t *) header_ptr) = pack(size, alloc);
    return;
}

static inline void print_heap (void) {
    void *heap_lo = mem_heap_lo();
    void *heap_hi = mem_heap_hi();
    // dbg_printf("lo: %lx\thi: %lx\tsize: %zd\n", (uintptr_t) heap_lo, (uintptr_t) heap_hi, mem_heapsize());
    void *p = increment_pointer(heap_lo, SIZE_T_SIZE);
    dbg_printf("|");
    while (p < heap_hi) {
        size_t size = get_size(p);
        dbg_printf(" %lx %zx %zd |", (uintptr_t) p, size, get_alloc(p));
        p = increment_pointer(p, size);
    }
    dbg_printf("\n");
    return;
}

static inline void swap_alloc (void *ptr) {
    REQUIRES(ptr != NULL);
    void *header_ptr = get_header_ptr(ptr);
    REQUIRES(header_ptr != NULL);
    REQUIRES(in_heap(header_ptr));
    REQUIRES(is_aligned(header_ptr));
    REQUIRES(is_valid_header(header_ptr));
    /* swap the header's alloc bit */
    *((size_t *) header_ptr) ^= 0x1;
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
    size_t required_size = ALIGN(size) + SIZE_T_SIZE;
    dbg_printf("malloc: %zx %zx\n", size, required_size);
    /* search through the heap */
    while (p < mem_heap_hi()) {
        size_t block_size = get_size(p);
        if (!get_alloc(p) && block_size >= required_size) {
            /* found a free space that has enough space */
            write_header(p, required_size, 1);
            /* split the block */
            if (block_size > required_size) {
                size_t remain_size = block_size - required_size;
                write_header(increment_pointer(p, required_size), remain_size, 0);
            }

            checkheap(1);
            print_heap();
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
    write_header(p, required_size, 1);
    
    dbg_printf("get: %lx\n", (uintptr_t) p);
    checkheap(1);
    print_heap();
    return p;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) return;
    dbg_printf("free: %lx\n", (uintptr_t) ptr);
    swap_alloc(ptr);
    print_heap();
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
    oldsize = get_size(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);
    print_heap();

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
    void *p = increment_pointer(mem_heap_lo(), SIZE_T_SIZE);
    void *heap_hi = mem_heap_hi();
    /* traverse the heap */
    while (p < heap_hi) {
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
        if (get_alloc(p) > 1) {
            dbg_printf("error: headers are corrupted\n");
            return -1;
        }
        p = increment_pointer(p, get_size(p));
    }
    /* check if the pointer p ends at the end of the last block */
    if (p != (void *)((uintptr_t) heap_hi + 1 + SIZE_T_SIZE)) {
        dbg_printf("error: headers are corrupted\n");
        return -1;
    }
    verbose = verbose;
    return 0;
}
