/*
 * mm.c
 *
 * Name: Robert Ramstad, Xinchang Xiong
 *
 * NOTE TO STUDENTS: This first submission was simply us understanding and implementing a poor mans memory function. We opted
 * to use the example from the book. As you can tell we changed the macros into functions (as required by the instructions) and then did the same implementation as the textbook.
 * Realloc was not implemented in the book, so I used the instructions and my previous implementations of the other functions (Malloc and Free) to make our Realloc fully operational.
 * The next steps we will have to take is to start optimizing the functions so that we can get better throughput..
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* Global Variables */
#define WSIZE 8 /* Word and header/footer size (bytes) */
#define DSIZE 16 /* Double word size (bytes) */
#define CHUNKSIZE (1<<24) /* Extend heap by this amount (bytes) */
static char* heap_listp = 0;

/* What is the correct alignment? */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}
/* Textbook Macros */

static size_t MIN(size_t x,size_t y){
	return( ((x) < (y)? (x) : (y)) );
}
static size_t MAX(size_t x,size_t y){
	return( ((x) > (y)? (x) : (y)) );
}
static size_t PACK(size_t size, int alloc){
	return( ((size) | (alloc)) );
}
static size_t GET(void* p){ //function for get
	return( (*(size_t *)(p)) );
}

static void PUT(void* p, size_t val) {
	(*(size_t *)(p) = (val));
}

static size_t GET_SIZE(void* p){
	return( (GET(p) & ~0x7) );
}

static size_t GET_ALLOC(void* p){
	return( (GET(p) & 0x1) );
}

static void* HDRP(void* bp){
	return( ((char *)(bp) - WSIZE) );
}

static void* FTRP(void* bp){
	return( ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) );
}

static void* NEXT_BLKP(void* bp){
	return( ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) );
}

static void* PREV_BLKP(void* bp){
	return( ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) );
}

static void *coalesce(void *bp){ // boundary tag coalesching to merge blocks (from textbook)
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) { /* Case 1 */
		return bp;
	}

	else if (prev_alloc && !next_alloc) { /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
	}
	else if (!prev_alloc && next_alloc) { /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else { /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return bp;
}

static void *extend_heap(size_t words) //extends the heap with new free block(from textbook)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1){
		return NULL;}

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

static void* find_fit(size_t asize){ //Finds a fitting block of size "asize" (from textbook)
	/* First fit search */
	void *bp;

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
			return bp;
		}
	}
	return NULL;
}

static void place(void *bp, size_t asize)
 {
	size_t csize = GET_SIZE(HDRP(bp));

	if ((csize - asize) >= (2*DSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
	}
	else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}
/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    /* IMPLEMENT THIS */

    /* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
 		return false;
	}
 	PUT(heap_listp, 0); /* Alignment padding */
 	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
 	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
 	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
 	heap_listp += (2*WSIZE);

 	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
 	if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
 		return false;
 	}
 	return true;
    
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    /* IMPLEMENT THIS */
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;

	/* Ignore spurious requests */
	if (size == 0){
		return NULL;
		}

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE){
		asize = 2*DSIZE;
		}
	else{
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
		}

	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize,CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
		return NULL;
	}
	place(bp, asize);
	return bp;
}

/*
 * free
 */
void free(void* ptr)
{
    /* IMPLEMENT THIS */ 
	size_t size = GET_SIZE(HDRP(ptr));
    
	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{

	size_t oldsize;
	char *newptr;
    /* IMPLEMENT THIS */
	if (oldptr == NULL){
		return( malloc(size) );
	}
	
	if (size == 0){
		free(oldptr);
	}
	
	oldsize = GET_SIZE(HDRP(oldptr));

	newptr = malloc(size);
	memcpy(newptr, oldptr, MIN(size, oldsize));
	free(oldptr);
	
	return newptr;
	
	 
	
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */
#endif /* DEBUG */
    return true;
}
