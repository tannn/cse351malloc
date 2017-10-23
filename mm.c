/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Ceal Team 6",
    /* note that we will add a 10% bonus for working alone */
    /* First member's full name */
    "Tanner Marino",
    /* First member's email address */
    "tmarino@cse.unl.edu",
    /* Second member's full name (leave blank if none) */
    "Michael Shanahan",
    /* Second member's email address (leave blank if none) */
    "mshanahan@cse.unl.edu",
    /* note that we will deduct a 10% penalty for a team of three members */
    /* Third member's full name (leave blank if none) */
    "",
    /* Third member's email address (leave blank if none) */
    ""
};

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  16  /* initial heap size (bytes) */
#define OVERHEAD    24       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)  ((void *)(bp) - WSIZE)                                                    
#define FTRP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)       

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_FREE(bp)  (*(void **)(bp + WSIZE))                                            
#define PREV_FREE(bp)  (*(void **)(bp)) 
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))                                  
#define PREV_BLKP(bp)  ((void *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))
#define ALIGN(size) (((size) + 7) & ~0x7)
/* $end mallocmacros */

/* Global variables */
static char *heap_listp; //pointer to first block
static char *head; //pointer to first free block

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add(void *bp);
static void delete(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(2*OVERHEAD)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp + DSIZE, 0);                                 
    PUT(heap_listp + 3*WSIZE, 0);    
    PUT(heap_listp+OVERHEAD, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+ 3*DSIZE, PACK(0, 1));   /* epilogue header */
    head = heap_listp + DSIZE;  

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
	return NULL;

    asize = MAX(ALIGN(size) + DSIZE, OVERHEAD);                 
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	return NULL;
    place(bp, asize);
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    if(bp == NULL)                                           
    return;

    size_t size = GET_SIZE(HDRP(bp));                           

    PUT(HDRP(bp), PACK(size, 0));                               
    PUT(FTRP(bp), PACK(size, 0));                               
    coalesce(bp);    

}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    //free block if negative or zero
    if(size <= 0){
        mm_free(ptr);
        return 0;
    }

    if(ptr == NULL)
    return mm_malloc(size);

    size_t copySize;
    void *newp;
    size_t newSize = MAX(ALIGN(size) + DSIZE, OVERHEAD); //adjusted

    //get size of old block
    copySize = GET_SIZE(HDRP(ptr));

    int difference = copySize - newSize;

    if(copySize == newSize)
    return ptr;

    //shrink block if needed
    if(newSize <= copySize){
        //if valid new block, return old pointer
        if(difference <= OVERHEAD)
        return ptr;

        PUT(HDRP(NEXT_BLKP(ptr)), PACK(difference, 1)); //update size in new block
        PUT(HDRP(ptr), PACK(size, 1)); //update size for new block
        PUT(FTRP(ptr), PACK(size, 1)); 
        mm_free(NEXT_BLKP(ptr)); //free next block
        return ptr;
    } else {

	    if(size < copySize)
	    copySize = size;

	    newp = mm_malloc(size); //new block allocated if needed

	    if(!newp)
	    return 0;
	    
	    memcpy(newp, ptr, copySize); //move old date to new block
	    mm_free(ptr); //free old block
	    return newp;
	}
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
	printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= OVERHEAD) { 
	    delete(bp);
	    PUT(HDRP(bp), PACK(asize, 1));
	    PUT(FTRP(bp), PACK(asize, 1));
	    bp = NEXT_BLKP(bp);
	    PUT(HDRP(bp), PACK(csize-asize, 0));
	    PUT(FTRP(bp), PACK(csize-asize, 0));
	    coalesce(bp);
    }
    else { 
	    delete(bp);
	    PUT(HDRP(bp), PACK(csize, 1));
	    PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    void *bp;

    for(bp = head; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE(bp)){                    
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
		    return bp;
		}
    }
    return NULL; 
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t previous_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));       
    size_t next__alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));                                 
    size_t size = GET_SIZE(HDRP(bp));          

    if(previous_alloc == NULL)
    previous_alloc = PREV_BLKP(bp) == bp;                                          

    if(previous_alloc && !next__alloc){     
        delete(NEXT_BLKP(bp));                                               
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  
        PUT(HDRP(bp), PACK(size, 0));                                                       
        PUT(FTRP(bp), PACK(size, 0));                                                                     
    }
    else if(!previous_alloc && next__alloc){                                                
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                                              
        bp = PREV_BLKP(bp);                                                              
        delete(bp);                                                                   
        PUT(HDRP(bp), PACK(size, 0));                                                      
        PUT(FTRP(bp), PACK(size, 0));                                                      
    }
    else if(!previous_alloc && !next__alloc){                                        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));       
        delete(PREV_BLKP(bp));                                                    
        delete(NEXT_BLKP(bp));                                                    
        bp = PREV_BLKP(bp);                                                          
        PUT(HDRP(bp), PACK(size, 0));                                                
        PUT(FTRP(bp), PACK(size, 0));                                                
    }
    add(bp);                                                                   
    return bp;
}

/*
 * add - add block to beginning of free list
 */
static void add(void *bp){
	PREV_FREE(bp) = NULL;
	PREV_FREE(head) = bp;  
    NEXT_FREE(bp) = head;                                                                                  
    head = bp;                                                                       
}

/*
 * delete - remove block to heap
 */
static void delete(void *bp){
	PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
    if(PREV_FREE(bp) != NULL){                              
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp); 
    }else{
        head = NEXT_FREE(bp);                                                        
    }                                      
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
	   hsize, (halloc ? 'a' : 'f'), 
	   fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}
