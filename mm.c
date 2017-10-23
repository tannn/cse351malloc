/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"


/* Team structure */
team_t team = {
    "implicit first fit", 
    "Unknown Person", "anonymous",
    "", ""
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       16       /* word size (bytes) */  
#define DSIZE       32       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<48)  /* initial heap size (bytes) */
#define OVERHEAD    32       /* overhead of header and footer (bytes) */

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
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_LINK(bp)    ( (char *)(bp) )
#define PREV_LINK(bp)    ( (char *)(bp) - 0x8 )

#define GET_NEXT_LINK(bp) (char *) ( GET( bp ) & 0xFFFFFFFF  )
#define GET_PREV_LINK(bp) (char *) ( GET( bp - 0x8 ) &  0xFFFFFFFF )

/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
static char *head_link; /* pointer to head of the linked list */

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;


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
	fprintf(stderr,"***MALLOC***\n");
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = DSIZE + OVERHEAD;
    else
	asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
	fprintf(stderr,"MALLOC searching for size %d\n",asize); 
   if ((bp = find_fit(asize)) != NULL) {
	place(bp, asize);
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	return NULL;
    //PUT(NEXT_LINK(bp),NULL);
    //PUT(PREV_LINK(bp),NULL);
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
	fprintf(stderr,"***FREE***\n");
    size_t size = GET_SIZE(HDRP(bp));
	fprintf(stderr,"Freeing\n");
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    if(head_link == NULL) {
       fprintf(stderr,"Assigning Head...\n");
	head_link = bp;
	PUT(NEXT_LINK(head_link),NULL);
	PUT(PREV_LINK(head_link),NULL);
      fprintf(stderr,"Head Link: %p\n",head_link);
    }
    else {
	
        PUT(NEXT_LINK(bp),head_link);
	PUT(PREV_LINK(bp),NULL);
        PUT(PREV_LINK(head_link),bp);
//	head_link = bp;

	fprintf(stderr,"Freeing done\n");
	fprintf(stderr,"Head: %p\n",(void *) head_link);
	fprintf(stderr,"BP: %p\n",(void *) bp);
	fprintf(stderr,"NEW NEXT: %p\n",(void *)GET_NEXT_LINK(bp));
	fprintf(stderr,"NEW PREV: %p\n",(void *)GET_PREV_LINK(bp));
    	fprintf(stderr,"NExt: %p\n",(void *) NEXT_LINK(bp));
	fprintf(stderr,"Prev: %p\n",(void *) PREV_LINK(bp));

	head_link = bp;	
	}
	fprintf(stderr,"COALESCE is running from FREE\n"); 
   coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
	fprintf(stderr,"***REALLOC***\n");
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
	printf("ERROR: mm_malloc failed in mm_realloc\n");
	exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
	fprintf(stderr,"***CHECK HEAP***\n");
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
	fprintf(stderr,"***EXTEND HEAP***\n");
    char *bp;
    size_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
	
	fprintf(stderr,"Extending - setting header");
	if(head_link != NULL) {
	PUT(NEXT_LINK(bp),head_link);
	PUT(PREV_LINK(head_link),bp);
	PUT(PREV_LINK(bp),NULL);
	}
	else {
	PUT(NEXT_LINK(bp),NULL);
	PUT(PREV_LINK(bp),NULL);
	}
	head_link = bp;
	

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
   	fprintf(stderr,"COALESCE is running from EXTEND_HEAP\n");
	 return coalesce(bp);
//	return bp;
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
fprintf(stderr,"***PLACE START***\n");
    size_t csize = GET_SIZE(HDRP(bp));
//	printf(stderr,"PLACE CSIZE: %d | DIFF: %d | REQ: %d\n",csize,(csize - asize),(DSIZE + OVERHEAD));    
    void* nxt =(void *) GET_NEXT_LINK(bp);
    void* prv =(void *) GET_PREV_LINK(bp);
	fprintf(stderr,"PLACE asize: %d | csize: %d\n");
    fprintf(stderr,"PLACE Header: %p\n",(void *) head_link);
    fprintf(stderr,"PLACE BP: %p\n",(void *)bp);
    fprintf(stderr,"PLACE Next: %p\n",(void *) nxt);
    fprintf(stderr,"PLACE Prev: %p\n",(void *) prv);
    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
	fprintf(stderr,"place: The first case occurred\n");
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
    fprintf(stderr,"PLACE NEW BP: %p\n",(void *) bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));

        if(nxt != NULL) {

	fprintf(stderr,"Step 1\n");

	    PUT(NEXT_LINK(bp),nxt);

	fprintf(stderr,"Step 2\n");

	    PUT(PREV_LINK(nxt),bp);

	fprintf(stderr,"Step 3\n");
	}
	else {
		fprintf(stderr,"PLACE: Next is null, forcing\n");
		PUT(NEXT_LINK(bp),NULL);
	}

        if(prv != NULL) {
	fprintf(stderr,"Step 4\n");

	    PUT(NEXT_LINK(prv),bp);

	fprintf(stderr,"Step 5\n");

	    PUT(PREV_LINK(bp),prv);
	fprintf(stderr,"Step 6\n");
	}

	else {
		fprintf(stderr,"PLACE: Prev is null, forcing\n");
		PUT(PREV_LINK(bp),NULL);
		if(GET_PREV_LINK(head_link) != NULL) PUT(PREV_LINK(head_link),NULL);
		head_link = bp;
	}

	if(bp == head_link) {
		fprintf(stderr,"PLACE: Head placed...");
	        
		if(GET_NEXT_LINK(bp) != NULL) {
			//head_link = GET_NEXT_LINK(bp);
			PUT(PREV_LINK(head_link),NULL);
		}
		else {
			head_link = NULL;
		}
		//head_link = bp;
		//PUT(NEXT_LINK(head_link),NULL);
		//head_link = bp;
	}

	if(head_link != NULL && nxt == NULL && prv == NULL) {
		
	fprintf(stderr,"msg1m1\n");
		PUT(NEXT_LINK(bp),head_link);
	fprintf(stderr,"msg1m2\n");
		PUT(PREV_LINK(head_link),bp);
	fprintf(stderr,"msg1m3\n");
		head_link = bp;
	}

	if(head_link == NULL && nxt == NULL && prv == NULL) {
		head_link = bp;
	}
	//fprintf(stderr,"***PLACE END***\n");  
  }
    else {

	fprintf(stderr,"PLACE: The other case occurred\n");
	/*
	if(nxt != NULL && nxt != 0x1010101 && prv != NULL && prv != 0x1010101) {
		fprintf(stderr,"Case 2, break repaired");
		PUT(NEXT_LINK(prv),nxt);
		PUT(PREV_LINK(nxt),prv);
        }
	if((nxt == NULL || nxt == 0x1010101) && prv != NULL && prv != 0x1010101) {
		fprintf(stderr,"Case 2, tail assigned");
		PUT(NEXT_LINK(prv),0x00000000);
	}*/
	
	//case 1: next & prev are not null
		//repair the break
	//case 2: next is null, prev is not
		//tail was assigned: do nothing
	//case 3: next is not, prev is null
		//header was assigned: point to null
	//case 4: both are null
		//undefined: do nothing

	/*PUT(NEXT_LINK(prv),nxt);
	PUT(PREV_LINK(nxt),prv);*/

	if(nxt != NULL && prv != NULL && (char *) GET(nxt) != NULL && (char *) GET(prv) != NULL) {
		fprintf(stderr,"PLACE: Repairing break...\n");
		PUT(NEXT_LINK(prv),nxt);
		PUT(PREV_LINK(nxt),prv);
	}
	if(nxt != NULL && prv == NULL) {
		fprintf(stderr,"PLACE: Link head was placed...\n");
		head_link = nxt;
		fprintf(stderr,"outside test 1\n");
		PUT(PREV_LINK(head_link),NULL);
		fprintf(stderr,"PLACE: Outside test 2\n");
	/*	if(GET_NEXT_LINK(head_link) != NULL) {
			fprintf(stderr,"Head was not the last entry");
			PUT(GET_NEXT_LINK(head_link)
		}*/	
	}
	fprintf(stderr,"PLACE: Outside test 3\n");	
	if(nxt == NULL && prv == NULL) {
		head_link = NULL;
	}
	fprintf(stderr,"PLACE: Outside Test 4\n");
 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
	fprintf(stderr,"***PLACE END***\n");
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
	fprintf(stderr,"***FIND FIT***\n");
    /* first fit search */
    void *bp;

	fprintf(stderr,"Finding Fit\n");

    for (bp = head_link;NEXT_LINK(bp) != NULL && GET_NEXT_LINK(bp) != head_link && GET_NEXT_LINK(bp) != NULL && GET_NEXT_LINK(bp) != 0x1010101; bp = GET_NEXT_LINK(bp)) {
	fprintf(stderr,"Size: %d\n",GET_SIZE(HDRP(bp)));
	fprintf(stderr,"Head: %p\n",(void *)head_link);
	fprintf(stderr,"BP: %p\n",(void *)bp);
	fprintf(stderr,"Next: %p\n",(void *)GET_NEXT_LINK(bp));
	fprintf(stderr,"Prev: %p\n",(void *)GET_PREV_LINK(bp));

	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
		fprintf(stderr,"FIT FOUND\n");
	    return bp;
	}
    } 
    fprintf(stderr,"No fit found\n");
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */

static void *coalesce(void *bp) 
{
	fprintf(stderr,"COALESCING. BP: %p\n",bp);

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));

	fprintf(stderr,"1\n");
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	fprintf(stderr,"2\n");
    size_t size = GET_SIZE(HDRP(bp));

	/*void* nxt_cur = GET_NEXT_LINK(bp);
	void* nxt_nxt = GET_NEXT_LINK(NEXT_BLKP(bp));
	void* prv_cur = GET_PREV_LINK(bp);
	void* prv_prv = GET_PREV_LINK(PREV_BLKP(bp));*/

//	fprintf(stderr,"COAL TOP: NXT CUR=%p | NXT NXT=%p\nPRV CUR=%p | PRV PRV=%p\n",nxt_cur,nxt_nxt,prv_cur,prv_prv);

//	fprintf(stderr,"COALESCING. BP: %p NEXT: %p PREV: %p | NXTBLK: %p PRVBLK: %p\n",bp,GET_NEXT_LINK(bp),GET_PREV_LINK(bp),NEXT_BLKP(bp),PREV_BLKP(bp));
	
	/*
		four cases
		case 1 - both allocated | they don't point to one another
		case 2 - neither are allocated and they both point to current
		case 3 - prev is not allocated and prev-points to current
		case 4 - prev is not allocated and next-points to current
		case 5 - next is not allocated and prev-points to current
		case 6 - next is not allocated and next-points to current 
	*/

	//case 1
	fprintf(stderr,"CO C1 Out");
	if((prev_alloc && next_alloc)) {
		fprintf(stderr,"CO C1\n");
		return bp;
	}


	//case 2
	fprintf(stderr,"CO C2 Out");
	if(!prev_alloc && !next_alloc && GET_NEXT_LINK(bp) == NEXT_BLKP(bp) && GET_PREV_LINK(bp) == PREV_BLKP(bp)) {
		fprintf(stderr,"CO C2 Enter\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(FTRP(NEXT_BLKP(bp)));		

		void* nxt = (void *) GET_NEXT_LINK(NEXT_BLKP(bp));
		void* prv = (void *) GET_PREV_LINK(PREV_BLKP(bp));
			fprintf(stderr,"CO C2 | NXT: %p PRV: %p BP: %p\n",nxt,prv,bp);
		bp = PREV_BLKP(bp);
	
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));	

		if(nxt != NULL) {
			PUT(NEXT_LINK(bp),nxt);
			PUT(PREV_LINK(nxt),bp);
		}
		else {
			PUT(NEXT_LINK(bp),NULL);
		}
		
		if(prv != NULL) {	
			PUT(PREV_LINK(bp),prv);
			PUT(NEXT_LINK(prv),bp);
		}
		else {
			PUT(PREV_LINK(bp),NULL);
		}

		return bp;
	}	

	//case 3
	fprintf(stderr,"CO C3 Out");
	if(!prev_alloc && next_alloc && PREV_BLKP(bp) != NULL  && GET_PREV_LINK(bp) == PREV_BLKP(bp)) {
		fprintf(stderr,"CO C3 Enter\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		void* nxt = (void *) GET_NEXT_LINK(bp);
		void* prv = (void *) GET_PREV_LINK(PREV_BLKP(bp));
			fprintf(stderr,"CO C3 | NXT: %p PRV: %p BP: %p\n",nxt,prv,bp);
		bp = PREV_BLKP(bp);

		fprintf(stderr,"c3m1 bp: %p nxt: %p prv: %p prvp: %p nxtp: %p\n",bp,GET_NEXT_LINK(bp),GET_PREV_LINK(bp),PREV_BLKP(bp),NEXT_BLKP(bp));

		PUT(FTRP(bp), PACK(size,0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));

		fprintf(stderr,"c3m2");

		if(nxt != NULL) {
			PUT(NEXT_LINK(bp),nxt);
			PUT(PREV_LINK(nxt),bp);
		}
		else {
			PUT(NEXT_LINK(bp),NULL);
		}
		
		if(prv != NULL) {
			PUT(PREV_LINK(bp),prv);
			PUT(NEXT_LINK(prv),bp);
		}
		else {
			PUT(PREV_LINK(bp),NULL);
			head_link = bp;
			fprintf(stderr,"COALESCE: Head collapsed; resetting");
		}

		fprintf(stderr,"c3m3");

		return bp;
	}

	//case 4
	fprintf(stderr,"CO C4 Out");
	if(!prev_alloc && next_alloc && GET_NEXT_LINK(bp) == PREV_BLKP(bp)) {
		fprintf(stderr,"CO C4 Enter\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		void* nxt = (void *) GET_NEXT_LINK(PREV_BLKP(bp));
		void* prv = (void *) GET_PREV_LINK(bp);

		fprintf(stderr,"CO C6 | NXT: %p PRV: %p BP: %p\n",nxt,prv,bp);

		bp = PREV_BLKP(bp);

		PUT(FTRP(bp), PACK(size,0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));

		if(nxt != NULL) {

			PUT(NEXT_LINK(bp),nxt);
			PUT(PREV_LINK(nxt),bp);
		}
		else {
			PUT(NEXT_LINK(bp),NULL);

		}
		
		if(prv != NULL) {
			PUT(PREV_LINK(bp),prv);
			PUT(NEXT_LINK(prv),bp);
		}
		else {
			PUT(PREV_LINK(bp),NULL);
			head_link = bp;
			fprintf(stderr,"COALESCE: C4 collapsed head; resetting");
		}

		return bp;
	}

	//case 5
	fprintf(stderr,"CO C5 Out");
	if(!next_alloc && prev_alloc && GET_PREV_LINK(bp) == NEXT_BLKP(bp)) {
		fprintf(stderr,"CO C5 Enter\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		
		void* nxt = (void *) GET_PREV_LINK(NEXT_BLKP(bp));
		void* prv = (void *) GET_NEXT_LINK(bp);

		fprintf(stderr,"CO C4 | NXT: %p PRV: %p BP: %p\n",nxt,prv,bp);
		
		PUT(HDRP(bp), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));

		if(nxt != NULL) {
			PUT(NEXT_LINK(bp),nxt);
			PUT(PREV_LINK(nxt),bp);	
		}
		else {
			PUT(NEXT_LINK(bp),NULL);
		}
	}

	//case 6
	fprintf(stderr,"CO C6 Out");
	if(!next_alloc && prev_alloc && GET_NEXT_LINK(bp) == NEXT_BLKP(bp)) {
		fprintf(stderr,"CO C6 Enter\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));	
	
		void* nxt = (void *) GET_NEXT_LINK(NEXT_BLKP(bp));
		void* prv = (void *) GET_PREV_LINK(bp);
			fprintf(stderr,"CO C4 | NXT: %p PRV: %p BP %p\n",nxt,prv,bp);
		
		PUT(HDRP(bp), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));
	
		if(nxt != NULL) {
			PUT(NEXT_LINK(bp),nxt);
			PUT(PREV_LINK(nxt),bp);
		}
		else {
			PUT(NEXT_LINK(bp),NULL);
		}
		//PUT(PREV_LINK(bp),prv);
	}
	fprintf(stderr,"FINISHED COALESCING - NO CASE\n");
    return bp;
}


static void printblock(void *bp) 
{
	fprintf(stderr,"***PRINT BLOCK***\n");
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
	fprintf(stderr,"***CHECK BLOCK***\n");
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}

