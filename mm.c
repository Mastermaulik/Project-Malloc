/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Bit Ninjas",
	/* First member's full name */
	"Maulik Soneji",
	/* First member's email address */
	"201201122@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Harsh Patel",
	/* Second member's email address (leave blank if none) */
	"201201134@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; 	/* Pointer to first block */  
int global_list=9;		//keeps track of the most optimum place for the block to be allocated.
int free_blcks=0;		//keeps track about the number of free blocks available to us which is initially zero.

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void remove_blck(void *bp);
static void add_blck(void *bp);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
    if ((heap_listp = mem_sbrk(14 * WSIZE)) == (void *)-1)
		return (-1);
    
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(12*WSIZE, 1)); /* Prologue header */
	
    //initialize the addresses at the segregated free lists to zero to indicate that they arent assigned any address yet	
    int i;
    for(i = 2; i < 12; i++)
    {
        PUT(heap_listp + (i*WSIZE), 0);
    }

    PUT(heap_listp + (12 * WSIZE), PACK(12*WSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (13 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

    // Extend the empty heap with a free block of CHUNKSIZE bytes so that we can have our first free block 
     if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
    
      return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
         if ((bp = find_fit(asize)) != NULL)
        {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 *Requires:
 *A free block in the heap whose address would be stored in the
 *segregated free list.
 *
 *Effect:
 *We add the free block's address to the segregated free list so that we
 *can keep a track of the free blocks of a particular size.
 *
 *
*/
static void add_blck(void *bp)
 {
    
    void *next_blck;
    void *prev_blck;

    int size = GET_SIZE(HDRP(bp));

    int local_list = size / 128;//we store the addresses according to the sizes
    
    free_blcks++;// new block addded
    if(local_list > 9)
    {
        local_list = 9;
    }

    //if global list > local list then we have a free block which is most recently added so we update the value of globallist
    if(global_list > local_list || global_list == 9){
        global_list = local_list;
    }

   
    char *current_blck = (char *)GET(heap_listp + (local_list * WSIZE));

    //if this is zero we have to jst put the address there
    if(current_blck == 0)
    {
        PUT(heap_listp + (local_list * WSIZE), (int)bp);//puts the address of the freeblock.
        PUT(bp, 0);//as this is the first block there is no previous blck
        PUT(bp+WSIZE, 0);// also the next block has not been set so thus put it to zero
    }

    //the if there is some address already
    else
    {
        prev_blck = (char *)GET(heap_listp + (local_list * WSIZE));

        //find where to put the address of the free block
        //we arrange it in such a way that the sizes of the free blcks are also arranged in an ascending way.
        for (; (int)current_blck != 0 && GET_SIZE(HDRP(current_blck)) < (unsigned)size; current_blck = (char *)GET(current_blck+WSIZE))
        {
            prev_blck = current_blck;
        }

        current_blck = prev_blck;

        next_blck = (char *)GET(current_blck + WSIZE);

        PUT(current_blck + WSIZE, (int)bp);

        if((int)next_blck != 0)
        {
            PUT(next_blck, (int)bp);
        }

        //set next and prev pointers of this block
        PUT(bp+WSIZE, (int)next_blck);
	PUT(bp, (int)current_blck);
        
    }
}
/*
 *Requires: A pointer to the free block which is now being allocated.
 *
 *Effects: As this block would now be getting allocated it has to removed from the
 *free lists that we had constructed to get track of all the free blocks
 *
 *
 *
*/
static void remove_blck(void *bp)
{
    //decrement a fre block because its now getting allocated
    free_blcks--;


    int size = GET_SIZE(HDRP(bp));

    int local_list = size / 128;

    if(local_list > 9)
    {
        local_list = 9;
    }

    // set up prev and next to store neighbour pointers
    size_t prev = GET(bp);
    size_t next = GET((char *)bp + WSIZE);

   
    if(prev == 0 && next == 0)
    {
        //set this list pointer to 0 indicating that it is the first block in the list
        PUT(heap_listp+(local_list * WSIZE), 0);
    }
     // prev is full and next is empty
    //set the next pointer of the previous block to zero
    else if (prev != 0 && next == 0)
    {
        PUT(((char *)prev + WSIZE), 0);
    }

    // set the prev pointer of the next block to zero
    else if (prev == 0 && next != 0)
    {
        PUT(heap_listp+(local_list * WSIZE), next);
        PUT((char *)next, 0);
    }
    // prev is full and next is full
    else
    {
       PUT(((char *)prev + WSIZE), next);
        PUT(((char *)next), prev);
    }
 }

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 *In our implementation, it first checks whether there are free blocks around the blk which is to
 *be reallocated. If so then it tries to collaesce with the free blocks and rellocate the block to
 *the new collaesced block
 *If the surrounding blocks are not free then it tries to find the right size by going through the list again(malloc again).
 */
void *
mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;

        size_t prevAlloc = GET_ALLOC(FTRP(PREV_BLKP(oldptr)));
        size_t nextAlloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr)));

        size_t oldSize = GET_SIZE(HDRP(oldptr));

        //adjusted size
        size_t asize;
        if (size <= DSIZE)
        {
            asize = 2*DSIZE;
        }
        else
        {
            asize =  DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
        }

        int change;//change indicates whether to search for a new block or to do some changes in the same block..

        //is new size is larger?
        if(oldSize  < size + DSIZE){ //DSIZE for header and footer
            change = 1;
        }
        else{
            change = 0;
        }

        void *newptr;
        // if size is 0, just call mm_free
        if (size == 0)
        {
            mm_free(ptr);
            newptr = 0;
            return NULL;
        }

        //if pointer is NULL, just call mm_malloc
        if (oldptr == NULL){
            return mm_malloc(size);
        }

     
        if(change == 0 && (oldSize - (size + DSIZE)) > (2*DSIZE) && (oldSize - asize) > (2*DSIZE))
        {//the minimum size of a free block is 16 because 8 bytes go for header and footer.payload has to be minimum non zero

            // the adjusted size still has enough space to make a free block
            place(ptr,asize);
        }

        size_t tempSize;
        size_t copySize;
        void *temp;

        // if no change required and we cannot split the block then just use the same block
        if(change == 0)
        {
            return ptr;
        }


        else {//if we need to change the block position

            int tempPrev = GET_SIZE(HDRP(PREV_BLKP(oldptr)));
            int tempNext = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));

            // next and prev are unallocated and will create a large enough block
            if (nextAlloc == 0 && prevAlloc == 0 && (tempPrev + tempNext + oldSize) >= (size + DSIZE))
            {
                newptr = PREV_BLKP(oldptr);
                temp = NEXT_BLKP(oldptr);
                tempSize = GET_SIZE(HDRP(newptr)) + GET_SIZE(HDRP(temp));

                //remove from free list since they will combine into 1
                remove_blck(PREV_BLKP(oldptr));
                remove_blck(NEXT_BLKP(oldptr));



                // if not big enough for new free block
                if((tempSize + oldSize) < (asize + 2*DSIZE)){
                    asize = tempSize + oldSize;
                }

                PUT(HDRP(newptr), PACK(asize, 1));
                copySize = GET_SIZE(HDRP(oldptr));
                memcpy(newptr, oldptr, copySize);
                PUT(FTRP(newptr), PACK(asize, 1));

                //new free block if sufficient place available
                if((tempSize + oldSize) >= (asize + 2*DSIZE)){
                    temp = NEXT_BLKP(newptr);
                    //set new header and footer for free block
                    PUT(HDRP(temp), PACK(tempSize + oldSize - asize, 0));
                    PUT(FTRP(temp), PACK(tempSize + oldSize - asize, 0));
                    add_blck(temp);
                }
                return newptr;
            }

            // prev is unallocated and will create a large enough block when combined
            else if(prevAlloc == 0 && ((tempPrev + oldSize) >= (size + DSIZE))){
                newptr = PREV_BLKP(oldptr);
                tempSize = GET_SIZE(FTRP(newptr));
                remove_blck(PREV_BLKP(oldptr));

                if((tempSize + oldSize) < (asize + 2*DSIZE)){
                    asize = tempSize + oldSize;
                }
                //set new header and footer
                PUT(HDRP(newptr), PACK(asize, 1));
                copySize = GET_SIZE(HDRP(oldptr));
                memcpy(newptr, oldptr, copySize);
                PUT(FTRP(newptr), PACK(asize, 1));

                //new free block
                if((tempSize + oldSize) >= (asize + 2*DSIZE))
                {

                    temp = NEXT_BLKP(newptr);
                    //set new header and footer for free block
                    PUT(HDRP(temp), PACK(tempSize + oldSize - asize, 0));
                    PUT(FTRP(temp), PACK(tempSize + oldSize - asize, 0));

                    add_blck(temp);
                }
                return newptr;
            }

            // next is unallocated and will create a large enough block
            else if(nextAlloc == 0 && (tempNext + oldSize) >= (size + DSIZE)){
                temp = NEXT_BLKP(oldptr);
                tempSize = GET_SIZE(FTRP(temp));
                remove_blck(NEXT_BLKP(ptr));

                if((tempSize + oldSize) < (asize + 2*DSIZE)){
                    asize = tempSize + oldSize;
                }
                //set header and footer
                PUT(HDRP(oldptr), PACK(asize, 1));
                PUT(FTRP(oldptr), PACK(asize, 1));

                //new free block
                if((tempSize + oldSize) >= (asize + 2*DSIZE)){
                    newptr = NEXT_BLKP(oldptr);
                    //set new header and footer for free block
                    PUT(HDRP(newptr), PACK(tempSize + oldSize - asize, 0));
                    PUT(FTRP(newptr), PACK(tempSize + oldSize - asize, 0));

                    add_blck(newptr);
                }
                return oldptr;
            }

            //prev and next are already allocated
            else{
                newptr = mm_malloc(size);
                copySize = GET_SIZE(HDRP(oldptr));
                if (size < copySize){
                    copySize = size;
                }

                memcpy(newptr, oldptr, copySize);
                mm_free(oldptr);
            }
            return newptr;
        }
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {                 
        add_blck(bp);
    }
    else if (!prev_alloc && next_alloc) {         
        remove_blck(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
        add_blck(bp);
    }
    else if (prev_alloc && !next_alloc) {        
        remove_blck(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
        add_blck(bp);
    }
    
    else{                                       
        remove_blck(PREV_BLKP(bp));
        remove_blck(NEXT_BLKP(bp));
       
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);

        add_blck(bp);
	}
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
    //if there are no free blocks available we need to extend the heap
    if(free_blcks == 0)
    {
    	    return NULL;
    }

    //search for a free block
    int local_list = asize / 128;

    //if local_list is less than the global_list we use global_list because the free block at the global_list has more size and its more optimum as we changed the globallist as soon as we had a new block.
    if(local_list < global_list)
    {
        local_list = global_list;
    }
    else if(local_list > 9)
    {
        local_list = 9;
    }

   //Loop through the remaining free lists starting at local_List
    for(; local_list < 10; local_list++)
    {
            
            
            char *bp = (char *)GET(heap_listp + (local_list * WSIZE));
	    int i = 0;
            for (;  i < 100 && (int)bp != 0 && GET_SIZE(HDRP(bp)) > 0; bp = (char *)GET(bp+WSIZE))
            {
                if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
                {
                   
                    return bp;
                }
                i++;
            }
    }

	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (2 * DSIZE)) {
        //first remove the block because its getting allocated
        remove_blck(bp);

		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));

		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));

        //now just add the new free block to the list
        add_blck(bp);
    }
    else
    {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
        //remove block
        remove_blck(bp);
    }
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
