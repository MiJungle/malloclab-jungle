/*
This is a dynamic memory allocator(malloclab) implemented with an 
explicit free list to manage allocation and freeing of memory.

* Block structures:
* An explicit list uses the payload to embed pointers to the previous and next free blocks
* within a free block. The free and allocated block organizations are shown below:
*
* Allocated Block          Free Block
*  ---------               ---------
* | HEADER  |             | HEADER  |
*  ---------               ---------
* |         |             |  NEXT   |
* |         |              ---------
* | PAYLOAD |             |  PREV   |
* |         |              ---------
* |         |             |         |
*  ---------              |         |
* | FOOTER  |              ---------
*  ---------              | FOOTER  |
*                          ---------
* 
*/

#include <stdbool.h>
#include <stdint.h>
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
    "Team 6",
    /* First member's full name */
    "MiJung Lee",
    /* First member's email address */
    "mijunglee1215@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Basic constants and macros */

#define WSIZE 4 
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x)>(y)? (x):(y))

/* Combines a size and an allocate bit and returns a value that can be stored in a header or footer*/
#define PACK(size, alloc) ((size) | (alloc)) 

/* Read and write a word at address p */
// p가 (void*)pointer이기 때문에 casting 중요
#define GET(p) (*(unsigned int *)(p))  
#define PUT(p, val) (*(unsigned int *)(p)= (val))

/* Read the size and allocated fields from address */
#define GET_SIZE(p) (GET(p) & ~0x7) 
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLK(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLK(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

/* Given ptr in free list, get next and previous ptr in the list
bp is address of the free block. Since minimum Block size is 16 bytes,
we utilize to store the address of preivous block pointer and next block pointer*/
#define GET_NEXT_PTR(bp) (*(char **)(bp))
#define GET_PREV_PTR(bp) (*(char **)(bp + WSIZE))

/* Puts pointers in the next and pervious elements of free list */
#define SET_NEXT_PTR(bp,qp) (GET_NEXT_PTR(bp) = (qp))
#define SET_PREV_PTR(bp,qp) (GET_PREV_PTR(bp)= (qp))

/* Global Variables */
static char *heap_listp = 0;
static char *free_list_start = 0;

/* Function prototypes for internal helper routines */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for maintaining free list*/
static void insert_in_free_list(void *bp);
static void remove_from_free_list(void *bp);

/* Function prototypes for heap consistency checker routines;*/
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);

int mm_init(void)
{

    if ((heap_listp = mem_sbrk(8 * WSIZE)) == NULL)
        return -1;
    PUT(heap_listp,0);                                  /* Alignment Padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      /* Prologue Header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      /* Prologue Footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          /* Epilogue Header */
    free_list_start = heap_listp + 2 * WSIZE;

/*     Extend the empty heap with a free block of minimum possible block size*/    
    if (extend_heap(4) == NULL)
    {
            return -1;
    }
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

/*     Allocate an even number of words to maintain alignment */     
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

/* since minimum block size given to us is 4 words(ie 16 bytes) */
   if (size < 16)
    {
        size = 16;
    }
/* call for more memory space */
    if ((int)(bp = mem_sbrk(size)) == -1 )
    {
        return NULL;
    }
/*     Initialize free block header/footer and the epilogue header*/        
    PUT(HDRP(bp), PACK(size, 0));           /* free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* free block footer */
    PUT(HDRP(NEXT_BLK(bp)), PACK(0,1));     /* new epilogue header */
    /* coalesce bp with next and previous blocks */
    return coalesce(bp);
}

static void *coalesce(void *bp) 
{
        //if previous block is allocated or its size is zero then PREV_ALLOC will be set
        size_t NEXT_ALLOC = GET_ALLOC(HDRP(NEXT_BLK(bp)));
        size_t PREV_ALLOC = GET_ALLOC(FTRP(PREV_BLK(bp))) || PREV_BLK(bp) == bp;

        size_t size = GET_SIZE(HDRP(bp));

        /* Next block is only free */
        if (PREV_ALLOC && !NEXT_ALLOC)
        {
            size += GET_SIZE( HDRP(NEXT_BLK(bp)));
            remove_from_free_list(NEXT_BLK(bp));
            PUT(HDRP(bp), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
        }
        /* Prev block is only free */
        else if (!PREV_ALLOC && NEXT_ALLOC) 
        {
            size += GET_SIZE(HDRP(PREV_BLK(bp)));
            bp = PREV_BLK(bp);
            remove_from_free_list(bp);
            PUT(HDRP(bp), PACK(size,0));
            PUT(FTRP(bp), PACK(size,0));

        }
        /* Both blocks are free */
        else if (!PREV_ALLOC && !NEXT_ALLOC) 
        {
            size += GET_SIZE(HDRP(PREV_BLK(bp))) + GET_SIZE(HDRP(NEXT_BLK(bp)));
            remove_from_free_list(PREV_BLK(bp));
            remove_from_free_list(NEXT_BLK(bp));
            bp = PREV_BLK(bp);
            PUT(HDRP(bp), PACK(size,0));
            PUT(FTRP(bp), PACK(size,0));    
        } /* lastly insert bp into free list and return bp */
        insert_in_free_list(bp);
        return bp;
}
void  *mm_malloc(size_t size)
{
    size_t asize;           /* Adjusted block size */
    size_t extendsize;      /* Amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return (NULL);

    /* Adjust block size to include overhead and alignment reqs */    
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else    
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    
    /*Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return (bp);
    }

   /*  No fit found. Get more memory and place the block */ 
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize /WSIZE)) == NULL)
        return (NULL);
    place(bp, asize);
    return (bp);
}

void *mm_realloc(void *bp, size_t size)
{
    if((int)size < 0)
        return NULL;
    else if((int)size == 0)
    {
        mm_free(bp);
        return NULL;
    }
    else if(size > 0)
    {
        size_t oldsize = GET_SIZE(HDRP(bp));
        size_t newsize = size + (2 * WSIZE); /* 2words for header and footer */
        /* if newsize is less than oldsize then we just return bp */

        if(newsize <= oldsize)
        {
            return bp;
        }
        /* if newsize is greater than oldsize */
        else 
        {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLK(bp)));
            size_t csize;
            /* next block is free and the size of the two blocks is greater than or equal the new size */
            /* then we only need to combine both the blocks */
            if(!next_alloc && ((csize = oldsize + GET_SIZE(HDRP(NEXT_BLK(bp)) ))) >= newsize)
            {
                remove_from_free_list(NEXT_BLK(bp));
                PUT(HDRP(bp), PACK(csize, 1));
                PUT(FTRP(bp), PACK(csize, 1));
                return bp;
            }        
            else {
                void *new_ptr = mm_malloc(newsize);
                place(new_ptr, newsize);
                memcpy(new_ptr,bp, newsize);
                mm_free(bp);
                return new_ptr;
            }
        }
    }
    else
        return NULL;
}

static void *find_fit(size_t asize)
{
    void *bp;
    static int last_malloced_size = 0;
    static int repeat_counter = 0;
    if( last_malloced_size == (int)asize)
    {
        if(repeat_counter>30)
        {
            int extendsize = MAX(asize, 4 * WSIZE);
            bp = extend_heap(extendsize/4);
            return bp;
        }
        else
            repeat_counter++;
    }
    else 
        repeat_counter = 0;
    for (bp = free_list_start; GET_ALLOC(HDRP(bp)) == 0; bp = GET_NEXT_PTR(bp)) 
    {
        if (asize <= (size_t)GET_SIZE(HDRP(bp)))
        {
            last_malloced_size = asize;
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
        size_t csize = GET_SIZE(HDRP(bp));

        if ((csize - asize) >= 4 * WSIZE)
        {
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            remove_from_free_list(bp);
            bp = NEXT_BLK(bp);
            PUT(HDRP(bp), PACK(csize - asize, 0));
            PUT(FTRP(bp), PACK(csize - asize, 0));
            coalesce(bp);
        }
        else
        {
            PUT(HDRP(bp), PACK(csize, 1));
            PUT(FTRP(bp), PACK(csize, 1));
            remove_from_free_list(bp);
        }
}
static void insert_in_free_list(void *bp)
{
    SET_NEXT_PTR(bp, free_list_start);
    SET_PREV_PTR(free_list_start, bp);
    SET_PREV_PTR(bp, NULL);
    free_list_start = bp;

}

static void remove_from_free_list(void *bp)
{
        if(GET_PREV_PTR(bp)) 
                SET_NEXT_PTR(GET_PREV_PTR(bp), GET_NEXT_PTR(bp));
        else    
                free_list_start =GET_NEXT_PTR(bp);
        SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));
}

void mm_free(void *bp)
{
    size_t size;
    if (bp == NULL)
            return;
    /* Free and coalesce the block */
    size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void checkblock(void *bp)
{
    if((uintptr_t)bp % DSIZE)
            printf("Error: %p is not doubleword aligned\n", bp);
    if(GET(HDRP(bp)) != GET(FTRP(bp)))
            printf("Error: header does not match footer\n");
}

void checkheap(bool verbose)
{
    void *bp;
    if (verbose)
            printf("HEAP (%p): \n", heap_listp);
    if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
            !GET_ALLOC(HDRP(heap_listp)))
            printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = (void *)NEXT_BLK(bp))
    {
        if (verbose)
                printblock(bp);
        checkblock(bp);
    }
    if (verbose)
            printblock(bp);
    if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
            printf("Bad epilogue header\n");
}

static void printblock(void *bp)
{
        bool halloc, falloc;
        size_t hsize, fsize;

        checkheap(false);
        hsize = GET_SIZE(HDRP(bp));
        halloc = GET_ALLOC(HDRP(bp));
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp));

        if (hsize = 0)
        {
            printf("%p: end of heap\n", bp);
            return ;
        }
        printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
                hsize, (halloc ? 'a': 'f'),
                fsize, (falloc ? 'a':'f'));
}