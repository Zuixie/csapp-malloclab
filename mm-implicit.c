/*
 * mm-implicit.c
 * Simple allocator implement by implicit free list.
 * each block struct like this
 *  31      ...           3| 2  1  0
 *  --------------------------------
 * | 00 ... size (29 bits) | 0 0 a/f| header 
 * |       content ...              |
 * |       content ...              |
 * | 00 ... size (29 bits) | 0 0 a/f| footer
 *  --------------------------------
 * The header encodes the block size as well as 
 * whether the block is allocated or free. 
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x07)
#define GET_ALLOC(p) (GET(p) & 0x01)

#define HDPR(p) (((char *)(p)) - WSIZE)
#define FTPR(p) (((char *)(p)) + GET_SIZE(HDPR(p)) - DSIZE)
#define NEXT_BLPR(p) (FTPR(p) + DSIZE)
#define PRE_BLPR(p) (((char *)(p)) - GET_SIZE(HDPR(p) - WSIZE))

/* Global variables */
static char *heap_sptr;
static char *next_find_ptr;

/* Function prototypes for internal helper routines */
static void *find_first_fit(size_t size);
static void *find_next_fit(size_t size);
static void *find_best_fit(size_t size);
static void place(void *ptr, size_t size);
static void *coalesce(void *ptr);

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void)
{
    // allocate 4 * WORD 
    if ((heap_sptr = mem_sbrk(4 * WSIZE)) == (void *)-1) 
        return -1;
    
    // set data
    PUT(heap_sptr, 0x0);
    PUT(heap_sptr + WSIZE, PACK(8, 1));
    PUT(heap_sptr + 2 * WSIZE, PACK(8, 1));
    PUT(heap_sptr + 3 * WSIZE, PACK(0, 1));
    heap_sptr = heap_sptr + DSIZE;
    next_find_ptr = heap_sptr;

    dbg_printf("init heap_sptr:%p\n", heap_sptr);

    return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
    size_t newsize;
    char *ptr;

    if (size <= 0) 
        return NULL;
    newsize = ALIGN(size + DSIZE);

    // ptr = find_first_fit(newsize);
    ptr = find_best_fit(newsize);   
    // ptr = find_next_fit(newsize);
    
    if (ptr == NULL) 
    {
        // call mem_sbrk
        if ((ptr = mem_sbrk(newsize)) == (void *)-1) 
            return NULL;
        PUT(ptr + newsize - WSIZE, 1);
        PUT(HDPR(ptr), PACK(newsize, 0));
        PUT(FTPR(ptr), PACK(newsize, 0));
    }

    place(ptr, newsize);
    dbg_printf("malloc: %x, %p\n", (unsigned int)newsize, ptr);
    return ptr;
}

/*
 * free - free allocted block 
 *      free(NULL) has no effect
 */
void free(void *ptr)
{
    size_t size;
    
    if (ptr == NULL)
        return; 

    dbg_printf("free: %p, %p \n", HDPR(ptr), ptr);

    // // set next_find_ptr to previous block if free ponit == next_find_ptr 
    // if (ptr == next_find_ptr || (NEXT_BLPR(ptr) == next_find_ptr && !GET_ALLOC(HDPR(NEXT_BLPR(ptr))))) 
    // {
    //     next_find_ptr = PRE_BLPR(ptr);
    // }

    size = GET_SIZE(HDPR(ptr));   
    PUT(HDPR(ptr), PACK(size, 0));
    PUT(FTPR(ptr), PACK(size, 0));

    next_find_ptr = coalesce(ptr);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  
 */
void *realloc(void *oldptr, size_t size)
{
    dbg_printf("realloc: %p, %x\n", oldptr, (unsigned int)size);
    size_t oldsize, newsize;
    void *newptr, *temp;

    // If size == 0 then this is just free, and we return NULL.
    if(size == 0) 
    {
        free(oldptr);
        return 0;
    }

    // If oldptr is NULL, then this is just malloc.
    if(oldptr == NULL) 
    {
        return malloc(size);
    }

    oldsize = GET_SIZE(HDPR(oldptr));
    newsize = ALIGN(size + DSIZE);

    // oldsize == newsize, return oldptr
    if (oldsize == newsize) 
    {
        return oldptr;
    } 
    // newsize < oldsize, do not need to alloc new block 
    else if (newsize < oldsize)
    {
        if (oldsize - newsize < 16) 
            return oldptr;
        // oldsize - newsize > 16 -> need to split and coalesce
        PUT(HDPR(oldptr), PACK(newsize, 1));
        PUT(FTPR(oldptr), PACK(newsize, 1));
        
        temp = NEXT_BLPR(oldptr);
        PUT(HDPR(temp), PACK(oldsize - newsize, 0));
        PUT(FTPR(temp), PACK(oldsize - newsize, 0));
        
        next_find_ptr = coalesce(temp);

        return oldptr;
    } 
    // newsize > oldsize
    else
    {
        temp = NEXT_BLPR(oldptr);
        if ((!GET_ALLOC(HDPR(temp))) && (oldsize + GET_SIZE(HDPR(temp)) >= newsize)) 
        {
            // next block is free and space is enough
            place(temp, newsize - oldsize);
            PUT(HDPR(oldptr), PACK(oldsize + GET_SIZE(HDPR(temp)), 1));
            PUT(FTPR(oldptr), PACK(GET_SIZE(HDPR(oldptr)), 1));
            next_find_ptr = oldptr;
            return oldptr;
        }
    }

    newptr = malloc(size);

    // If realloc() fails the original block is left untouched
    if(!newptr) 
    {
        return 0;
    }

    // Copy the old data. 
    oldsize = GET_SIZE(HDPR(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    // Free the old block. 
    free(oldptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * mm_checkheap - Show detail of cureent heap and do some check.
 *      block point| size | alloc | user point
 */
void mm_checkheap(int verbose)
{
    // address: |size|0/1|
    // unsigned int freecount = 0; 
    // unsigned int freesizesum = 0;
    // unsigned int alloccount = 0;
    // unsigned int allocsizesum = 0;
    // unsigned int count_temp;
    unsigned int size_temp;
    unsigned int last_alloc = 1;

    char *ptr = heap_sptr;
    char *temp;

    printf("%d ====================================\n", verbose);
    while (GET(HDPR(ptr)) != 0x01)
    {
        temp = HDPR(ptr);
        size_temp = GET_SIZE(temp);
        printf("%p | %08x | %u | %p \n", temp, size_temp, GET_ALLOC(temp), ptr);
        
        // check val euqal between head and foot
        if (GET(HDPR(ptr)) != GET(FTPR(ptr))) 
        {
            printf("error!! head != foot \n");
            exit(1);
        }

        // whether the two linker block are not merged
        if (last_alloc == 0 && GET_ALLOC(temp) == last_alloc) 
        {
            printf("error ... ... coalescing fail\n");
            exit(1);
        }

        last_alloc = GET_ALLOC(temp);
        ptr = NEXT_BLPR(ptr);
    }

    temp = HDPR(ptr);
    printf("%p | %08x | %u | %p \n", temp, GET_SIZE(temp), GET_ALLOC(temp), ptr);
    printf("next start find: %p\n", next_find_ptr);
    // count:free: count/size; malloc:count/size; heap:
    printf("%d ====================================\n", verbose);

}

static void *find_first_fit(size_t size)
{
    char *ptr = heap_sptr;
    char *temp; 

    while (GET(HDPR(ptr)) != 0x01)
    {
        temp = HDPR(ptr);
        if (GET_ALLOC(temp) == 0x00 && size <= GET_SIZE(temp)) 
        {
            return ptr;
        }
        ptr = NEXT_BLPR(ptr);
    }

    return NULL;
}

static void *find_next_fit(size_t size)
{
    char *ptr = next_find_ptr;
    char *temp;

    do 
    {
        temp = HDPR(ptr);
        if (GET_ALLOC(temp) == 0 && size <= GET_SIZE(temp)) 
        {
            next_find_ptr = ptr;
            return ptr;
        }

        ptr = NEXT_BLPR(ptr);

        if (GET(HDPR(ptr)) == 0x01) 
            ptr = heap_sptr;

    } while (ptr != next_find_ptr);

    return NULL;
}

static void *find_best_fit(size_t size)
{
    char *ptr = heap_sptr;
    char *best_ptr = NULL;
    size_t size_gap = 0;
    char *temp;

    while (GET(HDPR(ptr)) != 0x01)
    {
        temp = HDPR(ptr);
        // find free && have enough space
        if (GET_ALLOC(temp) == 0x00 && size <= GET_SIZE(temp)) 
        {
            // first or the size of gap smaller than the last one
            if (GET_SIZE(temp) - size < size_gap || best_ptr == NULL) 
            {
                size_gap = GET_SIZE(temp) - size;
                best_ptr = ptr;
                if (size_gap == 0)
                    return best_ptr;
            }
        }

        ptr = NEXT_BLPR(ptr);
    }

    return best_ptr;
}

/*
 * place - Place the requested block at the beginning of the free block, 
 *      splitting only if the size of remainder would equal or exceed 
 *      the minimun block size.
 */
static void place(void *ptr, size_t size)
{
    size_t blocksize = GET_SIZE(HDPR(ptr));

    if ((blocksize - size) < 16)
    {
        PUT(HDPR(ptr), PACK(blocksize, 1));
        PUT(FTPR(ptr), PACK(blocksize, 1));
    }
    else 
    {
        // split
        PUT(HDPR(ptr), PACK(size, 1));
        PUT(FTPR(ptr), PACK(size, 1));
        
        ptr = NEXT_BLPR(ptr);
        PUT(HDPR(ptr), PACK(blocksize - size, 0));
        PUT(FTPR(ptr), PACK(blocksize - size, 0));
    }
}

/*
 * coalesce - merge adjacent free blocks
 *      Return a free block point after coalesce finish. 
 *      The next find fit need return the point. 
 */
static void *coalesce(void *ptr)
{
    void *pre = PRE_BLPR(ptr);  
    void *next = NEXT_BLPR(ptr);
    size_t size;
    // case 1 pre:alloc, next:alloc
    if (GET_ALLOC(HDPR(pre)) && GET_ALLOC(HDPR(next))) 
    {
        return ptr;
    }
    // case 2 pre:alloc, next:free
    else if (GET_ALLOC(HDPR(pre)) && (!GET_ALLOC(HDPR(next)))) 
    {
        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(next));
        PUT(HDPR(ptr), PACK(size, 0));
        PUT(FTPR(ptr), PACK(size, 0));

        return ptr;
    }
    // case 3 pre:free, next:alloc
    else if ((!GET_ALLOC(HDPR(pre))) && GET_ALLOC(HDPR(next))) 
    {
        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(pre));
        PUT(HDPR(pre), PACK(size, 0));
        PUT(FTPR(pre), PACK(size, 0));
        
        return pre;
    }
    // case 4 pre:free, next:free
    else
    {
        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(pre)) + GET_SIZE(HDPR(next));
        PUT(HDPR(pre), PACK(size, 0));
        PUT(FTPR(pre), PACK(size, 0)); 
        
        return pre;
    }   

}
