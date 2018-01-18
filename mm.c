/*
 * mm.c
 * Allocator implement by segregated free list.
 * each allocated block struct like this
 *  31      ...           3| 2  1  0
 *  --------------------------------
 * | 00 ... size (29 bits) | 0 0 a/f| header 
 * |       content ...              |
 * |       content ...              |
 * | 00 ... size (29 bits) | 0 0 a/f| footer
 *  --------------------------------
 * The header encodes the block size as well as 
 * whether the block is allocated or free.
 *
 *
 * each free block struct like this
 *  31      ...           3| 2  1  0
 *  ----------------------------------
 * | 00 ... size (29 bits) | 0 b/r a/f| header 
 * |      left child                  | 
 * |      right child                 | 
 * |      parents node                |
 * |      padding                     |
 * | 00 ... size (29 bits) | 0 b/r a/f| footer
 *  ----------------------------------
 * The both of left child and right child used 4 bytes.
 * The 4bytes store the distance from address of heap start.
 * All free blocks organized by doubly linked list.
 * This reduces the first-fit allocation time.  
 *
 * Maintain the list in last-in first-out (LIFO),
 * inserting newly freed blocks at the beginning of the list. 
 * 
 * The first 4 bytes of the heap are the 
 * prologue block of the linked list.
 * This block store the successor value.
 * The reason for this desgin is to optimize
 * the addition and remove of block. 
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

#define BLACK 1
#define RED 0

#define SEG_MAX 10
#define MIN_BLOCK_SIZE 24
#define CHUNKSIZE  (1<<8)

#define MAX(a, b) ((a) > (b) ? (a) : (b))

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

#define GET_LEFT_PTR(p) ((char *)(p))
#define GET_RIGHT_PTR(p) ((char *)(p) + WSIZE)
#define GET_PARENT_PTR(p) ((char *)(p) + DSIZE)

#define GET_LEFT_VAL(p) GET(GET_LEFT_PTR(p))
#define GET_RIGHT_VAL(p) GET(GET_RIGHT_PTR(p))
#define GET_PARENT_VAL(p) GET(GET_PARENT_PTR(p))
#define SET_LEFT_VAL(p, val) PUT(GET_LEFT_PTR(p), val)
#define SET_RIGHT_VAL(p, val) PUT(GET_RIGHT_PTR(p), val)
#define SET_PARENT_VAL(p, val) PUT(GET_PARENT_PTR(p), val)

#define GET_POINTER(val) (heap_start_addr + (val)) // TEST

#define SET_BLACK(p) PUT(p, (GET(p) | 0x02))
#define SET_RED(p) PUT(p, (GET(p) & ~0x02))
#define GET_COLOR(p) (GET(p) & 0x02)

/* Global variables */
static char *heap_listp;
static char *next_find_ptr;
static char *heap_start_addr;
static char *free_listp;

/* Function prototypes for internal helper routines */
static unsigned int get_seg_index(size_t size);
static void freelist_remove(void *ptr);
static void remove_to_tree(void *ptr, void *root);
static void freelist_add(void *ptr);
static void insert_to_tree(void *root, void *newnode, size_t size);
static void *find_first_fit(size_t size);
static void place(void *ptr, size_t size);
static void *coalesce(void *ptr);
static unsigned int check_seg_list(int verbose);
static unsigned int check_whole_heap(int verbose);
static unsigned int check_tree(void *root, unsigned int index);

/*
 * mm_init - Called when a new trace starts.
 * heap_start_addr              heap_listp
 * |                                 |
 * |   seg array  (SEG_MAX * 4)   | 4 | 4 | 4 | 4 |
 * | 
 * free_listp
 */
int mm_init(void)
{
    // allocate init block -> | arrary size: 4 * SEG_MAX | 16bytes |  
    if ((heap_listp = mem_sbrk(4 * WSIZE + SEG_MAX * WSIZE))
        == (void *)-1) 
        return -1;
    
    heap_start_addr = heap_listp;
    free_listp = heap_listp;

    for (unsigned int i = 0; i < SEG_MAX; i++) 
    {
        PUT(heap_listp + i * WSIZE, 0);
    }

    heap_listp += (SEG_MAX * WSIZE);
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(8, 1));
    PUT(heap_listp + 2 * WSIZE, PACK(8, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));
    heap_listp = heap_listp + DSIZE;
    // next_find_ptr = heap_listp;

    dbg_printf("init heap_listp:%p\n", heap_listp);
    dbg_printf("init heap_start_addr:%p\n", heap_start_addr);

    return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
    size_t newsize;
    size_t sbrk_size;
    char *ptr;

    if (size <= 0) 
        return NULL;
    newsize = ALIGN(size + DSIZE);
    newsize = MAX(newsize, MIN_BLOCK_SIZE);

    ptr = find_first_fit(newsize);
    
    if (ptr == NULL) 
    {
        sbrk_size = ALIGN(MAX(newsize, CHUNKSIZE));
        if ((ptr = mem_sbrk(sbrk_size)) == (void *)-1) 
            return NULL;
        PUT(ptr + sbrk_size - WSIZE, 1);
        PUT(HDPR(ptr), PACK(sbrk_size, 0));
        PUT(FTPR(ptr), PACK(sbrk_size, 0));
        dbg_printf("sbrk: %x \n", (unsigned int)sbrk_size);
        freelist_add(ptr);
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
    
    if (!ptr)
        return; 

    dbg_printf("free: %p, %p \n", HDPR(ptr), ptr);

    size = GET_SIZE(HDPR(ptr));   
    PUT(HDPR(ptr), PACK(size, 0));
    PUT(FTPR(ptr), PACK(size, 0));

    // freelist_add(ptr);

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
    newsize = MAX(newsize, MIN_BLOCK_SIZE);

    // oldsize == newsize, return oldptr
    if (oldsize == newsize) 
    {
        return oldptr;
    } 
    // newsize < oldsize, do not need to alloc new block 
    else if (newsize < oldsize)
    {
        if (oldsize - newsize < MIN_BLOCK_SIZE) 
            return oldptr;
        // oldsize - newsize > 16 -> need to split and coalesce
        PUT(HDPR(oldptr), PACK(newsize, 1));
        PUT(FTPR(oldptr), PACK(newsize, 1));
        
        temp = NEXT_BLPR(oldptr);
        PUT(HDPR(temp), PACK(oldsize - newsize, 0));
        PUT(FTPR(temp), PACK(oldsize - newsize, 0));

        // freelist_add(temp);
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
void *calloc(size_t nmemb, size_t size)
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
    unsigned int freecount_heap = 0; 
    unsigned int freecount_list = 0; 
   
    dbg_printf("%d ====================================\n", verbose);

    // check whole heap
    freecount_heap = check_whole_heap(verbose);
    
    // check free list
    freecount_list = check_seg_list(verbose);

    dbg_printf("free list count: %d, heap free list count: %d\n", freecount_list, freecount_heap);
    
    // check free block num in heap equal with in free list  
    if (freecount_heap != freecount_list) 
    {
        printf("error ! free block num errr \n");
        exit(1);
    }

    dbg_printf("%d ====================================\n", verbose);

}

static inline unsigned int get_seg_index(size_t size)
{
    unsigned int index = 0;
    size = size >> 3;
    while (size >> index) index++; 
    return index > SEG_MAX ? SEG_MAX - 1 : index - 1;
}

/* remove request block from free list */
static inline void freelist_remove(void *ptr)
{
    unsigned int index = get_seg_index(GET_SIZE(HDPR(ptr)));
    char *root = free_listp + WSIZE * index;
    
    dbg_printf("remove: root: %p, ptr:%p\n", root, ptr);

    remove_to_tree(ptr, root);
}

static void remove_to_tree(void *ptr, void *root)
{
    unsigned int left_val = GET_LEFT_VAL(ptr);
    unsigned int right_val = GET_RIGHT_VAL(ptr);
    unsigned int parent_val = GET_PARENT_VAL(ptr);
    char *parent = GET_POINTER(parent_val);

    if (!left_val && !right_val) 
    {
        if (parent_val) 
        {
            if (GET_POINTER(GET_LEFT_VAL(parent)) == ptr) 
            {
                SET_LEFT_VAL(parent, 0);
            }
            else 
            {
                SET_RIGHT_VAL(parent, 0);
            }
        }
        else // root 
        {
            PUT(root, 0);
        }
    }
    // right is null
    else if (left_val && !right_val)
    {
        if (parent_val) 
        {            
            if (GET_POINTER(GET_LEFT_VAL(parent)) == ptr) 
            {
                SET_LEFT_VAL(parent, left_val);
            }
            else 
            {
                SET_RIGHT_VAL(parent, left_val);
            }
            SET_PARENT_VAL(GET_POINTER(left_val), parent_val);
        } 
        else 
        {
            PUT(root, left_val);
            SET_PARENT_VAL(GET_POINTER(left_val), 0);
        }
    }
    // left is null
    else if (!left_val && right_val) 
    {
        if (parent_val) 
        {            
            if (GET_POINTER(GET_LEFT_VAL(parent)) == ptr) 
            {
                SET_LEFT_VAL(parent, right_val);
            }
            else 
            {
                SET_RIGHT_VAL(parent, right_val);
            }
            SET_PARENT_VAL(GET_POINTER(right_val), parent_val);
        } 
        else 
        {
            PUT(root, right_val);
            SET_PARENT_VAL(GET_POINTER(right_val), 0);
        }
    }
    // both left and right are not null
    else 
    {
        // replace the node with right node
        if (parent_val) 
        {            
            if (GET_POINTER(GET_LEFT_VAL(parent)) == ptr) 
            {
                SET_LEFT_VAL(parent, right_val);
            }
            else 
            {
                SET_RIGHT_VAL(parent, right_val);
            }
            SET_PARENT_VAL(GET_POINTER(right_val), parent_val);
        } 
        else 
        {
            PUT(root, right_val);
            SET_PARENT_VAL(GET_POINTER(right_val), 0);
        }

        // find the the leftmost node && set left node
        parent = GET_POINTER(right_val);
         
        while (GET_LEFT_VAL(parent))
        {
            parent = GET_POINTER(GET_LEFT_VAL(parent));
        }
        // set left node
        SET_LEFT_VAL(parent, left_val);
        SET_PARENT_VAL(GET_POINTER(left_val), parent - heap_start_addr);
    }

}

static inline void freelist_add(void *ptr)
{   
    size_t size = GET_SIZE(HDPR(ptr));
    unsigned int index = get_seg_index(size);
    char *start = free_listp + WSIZE * index;
    char *root = heap_start_addr + GET(start);

    // set new node self
    SET_PARENT_VAL(ptr, 0);
    SET_LEFT_VAL(ptr, 0);
    SET_RIGHT_VAL(ptr, 0);

    dbg_printf("insert r:%p, p:%p, s:%x\n", root, ptr, 
               (unsigned int)size);

    // if root is empty
    if (root == heap_start_addr)
    {
        PUT(start, (char *)ptr - heap_start_addr);
        return;
    }

    insert_to_tree(root, ptr, size);
    // dbg_printf("insert success %d\n", check_seg_list(5));
}

/* Insert a given newnode to the tree */
static void insert_to_tree(void *root, void *newnode, size_t size) 
{
    // root
    if (root == heap_start_addr) 
    {
        PUT(root, (char *)newnode - heap_start_addr);
        return;
    }

    unsigned int rval = GET_RIGHT_VAL(root);
    unsigned int lval = GET_LEFT_VAL(root);

    // insert to right
    if (size > GET_SIZE(HDPR(root))) 
    {
        if (rval) 
        {
            // right is not null
            insert_to_tree(heap_start_addr + rval, newnode, size);
        } 
        else 
        {
            SET_RIGHT_VAL(root, (char *)newnode - heap_start_addr);
            SET_PARENT_VAL(newnode, (char *)root - heap_start_addr);
        }
    }
    // insert to left
    else 
    {
        if (lval) 
        {
            insert_to_tree(heap_start_addr + lval, newnode, size);
        }
        else 
        {           
            SET_LEFT_VAL(root, (char *)newnode - heap_start_addr);
            SET_PARENT_VAL(newnode, (char *)root - heap_start_addr);
        }
    }
}

static void *find_first_fit(size_t size)
{
    unsigned int index = 0;
    char *ptr;
    char *free_list_start;

    // compute the index of seg array by given size
    index = get_seg_index(size);
    
    for (; index < SEG_MAX; index++) 
    {
        free_list_start = index * WSIZE + free_listp;
        ptr = GET_POINTER(GET(free_list_start));

        while (ptr != heap_start_addr)
        {        
            if (size <= GET_SIZE(HDPR(ptr))) 
            {
                return ptr;
            }
            // ptr = heap_start_addr + GET_SUCC_VAL(ptr);
            ptr = GET_POINTER(GET_RIGHT_VAL(ptr));
        }
    }

    return NULL;
}

/*
 * place - Place the requested block at the beginning of the free block, 
 *      splitting only if the size of remainder would equal or exceed 
 *      the minimun block size.
 */
static void place(void *ptr, size_t size)
{
    dbg_printf("start place ... ... %p, %x\n", ptr, (int)size);
    size_t blocksize = GET_SIZE(HDPR(ptr));

    if ((blocksize - size) < MIN_BLOCK_SIZE)
    {
        freelist_remove(ptr);

        PUT(HDPR(ptr), PACK(blocksize, 1));
        PUT(FTPR(ptr), PACK(blocksize, 1));
    }
    else 
    {
        // split
        freelist_remove(ptr);

        PUT(HDPR(ptr), PACK(size, 1));
        PUT(FTPR(ptr), PACK(size, 1));

        ptr = NEXT_BLPR(ptr);
        PUT(HDPR(ptr), PACK(blocksize - size, 0));
        PUT(FTPR(ptr), PACK(blocksize - size, 0));
        freelist_add(ptr);
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
        freelist_add(ptr);
        return ptr;
    }
    // case 2 pre:alloc, next:free
    else if (GET_ALLOC(HDPR(pre)) && (!GET_ALLOC(HDPR(next)))) 
    {
        freelist_remove(next);

        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(next));
        PUT(HDPR(ptr), PACK(size, 0));
        PUT(FTPR(ptr), PACK(size, 0));

        freelist_add(ptr);
        return ptr;
    }
    // case 3 pre:free, next:alloc
    else if ((!GET_ALLOC(HDPR(pre))) && GET_ALLOC(HDPR(next))) 
    {
        freelist_remove(pre);
        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(pre));
        PUT(HDPR(pre), PACK(size, 0));
        PUT(FTPR(pre), PACK(size, 0));
        freelist_add(pre);
        return pre;
    }
    // case 4 pre:free, next:free
    else
    {
        freelist_remove(pre);
        freelist_remove(next);

        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(pre)) + GET_SIZE(HDPR(next));
        PUT(HDPR(pre), PACK(size, 0));
        PUT(FTPR(pre), PACK(size, 0)); 

        freelist_add(pre);
        return pre;
    }   
}

/* Check free block by seg array. Return the count of free blocks */
static unsigned int check_seg_list(int verbose) 
{
    unsigned int index;
    char *ptr;
    char *free_list_start;
    unsigned int count = 0;
    unsigned count_temp;

    for (index = 0; index < SEG_MAX; index++) 
    {
        count_temp = 0;
        free_list_start = index * WSIZE + free_listp;
        ptr = GET_POINTER(GET(free_list_start));
        if (verbose > 2) 
        {
            dbg_printf("start: %p; root: %p - ", free_list_start, ptr);
        }

        count_temp = check_tree(ptr, index);
        count += count_temp;

        if (verbose > 2)
        {
            dbg_printf("%u:%u\n", index, count_temp);
        }
    }

    return count;
}

// TODO add the size of entire heap 
static unsigned int check_whole_heap(int verbose) 
{
    if (verbose < 0)
        return 0;
    unsigned int size_temp;
    char *temp;
    unsigned int freecount_heap = 0;
    char *ptr = heap_listp;
    int last_free = 0;

    while (GET(HDPR(ptr)) != 0x01)
    {
        temp = HDPR(ptr);
        size_temp = GET_SIZE(temp);

        if (GET_ALLOC(temp))
        {
            dbg_printf("%p | %08x | %u | %p \n", 
                   temp, size_temp, GET_ALLOC(temp), ptr);
            last_free = 0;
        }
        else
        {
            dbg_printf("%p | %08x | %u | %p | %p | %p | %p\n", temp, 
                       size_temp, GET_ALLOC(temp), ptr,
                       GET_POINTER(GET_LEFT_VAL(ptr)),
                       GET_POINTER(GET_RIGHT_VAL(ptr)),
                       GET_POINTER(GET_PARENT_VAL(ptr)));
            freecount_heap++;
            if (last_free) 
            {
                printf("%x error not coalesc!!! %p\n", size_temp, ptr);
                exit(1);
            }
            last_free = 1;
        }

        if (GET(HDPR(ptr)) != GET(FTPR(ptr))) 
        {
            printf("error!! head != foot %p\n", ptr);
            exit(1);
        }

        ptr = NEXT_BLPR(ptr);
    }

    // epilogue
    temp = HDPR(ptr);
    dbg_printf("%p | %08x | %u | %p \n", temp, GET_SIZE(temp), GET_ALLOC(temp), ptr);

    dbg_printf("free listp: %p\n", free_listp);

    return freecount_heap;
}

/* check binary search tree , reutrn this number of total free block*/
static unsigned int check_tree(void *root, unsigned int index) 
{
    unsigned int left_val;
    unsigned int left_size;
    unsigned int right_val;
    unsigned int right_size;
    unsigned int root_size;
    unsigned int count_right;
    unsigned int count_left;

    if (root == heap_start_addr) 
    {
        return 0;
    }
    
    left_val = GET_LEFT_VAL(root);
    right_val = GET_RIGHT_VAL(root);
    root_size = GET_SIZE(HDPR(root));
    
    // check size 
    left_size = left_val ? GET_SIZE(HDPR(GET_POINTER(left_val))) : root_size - 1;
    right_size = right_val ? GET_SIZE(HDPR(GET_POINTER(right_val))) : root_size + 1; 

    if (!(left_size <= root_size && right_size > root_size)) 
    {
        printf("error! tree: %p\n", root);
        printf("root:%x, left:%x, right:%x\n", root_size, left_size, right_size);
        exit(1);
    }
    
    // check index 
    if (index != get_seg_index(root_size)) 
    {   
        printf("error! tree: %p, %d\n", root, index);
        printf("size:%x, %d.  The size does not belong to this group.\n",
                root_size, get_seg_index(root_size));
    }

    count_right = check_tree(GET_POINTER(right_val), index);
    count_left = check_tree(GET_POINTER(left_val), index);
    return count_right + count_left + 1;
}