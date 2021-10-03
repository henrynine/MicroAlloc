/*
 * this memory allocator uses first in last out segregated free lists.
 * when blocks are freed, they are not immediately returned to the main 
 * lists - they're put on an unsorted list which is searched before the
 * main lists when finding a free block, and if they are searched on this
 * list but not allocated, then they're returned to the main lists.
 * all pointers returned are guaranteed to be aligned to twice the
 * width of size_t - on most systems, this is 8 bytes
 */
#include <stdio.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>
#include <limits.h>

/*
 * free blocks are structured in memory as a one word header followed by
 * a next pointer, then a previous pointer. the location of the footer
 * varies based on the size of the block.
 * prologue and epilogue blocks only use the header.
 */
typedef struct block {
    size_t size;
    struct block *next;
    struct block *prev;
} Block;

// type for headers and footers
#define BTAG_T           size_t

// constant definitions
// size of single word
#define WSIZE            (sizeof(BTAG_T))
// size of double word
#define DSIZE            (2 * WSIZE)
// single or double word alignment
#define ALIGNMENT        (DSIZE)
// minimum regular block size - header, footer, 2 pointers
#define MINBLOCK         (sizeof(Block) + WSIZE)
// maximum small list size in bytes
#define MAXSMALL         504
// number of free lists
#define LISTCOUNT        75

// helper macros
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size)      (((size) + (ALIGNMENT-1)) & ~0x7)
// checks if a pointer is aligned
#define IS_ALIGNED(p)    (ALIGN((uintptr_t) p ) == (uintptr_t) p)
    // (((uintptr_t)(p)) % (ALIGNMENT) == 0)

/* user pointers point to the start of the user-accessible memory, which
 * begins after the header. for internal manipulation the allocator uses
 * pointers to headers. */
// convert user pointer to block pointer
#define USERTOBLOCK(u)    ((Block *)(((void *) u) - WSIZE))
// convert block pointer to user pointer
#define BLOCKTOUSER(b)    ((Block *)(((void *) b) + WSIZE))

// get size of block
#define SIZE(b)           ((b)->size & ~0x7) 
// get the amount of a block that's allocated to the user
#define USERSIZE(b)       (SIZE(b) - DSIZE)
// get the block size required to hold u bytes of user memory
#define BLOCKSIZE(u)      (u + DSIZE)

// 1 if block is allocated
#define ISALLOC(b)        ((b)->size & 0x1) 
// 1 if block is on a quick list
#define ISQUICK(b)        ((b)->size & 0x2) 

// mark block as free for coalescing - also marks block as unallocated
#define MARKQUICK(b)      ((b)->size |= 0x2)
// mark block as not free for coalescing
#define MARKUNQUICK(b)    ((b)->size &= ~0x2)

// mark block as allocated and not on a quick list
#define MARKALLOC(b)      ((b)->size = ((b)->size & ~0x2) | 0x1)
// mark block as free
#define MARKFREE(b)       ((b)->size &= ~0x1)

// set a block as allocated with size 0 - used for prologue/epilogue
#define BOUNDINIT(b)      ({MARKALLOC(b); SETSIZEHDR(b, 0);})

// set the size of a block in its header without changing its flags
#define SETSIZEHDR(b, s)  ((b)->size = ((b)->size & 0x7) | (s))
/* get the footer of a block - used as a helper for HDRTOFTR and for 
 * consistency checking */
#define GETFTR(b)         ((Block *)(((void *)(b)) + SIZE(b) - WSIZE))
// copy the header of a block to its footer
#define HDRTOFTR(b)       (GETFTR(b)->size = (b)->size)
/* set the size of a block without changing its flags - make sure to set
 * flags before calling this so the flags are also copied to the footer.
 * not valid for prologue or epilogue blocks
 */
#define SETSIZE(b, s)     {SETSIZEHDR(b, s); HDRTOFTR(b);}

/* the following macros should only be used for coalescing purposes -
 * they don't consider neighbors in a free list, but neighbors in the
 * raw address space. */
// get the footer of the block before b - for prologues, gets the header
#define PREVFTR(b)        (((Block *)((void *)(b) - WSIZE)))
// get the previous block in the raw address space using its footer
#define PREVRAW(b)        ((Block *)((void *)(b) - SIZE(PREVFTR(b))))
/* check the footer of the previous block for lack of allocated and quick
 * flags */
#define PREVUNCOAL(b)     (PREVFTR(b)->size & 0x3)
// get the next block in the raw address space
#define NEXTRAW(b)        ((Block *)(((void *)(b)) + SIZE(b)))
// get the coalescability of the next block in raw address space
#define NEXTUNCOAL(b)     (NEXTRAW(b)->size & 0x3)

// internal functions
static Block  *extend_heap(size_t);
static void   split(Block *, size_t);
static int    find_list_index(size_t);
static Block  *find_in_list(Block *, size_t);
static Block  *find_block(size_t);
static void   free_list_insert(Block *, bool);
static void   free_list_remove(Block *);
static Block  *coalesce(Block *);

/* these blocks track the beginning and end of the region of memory
 * being managed. */
static Block *prologue; 
static Block *epilogue;

/* the first free list is the unsorted list. after that, blocks increase
 * in size two words at a time, from the minimum size up to 504 bytes.
 * blocks of size 512 bytes and up are spllit by powers of 2, with all
 * blocks over 512 kilobytes sharing a list. */
static Block **free_lists;

/* malloc_init - initialize the allocator. creates the prologue with
 * correct alignment and gets room for the free lists. */
static int malloc_init(void)
{
    static int init;
    size_t pad_bytes, req_bytes;
    void *old_brk;

    if (init > 0) return 0;

    // get room for free_lists and initialize all to NULL
    if ((free_lists = (Block **) sbrk(sizeof(Block *) * LISTCOUNT)) == \
        (void *) -1) {
        fprintf(stderr, "malloc_init: couldn't acquire memory for "
                        "free_lists\n");
        errno = ENOMEM;
        return -1;
    }
    memset(free_lists, 0, sizeof(Block *) * LISTCOUNT);

    // check if padding bytes are needed
    if ((old_brk = sbrk(0)) == (void *)(-1)) {
        fprintf(stderr, "malloc_init: couldn't check current brk\n");
        errno = ENOMEM;
        return -1;
    }

    pad_bytes = ALIGN((uintptr_t)old_brk) - (uintptr_t) old_brk;
    /* request enough bytes for padding + prologue + epilogue. aligning 
     * here ensures that the end of the new chunk is DWORD aligned. */
    req_bytes = ALIGN(pad_bytes + WSIZE + sizeof(Block));
    if (sbrk(req_bytes) == (void *) -1) {
        fprintf(stderr, "mm_init: not enough memory\n");
        errno = ENOMEM;
        return -1;
    }
    
    // initialize chunk - new prologue starts at old_brk + pad_bytes
    prologue = (Block *) (old_brk + pad_bytes);
    // epilogue starts after after prologue
    epilogue = (Block *) ((void *) prologue + WSIZE);

    // initialize prologue and epilogue
    BOUNDINIT(prologue);
    BOUNDINIT(epilogue);
    init = 1;
    return 0;
}

/* allocate a block by finding a free block of sufficient
 * size and increasing the program break if none is found.
 * always allocates a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
    Block *found_block, *last_in_heap;

    if (malloc_init() < 0) {
        return NULL;
    }

    if (size == 0) {
        return NULL;
    }

    // align the request size to preserve block alignment
    if (size > ALIGN(BLOCKSIZE(size))) {
        fprintf(stderr, "malloc: request too large\n");
        errno = ENOMEM;
        return NULL;
    }
    size = ALIGN(BLOCKSIZE(size));

    // search for a block
    found_block = find_block(size);
    if (found_block == NULL) {
        // expand the heap to create room for the request
        last_in_heap = PREVRAW(epilogue);
        if (!ISALLOC(last_in_heap)) {
            /* can extend the last block in the heap instead of creating
             * an entirely new one */
            found_block = last_in_heap;
            if (extend_heap(size - SIZE(found_block)) == NULL) {
                // pass error up the stack
                return NULL;
            }
            free_list_remove(found_block);
            SETSIZE(found_block, size);
        } else {
            // extend the heap enough to make a whole new block
            if ((found_block = extend_heap(size)) == NULL) {
                // pass error up the stack
                return NULL;
            }
        }
    }

    if (!ISALLOC(found_block)) {
        /* block was obtained from a free list, not just by extending the 
         * heap - remove it from that list */
        free_list_remove(found_block);
    }

    // if the new block doesn't need all the space found, don't take it all
    split(found_block, size);
   
    return BLOCKTOUSER(found_block);
}

/*
 * free - release a block allocated to the user
 */
/* TODO add sanity checks:
 * 1. ptr is aligned (otherwise it can't be malloc return)
 * 2. check on size field - make sure it's not too small or too large
 * 3. make sure ptr isn't out of range of memory being used
 * 4. make sure ptr isn't already marked as free
 */
void free(void *ptr)
{
    if (ptr == NULL) {
        return; // do nothing with null pointers
    }
    // coalesce both when putting on and taking off the unsorted list
    Block *b = coalesce(USERTOBLOCK(ptr));
    free_list_insert(b, true);
}

/* allocate a region of memory for nmemb objects of the given size and
 * set all bytes in that region to 0. */
void *calloc(size_t nmemb, size_t size)
{
    Block *userptr;
    size_t total_size = nmemb * size;

    // check for overflow
    if (size && (nmemb > SIZE_MAX/size)) {
        errno = ENOMEM;
        return NULL;
    }
    
    userptr = malloc(total_size);
    if (userptr == NULL) {
        return NULL;
    }
    // zero out memory
    memset(userptr, 0, total_size);
    return userptr;
}

/* realloc - try to expand allocated space in place. if not possible,
 * move the block. */
void *realloc(void *ptr, size_t size)
{
    Block *new;
    Block *b;
    size_t old_size, new_size;
    size_t original_size;

    if (ptr == NULL)
        return malloc(size);
    if (size == 0)
        free(ptr);

    // convert user size to block size and align
    size = ALIGN(BLOCKSIZE(size));

    b = USERTOBLOCK(ptr);
    original_size = USERSIZE(b);

    /* coalesce the current block in hopes that this will create enough
     * room for the new size - even if that's not the case, the coalescing
     * would be done anyway when freeing it */
    if (size > SIZE(b)) {
        do {
            old_size = SIZE(b);
            b = coalesce(b);
        } while (SIZE(b) > old_size);
    }

    if (SIZE(b) < size) {
        // if b is the last block in the heap, simply extend the heap.
        // malloc would do this too, but not before searching more free 
        // lists than necessary.
        if (NEXTRAW(b) == epilogue) {
            if (extend_heap(size - SIZE(b)) == NULL) {
                return NULL;
            }
            SETSIZE(b, size);
            new = BLOCKTOUSER(b);
            /* TODO in certain cases, b will be marked as free after 
             * coalescing - there is room for improvement there */
            if (!ISALLOC(b)) {
                MARKALLOC(b);
                HDRTOFTR(b);
            }
        } else {
            // need to move the block
            new = malloc(size);
            if (new == NULL) {
                errno = ENOMEM;
                return NULL;
            }
        }
        if (new != ptr) { // avoid unnnecessary memmove calls
            memmove(new, ptr, original_size);
        }
        /* the old block should only be freed if it doesn't overlap at all
         * with the new block. if the new block is at a lower address, then
         * they do overlap. */
        if (ptr < (void *) new) {
            free(ptr);
        }
    } else {
        /* either the block is being shrunk or coalescing created
         * sufficient room */
        new = BLOCKTOUSER(b);
        // if block is shrinking, don't copy too many bytes
        new_size = original_size < size ? original_size : size;

        if (!ISALLOC(b)) {
            /* see above todo comment*/
            free_list_remove(b);
        }
        
        if (new != ptr) { // avoid unnecessary memmove calls
            memmove(new, ptr, new_size);
        }
        /* split after moving data so data isn't overwritten in case of
         * a shrink */
        split(b, size);
    }

    return new;
}

// ask the operating system for more memory.
static Block *extend_heap(size_t size)
{
    Block *new_block;

    /* current break is the end of the current epilogue - request the
     * arg amount of bytes rounded up to be DWORD aligned, and 
     * the old epilogue is overwritten and alignment is preserved */
    if (sbrk(size) == (void *) -1) {
        fprintf(stderr, "req_memory failed: ran out of memory\n");
        errno = ENOMEM;
        return NULL;
    }
    // set and initialize the new block
    new_block = epilogue;
    MARKALLOC(new_block);
    SETSIZE(new_block, size);
    // set and initialize new epilogue
    epilogue = (Block *) ((void *) epilogue + size);
    BOUNDINIT(epilogue);
    return new_block;
}

/* shrink b to the given size and free the remaining space if there's room.
 * requires that size is aligned.
 */
static void split(Block *b, size_t size) 
{
    size_t new_size;
    Block *new_block;

    if ((new_size = SIZE(b) - size) >= MINBLOCK) {
        // enough room to split
        SETSIZE(b, size);
        /* exception to the note that NEXTRAW should only be used for 
         * coalescing */
        new_block = NEXTRAW(b);
        SETSIZE(new_block, new_size);
        // place the remainder on the unsorted list to reduce fragmentation
        free_list_insert(new_block, true);
    }
}

// find the free list index for a size - unsorted list is index 0
static inline int find_list_index(size_t s)
{
    int l = 0;
    if (s < 512)
        return (s >> 3) - 1;
    else {
        s >>= 10;
        while (s) {
            l++;
            s >>= 1;
        }
        return l < 12 ? 63 + l : LISTCOUNT - 1;
    }
}

/* 
 * find a block with block size >= size in list and return it. if no
 * block of sufficient size exists in the list, return NULL. */
static inline Block *find_in_list(Block *list, size_t size)
{
    Block *curr = list;
    if (size <= MAXSMALL)
        return list; // for small sizes, just return the head
    while (curr != NULL) {
        // for larger sizes, must check the block is big enough
        if (SIZE(curr) >= size)
            return curr;
        curr = curr->next;
    }
    return NULL;
}

/* search all free lists starting at appropriate idx for a block of at
 * least the given size. blocks are coalesced as they're taken off
 * of the unsorted list */
static Block *find_block(size_t size)
{
    Block *list, *found_block;
    int list_index;

    /* search the unsorted list first, coalescing blocks and returning them
     * to the main lists on the way */
    // TODO could be cleaner probably with a do while
    found_block = free_lists[0];
    while (found_block != NULL) {
        found_block = coalesce(found_block);
        if (!ISALLOC(found_block)) {
            free_list_remove(found_block);
        }
        if (SIZE(found_block) >= size) {
            return found_block;
        }
        // put block on the main lists
        free_list_insert(found_block, false);
        found_block = free_lists[0];
    }

    /* search the main lists, starting with the smallest one that
     * contains big enough blocks */
    for (list_index = find_list_index(size); list_index < LISTCOUNT; 
         list_index++) {
        list = free_lists[list_index];
        if ((found_block = find_in_list(list, size))) {
            return found_block; // found a large enough block
        }
    }
    // no block of sufficient size was found
    return NULL;
}

/* insert a block into the appropriate address order free list. if unsorted
 * is true, it's put onto the unsorted list instead */
static void free_list_insert(Block *new_block, bool unsorted)
{
    // get the appropriate list's head
    Block **head = unsorted ? &free_lists[0] : 
                              &free_lists[find_list_index(SIZE(new_block))];

    MARKFREE(new_block);
    MARKUNQUICK(new_block);
    HDRTOFTR(new_block);

    if (*head == NULL) {
        *head = new_block;
        new_block->next = NULL;
        new_block->prev = NULL;
        return;
    }
    new_block->next = *head;
    (*head)->prev = new_block;
    *head = new_block;
    new_block->prev = NULL;
}

/* remove b from the global free list and mark it as allocated and
 * uncoalescable
 * 
 * note: it only matters what free list b is on if b is the head of that
 * list. the only two lists it can be on are the unsorted list and the
 * appropriate list for its size, so if it's not the head of either of
 * those, than it can be treated as if it's on either
 */
static void free_list_remove(Block *b)
{
    Block **size_head = &free_lists[find_list_index(SIZE(b))];
    Block **unsorted_head = &free_lists[0];
    Block **head;

    // if b is the head of its list, update the head
    if (b == *size_head || b == *unsorted_head) {
        head = b == *size_head ? size_head : unsorted_head;
        *head = b->next;
        if (*head != NULL)
            (*head)->prev = NULL;
    } else {
        // if b isn't the head, it must have a previous block
        b->prev->next = b->next;
    }
    if (b->next != NULL)
        b->next->prev = b->prev;
    MARKALLOC(b);
    HDRTOFTR(b);
}

// coalesce b with its immediate neighbors if possible
static Block *coalesce(Block *b)
{
    Block *prev, *next, *local_block;
    size_t new_size = SIZE(b);
    local_block = b;
    // for the prev and next blocks, remove them from their free lists
    // and update the new block size if they're coalescable
    if (!PREVUNCOAL(b)) {
        prev = PREVRAW(b);
        free_list_remove(prev);
        new_size += SIZE(prev);
        // prev block is now the start of the new block
        local_block = prev;
    }
    if (!NEXTUNCOAL(b)) {
        next = NEXTRAW(b);
        free_list_remove(next);
        new_size += SIZE(next);
    }
    if (new_size != SIZE(b)) {
        // coalescing is possible
        if (!ISALLOC(b))
            free_list_remove(b);
        SETSIZE(local_block, new_size);
    }
    return local_block;
}
