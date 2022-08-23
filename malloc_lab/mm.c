/*
 * mm.c -  Simple allocator based on explicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *     -----------------------------------------------------------------------------
 *    | the Previous unallocated Block pointer | the Next unallocated Block pointer |  .....
 *     -----------------------------------------------------------------------------
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * the free list will be added new free blocks onto its head every time there is inserted a 
 * new free block;
 * the free list is like a double linked list with each blocks has one previous pointer and 
 * next pointer point to another free block;
 * allocator only needs to traverse over the free blocks pointers to see the next free 
 * blocks
 * I have also set up experiences to test the most efficient parameter when using find_fit 
 * functions to magnify the efficiency of finding free blocks
 * The allocated prologue and epilogue blocks are overhead that eliminate edge conditions 
 * during coalescing.
 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
    /* First and last name */
    "Sirui Kang",
    /* UID */
    "305*******",
    /* Custom message (16 chars) */
    "hihihi I'm Catherine",
};

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body;
} block_t;
/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };
//* define certan macros and micros */
#define ALIGNMENT 8 /* this is a double word alignment */
#define MINBLOCKSIZE 16
#define WSIZE      sizeof(void *) /* the footer or header size */
#define CHUNKSIZE  (1 << 16)      /* how many size will be expanded by heap */
#define DSIZE      (2 * WSIZE)    /* would be the double size of wsize*/
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* set the size and the status of whether it is allocated into block*/
#define set(size, alloc)  ((size) | (alloc))
/* to see content at vertain addess */
#define GET(a)       (*(uintptr_t *)(a))
#define PUT(a, val)  (*(uintptr_t *)(a) = (val))
#define GET_SIZE(a)   (GET(a) & ~(DSIZE - 1))
#define GET_ALLOC(a)  (GET(a) & 0x1)
/*get the address of header or footer of a block */
#define HDRP(block)  ((void *)(block) - WSIZE)
#define FTRP(block)  ((void *)(block) + GET_SIZE(HDRP(block)) - DSIZE)
/*get the address of next or previous block of the current block */
#define NEXT_BLK(block)  ((void *)(block) + GET_SIZE(HDRP(block)))
#define PREV_BLK(block)  ((void *)(block) - GET_SIZE((void *)(block) - DSIZE))
#define GET_NEXT_b(block)  (*(char **)(block + WSIZE))
#define GET_PREV_b(block)  (*(char **)(block))
#define SET_NEXT_b(block, qp) (GET_NEXT_b(block) = qp)
#define SET_PREV_b(block, qp) (GET_PREV_b(block) = qp)
static char *list = 0; 
static char *free_list_head = 0;
static block_t *prologue; /* pointer to first block */
/* Function prototypes for internal helper routines */
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);
static void *coalesce(void *block);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *block, size_t asize);
static void insert_in_free_list(void *block); 
static void remove_from_free_list(void *block); 
static void mm_checkheap(int verbose);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
  
  /* initialize empty heap. */
  if ((list = mem_sbrk(16*WSIZE)) == NULL)
  {
     return -1; //error
  }
  else
  {
    /* initialize Alignment,Prologue header and footer and Epilogue */
  PUT(list, 0);                           
  PUT(list + (1 * WSIZE), set(DSIZE, 1)); 
  PUT(list + (2 * WSIZE), set(DSIZE, 1)); 
  PUT(list + (3 * WSIZE), set(0, 1));     
  free_list_head = list + 2*WSIZE; 
  /* Extend heap */
  if (extend_heap(4) == NULL)
  { 
    return -1; //error
  }
  else
  {
    return 0; //no error
  }
  }
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
  size_t asize;    /* adjusted block size */
  size_t extendsize;  /* amount to extend heap if no fit */
  void *block;
  /* Ignore spurious requests. */
  if (size == 0)
  {
     return NULL;
  }
  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
  {
     asize = 2 * DSIZE;
  }
  else
  {
     asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
  }
  /* Search the free list for a fit. */
  if ((block = find_fit(asize)) != NULL) {
    place(block, asize);
    return block;
  }

  /* No fit found.  Get more memory and place the block. */
  extendsize = MAX(asize, CHUNKSIZE);// extend by the larger of the two
  if ((block = extend_heap(extendsize / WSIZE)) != NULL) 
  {
    place(block, asize);
    return block;
  } 
    return NULL;
} 
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *ptr){
  size_t size;
  if (ptr == NULL)
  {
    return; //returns nothing
  }
  else
  {
  size = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), set(size, 0));
  PUT(FTRP(ptr), set(size, 0));
  coalesce(ptr);
  }
}
/* $end mmfree */
/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}
/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *block){

  //to set zero of prev_alloc if prev block is set or size is 0
  size_t NEXT_ALLOC = GET_ALLOC(HDRP(NEXT_BLK(block))  );
  size_t PREV_ALLOC = GET_ALLOC(FTRP(PREV_BLK(block))  ) || PREV_BLK(block) == block;
  size_t s = GET_SIZE(HDRP(block));
  /* case 1: previous one is free and next is not */  
  if (NEXT_ALLOC && !PREV_ALLOC) {               
    s += GET_SIZE( HDRP(PREV_BLK(block))  );
    block = PREV_BLK(block);
    remove_from_free_list(block);
    PUT(HDRP(block), set(s, 0));
    PUT(FTRP(block), set(s, 0));
  }
   /* case 2: next one is free but previous is not */   
  else if (!NEXT_ALLOC && PREV_ALLOC) {                  
    s += GET_SIZE( HDRP(NEXT_BLK(block))  );
    remove_from_free_list(NEXT_BLK(block));
    PUT(HDRP(block), set(s, 0));
    PUT(FTRP(block), set(s, 0));
  }
  /* case 3: prev and next are all free */ 
  else if (!PREV_ALLOC && !NEXT_ALLOC) {                
    s += GET_SIZE( HDRP(PREV_BLK(block))  ) + GET_SIZE( HDRP(NEXT_BLK(block))  );
    remove_from_free_list(PREV_BLK(block));
    remove_from_free_list(NEXT_BLK(block));
    block = PREV_BLK(block);
    PUT(HDRP(block), set(s, 0));
    PUT(FTRP(block), set(s, 0));
  }
  insert_in_free_list(block);
  return block;
}
/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) {
  char *block;
  size_t s;
  s = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  // minimum block size is 16 bytes
  if (s < 16)
  {
    s = 16;
  }
  /* allocate memory space if not enough */
  if ((int)(block = mem_sbrk(s)) == -1)
  { 
    return NULL;
  }
    /* The newly acquired region will start directly after the epilogue block */ 
    /* Initialize free block header/footer and the new epilogue header */
    /* use old epilogue as new free block header */
  PUT(HDRP(block), set(s, 0));         
  PUT(FTRP(block), set(s, 0));        
  PUT(HDRP(NEXT_BLK(block)), set(0, 1)); 
 /* Coalesce if the previous block was free */
  return coalesce(block);
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize){
  void *block;
  static int l_s = 4; //the last size that has been allocated
  static int time = 0; //count the number we have find fit before
  if( l_s == (int)asize){
      if(time>60) //doing lab to see the most suitable time number
      {  
        int extendsize = MAX(asize, 4 * WSIZE);
        block = extend_heap(extendsize/8);//doing lab to see the most suitable number to be divided
        return block;
      }
      else
        time++;
  }
  else
    time = 0;
  for (block = free_list_head; GET_ALLOC(HDRP(block)) == 0; block = GET_NEXT_b(block) ){
    if (asize <= (size_t)GET_SIZE(HDRP(block)) ) /* block must be free and the size must be large enough to hold the request */
    {
      l_s = asize;
      return block;
    }
  }
  return NULL; /* no fit */
}

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(void *block, size_t asize){
  size_t s = GET_SIZE(HDRP(block)); //get the size of header of block recorded
  if ((s - asize) >= 16 * WSIZE) /* split the block by updating the header and marking it allocated*/
  {
    /* set footer of allocated block*/
    /* update the header of the new free block */
    /* update the footer of the new free block */
    PUT(HDRP(block), set(asize, 1));
    PUT(FTRP(block), set(asize, 1));
    remove_from_free_list(block);  // then it is allocated and need to be removed from free list
    block = NEXT_BLK(block);
    PUT(HDRP(block), set(s-asize, 0));
    PUT(FTRP(block), set(s-asize, 0));
    coalesce(block);
  }
  else {
     /* splitting the block will cause a splinter so we just include it in the allocated block */
    PUT(HDRP(block), set(s, 1));
    PUT(FTRP(block), set(s, 1));
    remove_from_free_list(block); // then it is allocated and need to be removed from free list
  }
}

/*insert unallocated block into the free_list*/
static void insert_in_free_list(void *block){
  SET_NEXT_b(block, free_list_head);  //set the blcok to be the head
  SET_PREV_b(free_list_head, block); 
  SET_PREV_b(block, NULL); //if the block is the head, then its previous will be null
  free_list_head = block; 
}

/*Removes allocated block from free_list*/
static void remove_from_free_list(void *block){
  if (GET_PREV_b(block)) //if the previous block is allocated
  {
     SET_NEXT_b(GET_PREV_b(block), GET_NEXT_b(block));
  }
  else //the previous block is not allocated
    free_list_head = GET_NEXT_b(block);
    SET_PREV_b(GET_NEXT_b(block), GET_PREV_b(block));
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose)
{
  void *block;
  //theck if the prologue header is proper
   if(!GET_ALLOC(HDRP(list)))
   {
    printf("error!!!!!!\n");
    return 0;
   }
  if (GET_SIZE(HDRP(list)) != DSIZE)
  {
    printf("error!!!!!!\n");
     return 0;
  }
  checkblock(list); //check every block in the list
  //theck if the epilogue header is proper
  if (GET_SIZE(HDRP(block)) != 0)
  {
     printf("error!!!!!!\n");
   return 0;
  }
  if(!GET_ALLOC(HDRP(block)))
  {
    printf("error!!!!!!\n");
    return 0;
  }
    return 1;
}

static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    uint32_t hsize, halloc, fsize, falloc;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t *footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}
static void checkblock(block_t *block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    footer_t *footer = get_footer(block);
    if (block->block_size != footer->block_size) {
        printf("Error: header does not match footer\n");
    }
}
