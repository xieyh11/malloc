/*
 * mm.c
 * Malloc function with a first fit segregated explicit doubli linked free list
 * Each chunck of memory is aligned by 8 bytes, with a minimum size of 24.
 * The segregated list is divided into 5 small classes (24, 32, 40, 48, 56) 
 * bytes, and the rest are class sizes of 2^6 ~ 2^(N-1) bytes (where as N-1 is 
 * max size). A free block greater than 2^(N-1) is automatically added to the 
 * greatest class size (2^(N-1)) when freed. Immediate coalecsing takes place 
 * when a block is freed. When realloc is called, the function checks whether 
 * the original block can be expanded at the same address by checking whether 
 * the next block is a free block and big enough. mm_check checks whether all 
 * blocks are bigger than the minimum size of 24 and whether all the free 
 * blocks in the linked list are actually free blocks. Other debugging 
 * functions include checking whether pointers point to a valid address in the 
 * heap and functions that print out a specific block, the free list, and the 
 * heap in order to check if blocks are overlapping or if free blocks have 
 * escaped coalescing. Printf is used to tell which function is called, and w
 * here the error took place, if there is one.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name (id1+id2)*/
    "yoheioka+kuriakin",
    /* First member's full name */
    "Yohei Oka",
    /* First member's email address */
    "yoheioka@fas.harvard.edu",
    /* Second member's full name (leave blank if none) */
    "Kuriakin Zeng",
    /* Second member's email address (leave blank if none) */
    "kuriakin@fas.harvard.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*Basic constants and macros*/
#define WSIZE 4					// word size (bytes)
#define DSIZE 8					// Double word size (byte)
#define CHUNKSIZE (1<<6)		// Extend heap by this amount (bytes)

#define MAX(x,y)  ((x) > (y) ? (x) : (y))

/* Pack a size and allococated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p*/
#define GET(p)			(*(unsigned int *)(p))
#define PUT(p, val)		(*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)		(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) 		((char*)(bp) - WSIZE)
#define FTRP(bp)		((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)	((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

/* move-function in a size class of the free list*/
#define NEXT_LL(bp) (*(void **)(bp)) 
#define PREV_LL(bp) (*(void **)((bp)+8))

/* definition for sizes*/
#define MINBLKSIZE 24
#define SMALLBLK 5  //(24,32,40,48,56 all< 2^6)
#define MINCLASS 6  //min 2^N size class in linked list
#define MAXCLASS 22 //max 2^(N-1) size class in linked list 
void*** grouparr;   //pointer to size class array
size_t arrsize;     //size of size class array
void* heap_listp;   //pointer that points to the start of USABLE heap
void* lo;			//points to the beginning of the heap
void* hi;			//points to the end of heap, refreshed when extend_heap 
					//is called

/* global variables are not allowed but used for debugging
//int malloccounter; 
//int freecounter; 	 
*/

/* functions*/
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *bp, size_t size);
static void rmvll(void *bp);		//remove free block from linked list
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void addfree(void *bp, size_t asize); //add free block to linked list

/*debuggers*/
void *mem_heap_lo(void); //Returns a generic pointer to the first byte in 
						 //the heap. 
void *mem_heap_hi(void); //Returns a generic pointer to the last byte in 
						 //the heap.
static int allocated(const void *p); //check whether block is allocated
static int in_heap(const void *p);  //check if pointer points to a valid 
									//address within heap
static void print_heap(void); 		//prints heap
static void print_block(void *cp);  //prints block
static void print_free(void);		//prints free list
static int mm_check(void);			


/************  Doubly Linked List Functions  *************/
/*
 * remove from doubly Linked list
 */ 
static void rmvll(void *bp) 
{
	//printf("start rmvll remove %p \n", bp);
	if(PREV_LL(bp)!=NULL)
    	NEXT_LL(PREV_LL(bp)) = NEXT_LL(bp);
    //printf("right here \n");
  	if((NEXT_LL(bp))!=NULL)
    	PREV_LL(NEXT_LL(bp)) = PREV_LL(bp);
    //printf("end rmvll\n");
}

/***************  end Linked List Functions  *************/



/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	//printf("initializing\n");
	//malloccounter = 1;
	//freecounter = 1;
	
	arrsize = (MAXCLASS-MINCLASS+SMALLBLK)*8;		//size of size class array
	
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(arrsize+4*WSIZE)) == (void *)-1)
		return -1;
		
	grouparr = (void***)heap_listp;	
	PUT (heap_listp+arrsize, 0);						// Alignment padding
	PUT (heap_listp+arrsize+(1*WSIZE), PACK(DSIZE, 1));	// Prologue header
	PUT (heap_listp+arrsize+(2*WSIZE), PACK(DSIZE, 1));	// Prologue footer
	PUT (heap_listp+arrsize+(3*WSIZE), PACK(0,1));		// Epilogue header
	//printf("initializing. before usable heap : %p\n", heap_listp);
	heap_listp += (arrsize+(2*DSIZE));		//put heap_listp inside prologue
	//printf("initializing. after usable heap : %p\n", heap_listp);
	
	arrsize /= 8; 	//divide by 8, so we can index by element, not by bytes
    
    //initialize class size array to NULL
    int i; 
  	for(i=0;i<arrsize;i++)
    	grouparr[i] = NULL;
    	
	/******
	grouparr={24,32,40,48,56,2^6,2^7,......2^21} (21 elements)
	******/
	
	
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    	return -1;
    	
    //printf("initializing complete\n");
    lo = mem_heap_lo();		//start of heap
    hi = mem_heap_hi();		//end of heap
    //printf("hi: %p, lo:%p\n", lo, hi); 
    return 0;
}



/* 
 * extend_hea - Extends the heap with a new free block
 */
static void *extend_heap(size_t words)
{
	//printf("start extend heap. extend by \n");
	char *bp;
	size_t size;

	/* Allocate an even numer of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
		
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));			// Free block header 
	PUT(FTRP(bp), PACK(size, 0));			// Free block footer
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));	// New epilogue header
	hi = mem_heap_hi(); 					// update end of heap
	
	
	//printf("finish extend heap \n");
	/* Coalesce if the previous block was free */
	return coalesce(bp); 
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
	//printf("start malloc size: %d \n", size);
    /* Ignore spurious requests */
    if (size == 0)
    	return NULL;
    	
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= 2*DSIZE)		//if smaller than MINBLKSIZE, set to 24
    	size = MINBLKSIZE;
    else
    	size = ALIGN(size+DSIZE);
    //printf("alligned size: %d \n", size);
    	
    /* Search the free list for a fit (first fit) */  
    int i;
  	void* bp=NULL;
  	
  	//find size class to look in
  	if (size < 64)		//look in the 5 small classes
  	{
  		for(i=0; i< SMALLBLK; i++)
  		{
  			if (size<=i*8 + 24)
				break;
		}
	}
	
	else if (size < (1<<MAXCLASS)) //look in the classes 2^6~2^21
	{
		for(i=MINCLASS; i<MAXCLASS; i++)
		{	
			if (size <= (1<<i))
			{
				i -= 1;			//make it easier to index in the next step
				break;
			}
		}
	}
	
	else 				//if size > 2^21
		i = arrsize-1;
  	
  	int found = 0;
  	
	//search for free blocks in classes, if not there, move to next class
	for(;i<arrsize; i++)
	{
		//printf ("searching 2^ %d \n",i+1);
    	for(bp=grouparr[i]; bp!=NULL; bp=NEXT_LL(bp))
    	{
      		if((GET_SIZE(HDRP(bp)))>=size)
      		{
				i=arrsize;	//found a block  big enough
      			found = 1;
      			//printf ("found block big enough!\n");
      			break;
      		}
    	}
    	if (found == 1)
    		break;
	}
	
	
	//printf("malloc count: %d \n", malloccounter);		
	///malloccounter +=1 ;
	/*if (malloccounter == 70)			//debugger for specific trace
	{
		mm_check();
		print_heap();
		print_free();
	}
	*/
	
	
	//if we found a block, place it at that address
	if(bp!=NULL)
	{
    	place(bp, size);
    	//printf("finish malloc pointer: %p\n", bp);
    	//print_heap();
  	    //mm_check();
	    //print_free();
    	return bp;
    }
    
    // No fit found. Get more memory (extend_heap) and place the block 
    else
    {
    	//printf ("no fit! \n");
    	size_t extendsize = MAX(size,CHUNKSIZE);
    	if((bp = extend_heap(extendsize/WSIZE)) == NULL)
    		return NULL;
    	place(bp, size);
    	//printf("finish malloc pointer: %p\n", bp);
    	//mm_check();
    	//print_heap();
    	//print_free();
    	return bp;
 	}
}




/*
 * mm_realloc - checks whether the original block can be expanded at the same 
 * 				address by checking whether the next block is a free block and 
 *				big enough if not, free the original block and call mm_malloc
 */
void *mm_realloc(void *bp, size_t size)   
{
	//printf("start realloc \n");
	size_t oldsize;		//old size
  	void *newbp;		//new pointer

  	/* if size is equal to zero, the call is equivalent to mm_free(bp) */
  	if(size == 0) 
	{
    	mm_free(bp);
    	return 0;
  	}

  	/* if bp is NULL, the call is equivalent to mm_malloc(size) */
  	if(bp == NULL) 
  	{
    	return mm_malloc(size);
  	}
  	
  	//check if pointer is a valid address within the heap
	if(in_heap(bp)==0)
		return 0;


  	/* if next block is a free block */ 
  	if(!GET_ALLOC(HDRP(NEXT_BLKP(bp)))) 
  	{
  		//printf("0 \n");
    	if(size <= 2*DSIZE) //if size< minimum, set to 24
 			size = MINBLKSIZE;
    	else
    		size = ALIGN(size+DSIZE);;	//align by 8 bytes
    		
    	oldsize = GET_SIZE(HDRP(bp));
    	void* next = NEXT_BLKP(bp);
    	size_t nextsize = GET_SIZE(HDRP(next));
    	size_t extra = size-oldsize; //bytes that can't fit into the original
    
    	//if next free block can fit extention
    	if(nextsize>=extra)
    	{
    		//printf("1 \n");
    		/*if we can furthermore split the remainder*/
    		if((nextsize-extra) >= MINBLKSIZE)
    		{
    			//printf("1.1 \n");
				rmvll(next);
				PUT(HDRP(bp), PACK(size,1));
				PUT(FTRP(bp), PACK(size,1));
				next = NEXT_BLKP(bp);
				PUT(HDRP(next), PACK(nextsize-extra,0));
				PUT(FTRP(next), PACK(nextsize-extra,0));
				addfree(next, nextsize-extra);
				//printf("end realloc \n");
				return bp;
    		}
    	
    		//if not, allocate the whole block
      		else
      		{
      			//printf("1.2 \n");
      			rmvll(next);
				PUT(HDRP(bp), PACK(oldsize+nextsize,1));
				PUT(FTRP(bp), PACK(oldsize+nextsize,1));
				//printf("end realloc \n");
				rmvll(next);
				return bp;
      		}
    	}
  	}
  	
  	/* if we couldn't expand at the same address */
  	//printf("3 \n");
  	
    newbp = mm_malloc(size);	//call mm_malloc
    
    /* If realloc gets an error */
    if(!newbp) 
    	return 0;
    
    /* Copy the contents of the old data */
    oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize) 
    	oldsize = size;
    memcpy(newbp, bp, oldsize);
    
    /* Free the old block. */
    mm_free(bp);
    //printf("end realloc \n");

    return newbp;    
}

/*
 * mm_free - Freeing block, check if coalescing is possible
 */
void mm_free(void *bp)
{
	//printf("start free! pointer: %p\n", bp);
	
	/* check if pointer is valid */
	if (allocated(bp)==0 || in_heap(bp)==0)
	{
		//printf("pointer doesn't exist \n");
		return;
	}	
	
	size_t size = GET_SIZE(HDRP(bp));
	
	
	//printf("freeing size %d\n", size);
	
	/*free the block*/
	PUT(HDRP(bp), PACK(size,0));	
	PUT(FTRP(bp), PACK(size,0));
	bp = coalesce(bp);
	
	
	//printf("end free \n");         //debugger for specific trace
	//printf("free count: %d \n", freecounter);
	//freecounter +=1 ;
	//if (freecounter == 47)
	/*{
		mm_check();
		print_heap();
		print_free();
	}
	*/

}


/*
 * coalesce - coalesce blocks, 4 cases 
 */
static void *coalesce(void *bp)
{
	//printf("start coalesce \n");
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	/* Case 1: previous and next blocks are both allocated */
	if (prev_alloc && next_alloc)
	{
		//printf("Case 1 AFA \n");
		addfree(bp,size);
	}
	
	/* Case 2: previous block is allocated and the next block is free */
	else if (prev_alloc && !next_alloc)
	{
		//printf("Case 2 AFF \n");
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		rmvll(NEXT_BLKP(bp));	//remove second free block
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));	
		addfree(bp, size); 		//add to free linked list
	}
	
	/* Case 3: previous block is free and the next block is allocated */
	else if (!prev_alloc && next_alloc)
	{
		//printf("Case 3 FFA \n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));		
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));		
		rmvll(PREV_BLKP(bp));			//free previous free block from list
		addfree(PREV_BLKP(bp), size);	//add coalesced free block to list
		bp = PREV_BLKP(bp);
	}	
	
	/* Case 4: previous and next blocks are both free*/
	else
	{
		//printf("Case 4 FFF \n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));	
		rmvll(NEXT_BLKP(bp));// remove last free block from list
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		
		rmvll(PREV_BLKP(bp));			//free previous free block from list
		addfree(PREV_BLKP(bp), size);	//add coalesced free block to list
		bp = PREV_BLKP(bp);
	}
	//printf("end coalesce \n");
	return bp;
}




/*
 *Place - places the requested sized block in the given free block
 */
static void place(void* bp, size_t asize)
{
	//printf("start place size: %d\n", asize);
	size_t csize = GET_SIZE(HDRP(bp));
	//printf("csize - asize: %d - %d = %d\n", csize, asize, csize - asize);
	
	//if the remainder is big enough to become another free block 
	if ((csize - asize) >= MINBLKSIZE)
	{
		//printf("there is going to be remainder. size: %d\n", asize);
	    rmvll(bp);			//remove free block from free list
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));

		addfree(bp, csize-asize);
	}
	
	else
	{
		//printf("no remainder\n");
		rmvll(bp);
		PUT(HDRP(bp), PACK(csize,1));
		PUT(FTRP(bp), PACK(csize,1));
	}
	//printf("end place \n");
}



/*
 * addfree- Add free block to segegrated list
 */
static void addfree(void* bp, size_t asize) 
{
	//printf("start addfree size: %d \n", asize);
  	//search for correct size class
  	if (asize < 64)		//5 small size class 
  	{
  		int i;
  		for(i=0; i< SMALLBLK; i++)
  		{
  			if (asize<=i*8 + 24)
  			{
      			NEXT_LL(bp) = grouparr[i];//insert by changing pointers
      			PREV_LL(bp) = (grouparr+i); 
      			if(NEXT_LL(bp)!=NULL)
					PREV_LL(NEXT_LL(bp)) = bp;
      			grouparr[i]=bp;
      			//printf("end addfree. added to class %d \n", i*8 + 24 );
      			//print_free();
      			return;
  			}
  		}
  	}
  	
  	else if (asize < (1<<MAXCLASS))   //size class 2^6~2^21
	{
		int j;
  		for(j=MINCLASS; j<MAXCLASS;j++) 
  		{
    		if(asize<=(1<<j)) 
    		{
      			NEXT_LL(bp) = grouparr[j-1];//insert by changing pointers
      			PREV_LL(bp) = (grouparr+j-1); 
      			if(NEXT_LL(bp)!=NULL)
					PREV_LL(NEXT_LL(bp)) = bp;
      			grouparr[j-1]=bp;
      			//printf("end addfree. added to class 2^ %d \n", j);
      			//print_free();
      			return;
    		}
  		}
  	}

  	//if size >= 2^21
  	NEXT_LL(bp) = grouparr[arrsize-1]; 	//insert by changing pointers
  	PREV_LL(bp) = (grouparr+arrsize-1);	
  	if(NEXT_LL(bp)!=NULL)
    	PREV_LL(NEXT_LL(bp)) = bp;
 	grouparr[arrsize-1] = bp;	
 	//printf("end addfree. added to class 2^17 \n");
 	//print_free();
	return;
}






/*************************** DEBUGGING FUNCTIONS **************************/

/*
 * in_heap - check whether pointer points to a valid address in heap
 * 			 retunr 1 if valid
 */
static int in_heap(const void *p) 
{
    if (p < mem_heap_hi() && p >= mem_heap_lo())
    	return 1;
    else 
    	return 0;
}

/*
 * allocated - check whether block is already allocated, return 1 if allocated
 */
static int allocated(const void *p) 
{
    if (GET_ALLOC(HDRP(p)))
    	return 1;
    else 
    	return 0;
}

/*
 * heap checker
 *
 * mm_check - Returns 1 if heap is consistent. 
 *			  check 1) all blocks are greater than minimum size MINBLKSIZE
 * 					2) blocks in free list are indeed all free
 */
static int mm_check(void)
{
	printf("starting Heap Consistency Checker \n");
	void *cp = heap_listp;
    
	//Check if all blocks are at least MINBLKSIZE	
    while(cp < hi - 7)
	{
		size_t blocksize = GET_SIZE(HDRP(cp));
		if(blocksize < MINBLKSIZE)
		{
			printf("ERROR: block is smaller than minimum size at %p \n", cp);
            print_block(cp);
            return 0;
		}
		cp = NEXT_BLKP(cp);
	}
    
    //Check if blocks in free list are all free
    int i;    
    for(i = 0; i < MAXCLASS-MINCLASS+SMALLBLK; i++)
	{
        for(cp=grouparr[i]; cp!=NULL; cp=NEXT_LL(cp))
        {
			if (allocated(cp)==1)
			{
				printf("ERROR: block in linked list is not free at %p \n", cp);
				print_block(cp);
            	return 0;
			}
		}
	}
    
    printf("ending Heap Consistency Checker \n");
	return 1;    
}

/*
 * print_heap - Prints all blocks in heap
 */
void print_heap(void) 
{
    printf("***********HEAP************\n");
    printf(" from %p ~ %p\n", lo, hi);
    void *cp = heap_listp;
    printf("beginning of usable heap: %p\n", cp);
    while (cp < hi - 7) 
    {
        print_block(cp);
        cp = NEXT_BLKP(cp);
    }
    printf("***********HEAP END*********\n");
    printf("\n");    
}

/*
 * print_block - Prints detailed information of a specific block
 */
static void print_block(void *cp)
{
	printf("%p | size: %d | allocated: %d\n", cp, 
					GET_SIZE(HDRP(cp)), allocated(cp));
}

/*
 * print_free - Prints all free memory blocks in free lists
 */
static void print_free(void) 
{
	printf("***********FREE LIST************\n");
	int i;
	int classsize;
	void *cp;
	
    for(i = 0; i < MAXCLASS-MINCLASS+SMALLBLK; i++)
	{
		if ( i < SMALLBLK)
		{
			classsize = 24 + i*8;
			printf("***IN CLASS SIZE %d BYTES****\n", classsize);
		}
		else 
			printf("***IN CLASS SIZE 2^%d BYTES****\n", i+1);
			
        for(cp=grouparr[i]; cp!=NULL; cp=NEXT_LL(cp))
        {
			print_block(cp);
		}
	}
	printf("****END OF FREE LIST************\n");
}







