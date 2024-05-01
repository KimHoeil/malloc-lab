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

/* Basic constants and macros */
#define WSIZE 4             /* 워드,헤더/푸터 사이즈(바이트) Word and header/footer size (bytes) */
#define DSIZE 8             /* 더블 워드 (8바이트) Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* heap을 늘릴 때 늘리는 양 4096byte = 4kb Extend heap by this amout (bytes)*/

#define MAX(x, y) ((x) > (y) ? (x) : (y)) /* x가y보다 크면 x 작으면 y 리턴 */

/* Pack a size and allocated bit into a word */
/* 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))              /* p가 참조하는 워드를 읽어서 리턴 */
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* p가 가리키는 워드에 val을 저장 */

/* Read the size and allocated fields from address p */
/* 각각 주소 p에 있는 헤더 또는 풋터의 size와 할당 비트를 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer*/
/* 블록 포인터 bp가 주어지면, 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴 */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
/* 다음과 이전 블록의 블록 포인터를 각각 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team hoeil",
    /* First member's full name */
    "king_hoeil",
    /* First member's email address */
    "king_hoeil123@jungle.ac.kr",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 메모리 할당 방식 */
// #define FIRST_FIT
#define NEXT_FIT
static char *last_allocated;
// #define BEST_FIT

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 최초 가용 블록으로 힙 생성하기 */

    /* Creat the initial empty heap*/
    /* 16바이트 크기가 나오지 않으면 return -1*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            /* Alignment padding*/
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header*/
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer*/
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header*/
    heap_listp += (2 * WSIZE);                     /* heap_listp 포인터를 프롤로그 헤더와 푸터 사이에 위치 시킴 */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    /* 힙을 4096 바이트로 확장하고 초기 가용 블록 생성 */
    /* 공간이 없다면 return -1 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    /* 새 가용 블록으로 힙 확장하기*/

    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해줌)
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /* 가용 리스트에서 블록 할당하기 */

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 (헤더4, 푸터4, 저장공간 8)
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 8의 배수로 올림처리

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;

#ifdef FIRST_FIT
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }

#elif defined(NEXT_FIT)
    if (last_allocated == NULL)
        last_allocated = heap_listp;

    for (bp = last_allocated; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_allocated = bp;
            return bp;
        }
    }

    // 마지막 위치부터 할당할 곳을 못찾았다면, 처음부터 재탐색 시작.
    // last_allocated 뒤로는 할당할 곳이 없으므로 last_allocated까지만 탐색
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0 && last_allocated > bp; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_allocated = bp;
            return bp;
        }
    }
#elif defined(BEST_FIT)
    void *best_fit = NULL;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            // 기존에 할당하려던 공간보다 더 최적의 공간이 나타났을 경우 리턴 블록 포인터 갱신
            if (!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit)))
                best_fit = bp;
        }
    }
    return best_fit;
#else
#endif

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) /* Case 1 모두 앞뒤 할당되었을 때*/
    {
        return bp;
    }

    else if (prev_alloc && !next_alloc) /* Case 2 다음 블록이 빈 경우*/
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) /* Case 3 이전 블록이 빈 경우*/
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else
    { /* Case 4 이전 블록, 다음 블록이 모두 빈 경우*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    last_allocated = bp; // 통합해준후 next-fit 탐색시 사용하기 위해 last_allocated 포인터 갱신
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
