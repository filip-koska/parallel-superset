#pragma once

#include <assert.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef LOG_SUMSET
#include <stdio.h>
#include <pthread.h>

static pthread_mutex_t _stdout_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

// Maximum number ever added to multisets.
#define MAX_D 50

// Details of the sumset implementation.
typedef uint64_t Word;
#define MAX_BITS (MAX_D * MAX_D)
#define BITS_PER_WORD (sizeof(Word) * 8)
#define MAX_WORDS ((MAX_BITS + BITS_PER_WORD - 1) / BITS_PER_WORD)

// Represents the sumset A^Σ of a multiset A, with some info about A.
typedef struct Sumset {
    // Element last added to the multiset A (1 if nothing has been added).
    int last;

    // Sum of all elements (this is also the largest value in the sumset, but we cache it here).
    int sum;

    // Pointer to sumset this one was derived from (see sumset_add), allows recovering A (with solution_build()).
    const struct Sumset* prev;

    // The i-th bit is set iff i is in the sumset. Accessing this directly is forbidden for this homework.
    Word sumset[MAX_WORDS];
} Sumset;

// Initialize a sumset to represent an empty multiset A (with last=1 and prev=NULL), A^Σ={0}.
static inline void sumset_init(Sumset* s)
{
    for (int i = 0; i < MAX_WORDS; ++i)
        s->sumset[i] = 0;
    s->sumset[0] = 1;
    s->last = 1;
    s->sum = 0;
    s->prev = NULL;
}

// Return whether the sumset A^Σ contains the value x (that is, x is a sum of some subset of A).
static inline bool does_sumset_contain(const Sumset* a, int x)
{
    if (x >= MAX_BITS)
        return false;
    return a->sumset[x / BITS_PER_WORD] & (((Word)1) << (x % BITS_PER_WORD));
}

static inline void _sumset_add(Sumset* result, const Sumset* a, int x);

// Set `*result` to represent (A ∪ {x})^Σ, where `a` represents A^Σ, and `x` is an element added to A.
//
// Also sets result->last=x and result->prev=a (keeping track of added elements, for recovery in with solution_build()).
//
// `*result` does not need to be initialized before calling this.
// `result` can point to the same sumset as `a`.
static inline void sumset_add(Sumset* result, const Sumset* a, int x)
{
    assert(x >= a->last);
    assert(x <= MAX_D);

    result->prev = a;
    result->last = x;

    _sumset_add(result, a, x);
}

// Same as `sumset_add`, but leaves `result->prev` and `result->last` unchanged (they must already be initialized).
// (This is only useful for setting up the initial forced multisets A_0, B_0 in input_data_init/input_data_read).
static inline void _sumset_add(Sumset* result, const Sumset* a, int x) {
    result->sum = a->sum + x;
    assert(result->sum < MAX_BITS);

#ifdef LOG_SUMSET
    pthread_mutex_lock(&_stdout_mutex);
    printf("sumset_add: %d %d; ", x, a->sum);
    for (int i = 0; i <= MAX_BITS; ++i)
        if (does_sumset_contain(a, i))
            printf(" %d", i);
    printf("\n");
    pthread_mutex_unlock(&_stdout_mutex);
#endif

    // The following does:
    //   result->sumset =  a->sumset | (a->sumset << x);
    // over multiple words.

    int s = x / BITS_PER_WORD;
    int r = x % BITS_PER_WORD;

    for (int i = MAX_WORDS - 1; i > s; --i)
        result->sumset[i] = a->sumset[i] | (a->sumset[i - s] << r) | (a->sumset[i - s - 1] >> (BITS_PER_WORD - r));
    result->sumset[s] = a->sumset[s] | a->sumset[0] << r;
    for (int i = s - 1; i >= 0; --i)
        result->sumset[i] = a->sumset[i];
}


// Return |{A^Σ} ∩ {B^Σ}|, the number of distinct values in the intersection of the sumsets A^Σ and B^Σ.
// Note that if this returns 1, then the intersection is {0}.
// If ΣA=ΣB and this returns 2, then the intersection is {0, ΣA}.
static inline size_t get_sumset_intersection_size(const Sumset* a, const Sumset* b)
{
    size_t c = 0;
    for (int i = 0; i < MAX_WORDS; ++i)
        c += __builtin_popcountll(a->sumset[i] & b->sumset[i]);
    return c;
}

// Return whether the intersection of the sumsets A^Σ and B^Σ is trivial (contains only 0).
// This is equivalent to get_sumset_intersection_size(a, b) == 1, but faster.
static inline bool is_sumset_intersection_trivial(const Sumset* a, const Sumset* b)
{
    if ((a->sumset[0] & b->sumset[0]) != 1)
        return false;
    for (int i = 1; i < MAX_WORDS; ++i)
        if (a->sumset[i] & b->sumset[i])
            return false;
    return true;
}