#pragma once
#include "common/sumset.h"

typedef struct Multiset {
    int count[MAX_D + 1]; // count[i] represents the number of i in the multiset.
} Multiset;

// Initialize a multiset to represent an empty multiset.
void multiset_init(Multiset* v);

// A structure for representing the input data.
typedef struct InputData {
    Multiset a_in, b_in;  // Direct representations of the input multisets A_0, B_0.
    Sumset a_start, b_start;  // Representation of the corresponding initial sumsets A_0^Σ, B_0^Σ.
    int t; // Number of threads that can be used.
    int d; // Maximum element allowed in the multisets.
} InputData;


// Initialize input_data and read the task input (t, d, n, m, A_0, B_0) from stdin into it.
// The resulting sumsets a_start and b_start have prev=NULL and last=1.
void input_data_read(InputData* input_data);

// Initialize all structures in the InputData structure with multisets containing given elements.
// Useful for debugging, when we don't want to provide input on stdin.
// The elements must be given as arrays of integers, terminated with 0.
// E.g.: `input_data_init(&input_data, 8, 10, (int[]){0}, (int[]){1, 1, 0});`
void input_data_init(InputData* input_data, int t, int d, int a_elements[], int b_elements[]);

// A structure for representing a solution.
typedef struct Solution {
    int sum;
    Multiset a, b;
} Solution;

// Initialize a solution to represent an empty solution (sum 0, two empty multisets).
void solution_init(Solution* s);

// Build the solution from Sumsets a and b and the input data.
// It's OK if the given Sumsets are swapped.
//
// `last` values are not used for recovery (homework solutions may change them).
//
// Technical explanation:
// The solution is built by first recovering the added elements from Sumset-s:,
// following their `prev` pointers, computing the added element as `a->sum - a->prev->sum`,
// and repeating until prev is NULL.
// We compare the final sumset with input_data->a_start and input_data->b_start by value.
// This allows to determine which multiset was built from A_0 and which from B_0.
// (We can't have A_0^Σ = B_0^Σ unless A_0,B_0 have non-trivial common subset sums or A_0=B_0).
void solution_build(Solution* s, InputData* input_data, const Sumset* a, const Sumset* b);

// Prints the solution to stdout as required.
void solution_print(const Solution* s);
