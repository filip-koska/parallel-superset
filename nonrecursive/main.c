#include <stddef.h>
#include <stdio.h>

#include "common/io.h"
#include "common/sumset.h"

#define STACK_CAPACITY 512

typedef struct {
    Sumset a;
    Sumset const* b;
    bool poppable;
} StackElem;

typedef struct {
    size_t size;
    StackElem data[STACK_CAPACITY];
} Stack;

static void clear(Stack *stack) {
        stack->size = 0;
}

static size_t size(Stack const* stack) {
    return stack->size;
}

static bool empty(Stack const* stack) {
    return (stack->size == 0);
}

static StackElem *top(Stack * stack) {
    if (empty(stack))
        return NULL;
    return &(stack->data[stack->size - 1]);
}

static void push(Stack *stack, Sumset const* a, Sumset const* b, size_t i) {
    ++stack->size;
    top(stack)->poppable = false;
    top(stack)->b = b;
    sumset_add(&(top(stack)->a), a, i);
}

static void pop(Stack *stack) {
    if (!empty(stack))
        --stack->size;
}

static InputData input_data;
static Solution best_solution;
static Stack recursion_stack;

static bool started = false;

static uint64_t frame_cnt = 0;

static void solve(void) {

   Sumset const* a;
   Sumset const* b;

   while (!empty(&recursion_stack) || !started) {
    ++frame_cnt;

        if (!started) {
            started = true;
            if (input_data.a_start.sum > input_data.b_start.sum) {
                a = &input_data.b_start;
                b = &input_data.a_start;
            } else {
                a = &input_data.a_start;
                b = &input_data.b_start;
            }
        } else {
            StackElem *tmp = top(&recursion_stack);
            tmp->poppable = true;
            if (tmp->a.sum > tmp->b->sum) {
                a = tmp->b;
                b = &tmp->a;
            } else {
                a = &tmp->a;
                b = tmp->b;
            }
        }
        
        if (is_sumset_intersection_trivial(a, b)) {
            for (size_t i = a->last; i <= input_data.d; ++i) {
                if (!does_sumset_contain(b, i))
                    push(&recursion_stack, a, b, i);
            }
        } else if ((a->sum == b->sum) && get_sumset_intersection_size(a, b) == 2) {
            if (b->sum > best_solution.sum)
                solution_build(&best_solution, &input_data, a, b);
        }
        while (!empty(&recursion_stack) && top(&recursion_stack)->poppable)
            pop(&recursion_stack);
   }
}

int main() {
    input_data_read(&input_data);
    // input_data_init(&input_data, 8, 10, (int[]){0}, (int[]){1, 0});

    solution_init(&best_solution);
    solve();
    solution_print(&best_solution);
    printf("frame_cnt: %lu\n", frame_cnt);

}