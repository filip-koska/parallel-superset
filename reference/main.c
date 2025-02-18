#include <stddef.h>

#include "common/io.h"
#include "common/sumset.h"

static InputData input_data;

static Solution best_solution;

static void solve(const Sumset* a, const Sumset* b)
{
    if (a->sum > b->sum)
        return solve(b, a);

    if (is_sumset_intersection_trivial(a, b)) { // s(a) ∩ s(b) = {0}.
        for (size_t i = a->last; i <= input_data.d; ++i) {
            if (!does_sumset_contain(b, i)) {
                Sumset a_with_i;
                sumset_add(&a_with_i, a, i);
                solve(&a_with_i, b);
            }
        }
    } else if ((a->sum == b->sum) && (get_sumset_intersection_size(a, b) == 2)) { // s(a) ∩ s(b) = {0, ∑b}.
        if (b->sum > best_solution.sum)
            solution_build(&best_solution, &input_data, a, b);
    }
}

int main()
{
    input_data_read(&input_data);
    // input_data_init(&input_data, 8, 10, (int[]){0}, (int[]){1, 0});

    solution_init(&best_solution);
    solve(&input_data.a_start, &input_data.b_start);
    solution_print(&best_solution);
    return 0;
}
