#include "common/io.h"
#include "common/err.h"

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>

void multiset_init(Multiset* v)
{
    for (int i = 0; i < MAX_D; i++)
        v->count[i] = 0;
}

// Add all elements of multiset b into a.
static void multiset_add(Multiset* a, const Multiset* b)
{
    for (int i = 0; i <= MAX_D; i++)
        a->count[i] += b->count[i];
}

// Read n elements from stdin, recording them in a Multiset and the corresponding Sumset.
// The resulting sumset has prev=NULL and last=1.
static void read_multiset(int n, Multiset* v, Sumset* s)
{
    multiset_init(v);
    sumset_init(s);
    for (int i = 0; i < n; i++) {
        int x;
        if (scanf("%d", &x) != 1)
            fatal("scanf");
        v->count[x]++;
        _sumset_add(s, s, x);
    }
}

void input_data_init(InputData* input_data, int t, int d, int a_elements[], int b_elements[])
{
    input_data->t = t;
    input_data->d = d;
    multiset_init(&input_data->a_in);
    multiset_init(&input_data->b_in);
    sumset_init(&input_data->a_start);
    sumset_init(&input_data->b_start);
    for (int i = 0; a_elements[i] != 0; i++) {
        input_data->a_in.count[a_elements[i]]++;
        _sumset_add(&input_data->a_start, &input_data->a_start, a_elements[i]);
    }
    for (int i = 0; b_elements[i] != 0; i++) {
        input_data->b_in.count[b_elements[i]]++;
        _sumset_add(&input_data->b_start, &input_data->b_start, b_elements[i]);
    }
}


void input_data_read(InputData* input_data)
{
    int t, d, n, m;
    if (scanf("%d%d%d%d", &t, &d, &n, &m) != 4)
        fatal("scanf");
    assert((3 <= d) && (d <= MAX_D));
    assert((0 <= n) && (0 <= m));
    input_data->t = t;
    input_data->d = d;
    read_multiset(n, &input_data->a_in, &input_data->a_start);
    read_multiset(m, &input_data->b_in, &input_data->b_start);
}

void solution_init(Solution* s)
{
    s->sum = 0;
    multiset_init(&s->a);
    multiset_init(&s->b);
}

// Recover a multiset of added elements from its sumset, using prev pointers.
// Returns: the inital sumset, before any elements were added.
// Note that the resulting multiset does not contain initial elements (A_0), only the added ones.
static const Sumset* _multiset_of_added_elements_from_sumset(Multiset* v, const Sumset* a)
{
    multiset_init(v);
    while (a->prev) {
        v->count[a->sum - a->prev->sum]++;
        a = a->prev;
    }
    return a;
}

static void _multiset_swap(Multiset* a, Multiset* b)
{
    Multiset tmp = *a;
    *a = *b;
    *b = tmp;
}

// Compares the sumsets by value (A^Σ=B^Σ), ignoring last and prev pointers.
static bool _sumset_eq(const Sumset* a, const Sumset* b)
{
    if (a == b)
        return true;
    if (a->sum != b->sum)
        return false;
    for (int i = 0; i < MAX_WORDS; i++) {
        if (a->sumset[i] != b->sumset[i])
            return false;
    }
    return true;
}

void solution_build(Solution* s, InputData* input_data, const Sumset* a, const Sumset* b)
{
    s->sum = a->sum;
    const Sumset* start_a = _multiset_of_added_elements_from_sumset(&s->a, a);
    const Sumset* start_b = _multiset_of_added_elements_from_sumset(&s->b, b);
    (void) start_b;  // Avoid unused variable warning.

    if (_sumset_eq(start_a, &input_data->a_start)) {
        multiset_add(&s->a, &input_data->a_in);
        assert(_sumset_eq(start_b, &input_data->b_start));
        multiset_add(&s->b, &input_data->b_in);
    } else {
        assert(_sumset_eq(start_a, &input_data->b_start));
        assert(_sumset_eq(start_b, &input_data->a_start));
        multiset_add(&s->a, &input_data->b_in);
        multiset_add(&s->b, &input_data->a_in);
        _multiset_swap(&s->a, &s->b);
    }
}

// Print a multiset, like: "2x1 3\n" for {1, 1, 3}.
static void multiset_print(const Multiset* v)
{
    bool first = true;
    for (int i = 0; i < MAX_D; i++) {
        if (v->count[i]) {
            if (first)
                first = false;
            else
                printf(" ");
            if (v->count[i] > 1)
                printf("%dx", v->count[i]);
            printf("%d", i);
        }
    }
    printf("\n");
}

void solution_print(const Solution* s)
{
    printf("%d\n", s->sum);
    multiset_print(&s->a);
    multiset_print(&s->b);
}