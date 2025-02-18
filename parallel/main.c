#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>

#include "common/err.h"
#include "common/io.h"
#include "common/sumset.h"

#define MAX_THREADS 64
#define QUEUE_CAPACITY (MAX_D * MAX_D)
#define STACK_CAPACITY 512

static pthread_mutex_t queue_mutex;
static pthread_cond_t empty_cond;
static pthread_cond_t full_cond;
static pthread_mutexattr_t mutex_attr;
static pthread_mutex_t solution_mutex;

typedef struct Frame Frame;

struct Frame {
    Sumset *a_ptr; // always points to its sumset, except for the initial case
    Sumset a;
    Sumset *b;
    Frame *prev;
    atomic_int dependent;
    atomic_int done;
};

typedef struct {
    atomic_int size;
    Frame *data[QUEUE_CAPACITY];
    int front;
    int back;
    bool started;
    bool ended;
    int wait_cnt;
    int threads;
} Queue;

typedef struct {
    int size;
    Frame *data[STACK_CAPACITY];
} MemStack;

static void sync_init(void) {
    ASSERT_SYS_OK(pthread_mutexattr_init(&mutex_attr));
    ASSERT_SYS_OK(pthread_mutexattr_settype(&mutex_attr, PTHREAD_MUTEX_RECURSIVE));
    ASSERT_SYS_OK(pthread_mutex_init(&queue_mutex, &mutex_attr));
    ASSERT_SYS_OK(pthread_cond_init(&empty_cond, NULL));
    ASSERT_SYS_OK(pthread_cond_init(&full_cond, NULL));
    ASSERT_SYS_OK(pthread_mutex_init(&solution_mutex, &mutex_attr));
}

static void sync_destroy(void) {
    ASSERT_SYS_OK(pthread_cond_destroy(&empty_cond));
    ASSERT_SYS_OK(pthread_cond_destroy(&full_cond));
    ASSERT_SYS_OK(pthread_mutex_destroy(&queue_mutex));
    ASSERT_SYS_OK(pthread_mutex_destroy(&solution_mutex));
    ASSERT_SYS_OK(pthread_mutexattr_destroy(&mutex_attr));
}

static int size(Queue *queue) {
    return atomic_load(&queue->size);
}

static bool empty(Queue *queue) {
    ASSERT_SYS_OK(pthread_mutex_lock(&queue_mutex));
    bool ret = (atomic_load(&queue->size) == 0);
    ASSERT_SYS_OK(pthread_mutex_unlock(&queue_mutex));
    return ret;
}

static void push(Queue *queue, Frame *frame) {
    ASSERT_SYS_OK(pthread_mutex_lock(&queue_mutex));
    while (queue->size == QUEUE_CAPACITY)
        ASSERT_SYS_OK(pthread_cond_wait(&full_cond, &queue_mutex));
    queue->data[queue->back] = frame;
    queue->back = (queue->back + 1) % QUEUE_CAPACITY;
    ++queue->size;
    ASSERT_SYS_OK(pthread_cond_signal(&empty_cond));
    ASSERT_SYS_OK(pthread_mutex_unlock(&queue_mutex));
}

static Frame *pop(Queue *queue) {
    ASSERT_SYS_OK(pthread_mutex_lock(&queue_mutex));
    if (!queue->started) {
        queue->started = true;
    } else if (queue->size == 0 && queue->started && queue->wait_cnt == queue->threads - 1) {
        queue->ended = true;
        queue->size = -1;
        ASSERT_SYS_OK(pthread_cond_broadcast(&empty_cond));
        ASSERT_SYS_OK(pthread_mutex_unlock(&queue_mutex));
        return NULL;
    }
    ++queue->wait_cnt;
    while (queue->size == 0)
        ASSERT_SYS_OK(pthread_cond_wait(&empty_cond, &queue_mutex));
    --queue->wait_cnt;
    if (queue->ended) {
        ASSERT_SYS_OK(pthread_mutex_unlock(&queue_mutex));
        return NULL;
    }
    Frame *ret = queue->data[queue->front];
    queue->front = (queue->front + 1) % QUEUE_CAPACITY;
    --queue->size;
    ASSERT_SYS_OK(pthread_cond_signal(&full_cond));
    ASSERT_SYS_OK(pthread_mutex_unlock(&queue_mutex));
    return ret;
}

static void MS_push(MemStack *stack, Frame *frame) {
    stack->data[stack->size++] = frame;
}

static Frame *MS_pop(MemStack *stack) {
    if (stack->size == 0)
        return NULL;
    return stack->data[--stack->size];
}

static Frame *Frame_acquire(MemStack *stack) {
    Frame *ret = MS_pop(stack);
    if (ret == NULL)
        ret = (Frame*)malloc(sizeof(Frame));
    if (ret == NULL)
        exit(1);
    return ret;
}

static void Frame_release(MemStack *stack, Frame *frame) {
    MS_push(stack, frame);
}

static MemStack mem_stack[MAX_THREADS];

static Queue task_queue;

static bool finished[MAX_THREADS];

typedef struct {
    int id;
} ThreadData;

static InputData input_data;
static Solution best_solution;

static void recursive_reclaim_frames(size_t id, Frame *frame) {
    Frame *tmp = frame;
    int e = atomic_fetch_add(&tmp->done, 1);
    if (e == atomic_load(&tmp->dependent) - 1) {
        MS_push(&mem_stack[id], tmp);
        while (tmp != tmp->prev) {
            e = atomic_fetch_add(&tmp->prev->done, 1);
            if (e != atomic_load(&tmp->prev->dependent) - 1)
                break;
            MS_push(&mem_stack[id], tmp->prev);
            tmp = tmp->prev;
        }
    }
}

static void solve_frame(int id) {
    Frame *frame = pop(&task_queue);
    Sumset *a;
    Sumset *b;
    size_t a_sum, b_sum;
    if (frame == NULL) {
        if (task_queue.ended) {
            finished[id] = true;
            return;
        } else {
            if (input_data.a_start.sum > input_data.b_start.sum) {
                a = &input_data.b_start;
                b = &input_data.a_start;
            } else {
                a = &input_data.a_start;
                b = &input_data.b_start;
            }
        }
    } else {
        a_sum = frame->a_ptr->sum;
        b_sum = frame->b->sum;
        if (a_sum > b_sum) {
            a = frame->b;
            b = frame->a_ptr;
        } else {
            a = frame->a_ptr;
            b = frame->b;
        }
    }

    // at this point a points to the sumset with sum leq than sumset pointed to by b

    if (is_sumset_intersection_trivial(a, b)) {
        int i = (int)(input_data.d - a->last + 1);
        // atomic_fetch_add(&frame->dependent, i);
        if (b == frame->b) {
            atomic_fetch_add(&frame->prev->dependent, i);
        } else {
            atomic_fetch_add(&frame->dependent, i);
        }
        for (size_t i = a->last; i <= input_data.d; ++i) {
            if (!does_sumset_contain(b, i)) {
                Frame *next_frame = Frame_acquire(&mem_stack[id]);
                next_frame->a_ptr = &next_frame->a;
                sumset_add(next_frame->a_ptr, a, i);
                atomic_store(&next_frame->dependent, 1);
                atomic_store(&next_frame->done, 0);
                if (a == frame->a_ptr) { // the previously dominating subset still dominates
                    next_frame->prev = frame->prev;
                    next_frame->b = frame->b;
                } else {
                    next_frame->prev = frame;
                    next_frame->b = frame->a_ptr;
                }
                push(&task_queue, next_frame);
            }
        }
    } else if ((a_sum == b_sum) && get_sumset_intersection_size(a, b) == 2) {
        ASSERT_SYS_OK(pthread_mutex_lock(&solution_mutex));
        if (b_sum > best_solution.sum)
            solution_build(&best_solution, &input_data, a, b);
        ASSERT_SYS_OK(pthread_mutex_unlock(&solution_mutex));
    }
    
    recursive_reclaim_frames(id, frame);
}

static void *helper(void *arg) {
    size_t id = (*((ThreadData*)arg)).id;
    while (!finished[id])
        solve_frame(id);
    while (mem_stack[id].size > 0)
        free(MS_pop(&mem_stack[id]));
    return NULL;
}

static void Queue_init(Queue *queue, int t) {
    queue->back = queue->front = 0;
    queue->size = 0;
    queue->wait_cnt = 0;
    queue->threads = t;
    queue->started = queue->ended = false;
}

static ThreadData thread_data[MAX_THREADS];

static pthread_t thread_desc[MAX_THREADS];

int main() {
    sync_init();
    input_data_read(&input_data);
    solution_init(&best_solution);
    Queue_init(&task_queue, input_data.t);
    Frame *initial_frame = (Frame*)malloc(sizeof(Frame));
    initial_frame->a_ptr = &input_data.a_start;
    initial_frame->b = &input_data.b_start;
    initial_frame->dependent = 1;
    initial_frame->done = 0;
    initial_frame->prev = initial_frame;
    push(&task_queue, initial_frame);
    for (int i = 0; i < input_data.t; ++i) {
        finished[i] = false;
        thread_data[i].id = i;
        mem_stack[i].size = 0;
    }
    for (int i = 1; i < input_data.t; ++i) {
        ASSERT_SYS_OK(pthread_create(&thread_desc[i], NULL, helper, &thread_data[i]));
    }
    helper(&thread_data[0]);
    for (int i = 1; i < input_data.t; ++i) {
        int *result;
        ASSERT_SYS_OK(pthread_join(thread_desc[i], (void**)&result));
    }
    solution_print(&best_solution);
    sync_destroy();
    return 0;
}
