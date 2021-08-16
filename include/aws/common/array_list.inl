#ifndef AWS_COMMON_ARRAY_LIST_INL
#define AWS_COMMON_ARRAY_LIST_INL

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/* This is implicitly included, but helps with editor highlighting */
#include <aws/common/array_list.h>
/*
 * Do not add system headers here; add them to array_list.h. This file is included under extern "C" guards,
 * which might break system headers.
 */
AWS_EXTERN_C_BEGIN

AWS_STATIC_IMPL
int aws_array_list_init_dynamic(
    struct aws_array_list *AWS_RESTRICT list,
    struct aws_allocator *alloc,
    size_t initial_item_allocation,
    size_t item_size) {

    AWS_FATAL_PRECONDITION(list != NULL);
    AWS_FATAL_PRECONDITION(alloc != NULL);
    AWS_FATAL_PRECONDITION(item_size > 0);

    AWS_ZERO_STRUCT(*list);

    size_t allocation_size;
    if (aws_mul_size_checked(initial_item_allocation, item_size, &allocation_size)) {
        goto error;
    }

    if (allocation_size > 0) {
        list->data = aws_mem_acquire(alloc, allocation_size);
        if (!list->data) {
            goto error;
        }
#ifdef DEBUG_BUILD
        memset(list->data, AWS_ARRAY_LIST_DEBUG_FILL, allocation_size);

#endif
        list->current_size = allocation_size;
    }
    list->item_size = item_size;
    list->alloc = alloc;

    AWS_FATAL_POSTCONDITION(list->current_size == 0 || list->data);
    AWS_POSTCONDITION(aws_array_list_is_valid(list));
    return AWS_OP_SUCCESS;

error:
    AWS_POSTCONDITION(AWS_IS_ZEROED(*list));
    return AWS_OP_ERR;
}

AWS_STATIC_IMPL
void aws_array_list_init_static(
    struct aws_array_list *AWS_RESTRICT list,
    void *raw_array,
    size_t item_count,
    size_t item_size) {

    AWS_FATAL_PRECONDITION(list != NULL);
    AWS_FATAL_PRECONDITION(raw_array != NULL);
    AWS_FATAL_PRECONDITION(item_count > 0);
    AWS_FATAL_PRECONDITION(item_size > 0);

    list->alloc = NULL;

    int no_overflow = !aws_mul_size_checked(item_count, item_size, &list->current_size);
    AWS_FATAL_PRECONDITION(no_overflow);

    list->item_size = item_size;
    list->length = 0;
    list->data = raw_array;
    bool flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
}

AWS_STATIC_IMPL
bool aws_array_list_is_valid(const struct aws_array_list *AWS_RESTRICT list) {
    if (!list) {
        return false;
    }
    size_t required_size = 0;
    bool required_size_is_valid =
        (aws_mul_size_checked(list->length, list->item_size, &required_size) == AWS_OP_SUCCESS);
    bool current_size_is_valid = (list->current_size >= required_size);
    bool data_is_valid = AWS_IMPLIES(list->current_size == 0, list->data == NULL) &&
                         AWS_IMPLIES(list->current_size != 0, AWS_MEM_IS_WRITABLE(list->data, list->current_size));
    bool item_size_is_valid = (list->item_size != 0);
    return required_size_is_valid && current_size_is_valid && data_is_valid && item_size_is_valid;
}

AWS_STATIC_IMPL
void aws_array_list_debug_print(const struct aws_array_list *list) {
    printf(
        "arraylist %p. Alloc %p. current_size %zu. length %zu. item_size %zu. data %p\n",
        (void *)list,
        (void *)list->alloc,
        list->current_size,
        list->length,
        list->item_size,
        (void *)list->data);
}

AWS_STATIC_IMPL
void aws_array_list_clean_up(struct aws_array_list *AWS_RESTRICT list) {
    AWS_PRECONDITION(AWS_IS_ZEROED(*list) || aws_array_list_is_valid(list));
    if (list->alloc && list->data) {
        aws_mem_release(list->alloc, list->data);
    }

    AWS_ZERO_STRUCT(*list);
}

AWS_STATIC_IMPL
void aws_array_list_clean_up_secure(struct aws_array_list *AWS_RESTRICT list) {
    AWS_PRECONDITION(AWS_IS_ZEROED(*list) || aws_array_list_is_valid(list));
    if (list->alloc && list->data) {
        aws_secure_zero((void *)list->data, list->current_size);
        aws_mem_release(list->alloc, list->data);
    }

    AWS_ZERO_STRUCT(*list);
}

AWS_STATIC_IMPL
int aws_array_list_push_back(struct aws_array_list *AWS_RESTRICT list, const void *val) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    AWS_PRECONDITION(
        val && AWS_MEM_IS_READABLE(val, list->item_size),
        "Input pointer [val] must point writable memory of [list->item_size] bytes.");

    int err_code = aws_array_list_set_at(list, val, aws_array_list_length(list));

    if (err_code && aws_last_error() == AWS_ERROR_INVALID_INDEX && !list->alloc) {
        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return aws_raise_error(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE);
    }

    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return err_code;
}

AWS_STATIC_IMPL
int aws_array_list_front(const struct aws_array_list *AWS_RESTRICT list, void *val) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    AWS_PRECONDITION(
        val && AWS_MEM_IS_WRITABLE(val, list->item_size),
        "Input pointer [val] must point writable memory of [list->item_size] bytes.");
    if (aws_array_list_length(list) > 0) {
        memcpy(val, list->data, list->item_size);

        size_t i;
        __CPROVER_assume(i>=0 && i<list->item_size);
        AWS_POSTCONDITION(((const uint8_t *)(val))[i] == ((const uint8_t *)(list->data))[i]);

        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return AWS_OP_SUCCESS;
    }

    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
int aws_array_list_pop_front(struct aws_array_list *AWS_RESTRICT list) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    if (aws_array_list_length(list) > 0) {
        aws_array_list_pop_front_n(list, 1);
        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return AWS_OP_SUCCESS;
    }

    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
void aws_array_list_pop_front_n(struct aws_array_list *AWS_RESTRICT list, size_t n) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    if (n >= aws_array_list_length(list)) {
        aws_array_list_clear(list);
        AWS_POSTCONDITION(flag);
        return;
    }

    if (n > 0) {
        size_t popping_bytes = list->item_size * n;
        size_t remaining_items = aws_array_list_length(list) - n;
        size_t remaining_bytes = remaining_items * list->item_size;
        memmove(list->data, (uint8_t *)list->data + popping_bytes, remaining_bytes);
        list->length = remaining_items;
#ifdef DEBUG_BUILD
        memset((uint8_t *)list->data + remaining_bytes, AWS_ARRAY_LIST_DEBUG_FILL, popping_bytes);
#endif
    }
    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
}

int aws_array_list_erase(struct aws_array_list *AWS_RESTRICT list, size_t index) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);

    const size_t length = aws_array_list_length(list);

    if (index >= length) {
        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return aws_raise_error(AWS_ERROR_INVALID_INDEX);
    }

    if (index == 0) {
        /* Removing front element */
        aws_array_list_pop_front(list);
    } else if (index == (length - 1)) {
        /* Removing back element */
        aws_array_list_pop_back(list);
    } else {
        /* Removing middle element */
        uint8_t *item_ptr = (uint8_t *)list->data + (index * list->item_size);
        uint8_t *next_item_ptr = item_ptr + list->item_size;
        size_t trailing_items = (length - index) - 1;
        size_t trailing_bytes = trailing_items * list->item_size;
        memmove(item_ptr, next_item_ptr, trailing_bytes);

        aws_array_list_pop_back(list);
    }

    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL
int aws_array_list_back(const struct aws_array_list *AWS_RESTRICT list, void *val) {

    bool flag = aws_array_list_is_valid(list);
    assert(flag);

    AWS_PRECONDITION(
        val && AWS_MEM_IS_WRITABLE(val, list->item_size),
        "Input pointer [val] must point writable memory of [list->item_size] bytes.");
    if (aws_array_list_length(list) > 0) {
        size_t last_item_offset = list->item_size * (aws_array_list_length(list) - 1);
        size_t total_length = list->item_size * aws_array_list_length(list);

        memcpy(val, (void *)((uint8_t *)list->data + last_item_offset), list->item_size);

        flag = aws_array_list_is_valid(list);
        assert(flag);

        return AWS_OP_SUCCESS;
    }

    flag = aws_array_list_is_valid(list);
    assert(flag);

    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
int aws_array_list_pop_back(struct aws_array_list *AWS_RESTRICT list) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    if (aws_array_list_length(list) > 0) {

        AWS_FATAL_PRECONDITION(list->data);

        size_t last_item_offset = list->item_size * (aws_array_list_length(list) - 1);

        memset((void *)((uint8_t *)list->data + last_item_offset), 0, list->item_size);
        list->length--;
        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return AWS_OP_SUCCESS;
    }

    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return aws_raise_error(AWS_ERROR_LIST_EMPTY);
}

AWS_STATIC_IMPL
void aws_array_list_clear(struct aws_array_list *AWS_RESTRICT list) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    if (list->data) {
#ifdef DEBUG_BUILD
        memset(list->data, AWS_ARRAY_LIST_DEBUG_FILL, list->current_size);
#endif
        list->length = 0;
    }
    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
}

AWS_STATIC_IMPL
void aws_array_list_swap_contents(
    struct aws_array_list *AWS_RESTRICT list_a,
    struct aws_array_list *AWS_RESTRICT list_b) {
    AWS_FATAL_PRECONDITION(list_a->alloc);
    AWS_FATAL_PRECONDITION(list_a->alloc == list_b->alloc);
    AWS_FATAL_PRECONDITION(list_a->item_size == list_b->item_size);
    AWS_FATAL_PRECONDITION(list_a != list_b);
    bool flag = aws_array_list_is_valid(list_a);
    AWS_PRECONDITION(flag);
    flag = aws_array_list_is_valid(list_b);
    AWS_PRECONDITION(flag);

    struct aws_array_list tmp = *list_a;
    *list_a = *list_b;
    *list_b = tmp;
    flag = aws_array_list_is_valid(list_a);
    AWS_POSTCONDITION(flag);
    flag = aws_array_list_is_valid(list_b);
    AWS_POSTCONDITION(flag);
}

AWS_STATIC_IMPL
size_t aws_array_list_capacity(const struct aws_array_list *AWS_RESTRICT list) {
    AWS_FATAL_PRECONDITION(list->item_size);
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    size_t capacity = list->current_size / list->item_size;
    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return capacity;
}

AWS_STATIC_IMPL
size_t aws_array_list_length(const struct aws_array_list *AWS_RESTRICT list) {
    /*
     * This assert teaches clang-tidy and friends that list->data cannot be null in a non-empty
     * list.
     */
    AWS_FATAL_PRECONDITION(!list->length || list->data);

    size_t len = list->length;

    bool flag = aws_array_list_is_valid(list);
    assert(flag);

    return len;
}

AWS_STATIC_IMPL
int aws_array_list_get_at(const struct aws_array_list *AWS_RESTRICT list, void *val, size_t index) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    AWS_PRECONDITION(
        val && AWS_MEM_IS_WRITABLE(val, list->item_size),
        "Input pointer [val] must point writable memory of [list->item_size] bytes.");
    if (aws_array_list_length(list) > index) {
        memcpy(val, (void *)((uint8_t *)list->data + (list->item_size * index)), list->item_size);
        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return AWS_OP_SUCCESS;
    }
    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}

AWS_STATIC_IMPL
int aws_array_list_get_at_ptr(const struct aws_array_list *AWS_RESTRICT list, void **val, size_t index) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    AWS_PRECONDITION(val != NULL);
    if (aws_array_list_length(list) > index) {
        *val = (void *)((uint8_t *)list->data + (list->item_size * index));
        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return AWS_OP_SUCCESS;
    }
    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return aws_raise_error(AWS_ERROR_INVALID_INDEX);
}

AWS_STATIC_IMPL
int aws_array_list_set_at(struct aws_array_list *AWS_RESTRICT list, const void *val, size_t index) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    AWS_PRECONDITION(
        val && AWS_MEM_IS_READABLE(val, list->item_size),
        "Input pointer [val] must point readable memory of [list->item_size] bytes.");

    if (aws_array_list_ensure_capacity(list, index)) {
        flag = aws_array_list_is_valid(list);
        AWS_POSTCONDITION(flag);
        return AWS_OP_ERR;
    }

    AWS_FATAL_PRECONDITION(list->data);

    memcpy((void *)((uint8_t *)list->data + (list->item_size * index)), val, list->item_size);

    /*
     * This isn't perfect, but its the best I can come up with for detecting
     * length changes.
     */
    if (index >= aws_array_list_length(list)) {
        if (aws_add_size_checked(index, 1, &list->length)) {
            flag = aws_array_list_is_valid(list);
            AWS_POSTCONDITION(flag);
            return AWS_OP_ERR;
        }
    }

    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL
void aws_array_list_sort(struct aws_array_list *AWS_RESTRICT list, aws_array_list_comparator_fn *compare_fn) {
    bool flag = aws_array_list_is_valid(list);
    AWS_PRECONDITION(flag);
    if (list->data) {
        qsort(list->data, aws_array_list_length(list), list->item_size, compare_fn);
    }
    flag = aws_array_list_is_valid(list);
    AWS_POSTCONDITION(flag);
}

AWS_EXTERN_C_END

#endif /*  AWS_COMMON_ARRAY_LIST_INL */
