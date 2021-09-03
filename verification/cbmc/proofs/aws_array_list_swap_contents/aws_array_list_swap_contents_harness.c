/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 7s
 */
void aws_array_list_swap_contents_harness() {
    /* data structure */
    struct aws_array_list from;
    struct aws_array_list to;
    __CPROVER_assume(from.current_size < UINT32_MAX);
    __CPROVER_assume(to.current_size < UINT32_MAX);

    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&from, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    from.data = malloc(from.current_size);
    from.alloc = nondet_bool() ? NULL : aws_default_allocator();
    __CPROVER_assume(aws_array_list_is_valid(&from));

    __CPROVER_assume(aws_array_list_is_bounded(&to, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    to.data = malloc(to.current_size);
    to.alloc = nondet_bool() ? NULL : aws_default_allocator();
    __CPROVER_assume(aws_array_list_is_valid(&to));

    __CPROVER_assume(from.alloc != NULL);
    __CPROVER_assume(to.alloc != NULL);

    __CPROVER_assume(from.item_size > 0);
    __CPROVER_assume(to.item_size > 0);
    __CPROVER_assume(from.item_size == to.item_size);

    /* save current state of the data structure */
    struct aws_array_list old_from = from;
    struct store_byte_from_buffer old_byte_from;
    save_byte_from_array((uint8_t *)from.data, from.current_size, &old_byte_from);

    struct aws_array_list old_to = to;
    struct store_byte_from_buffer old_byte_to;
    save_byte_from_array((uint8_t *)to.data, to.current_size, &old_byte_to);

    /* perform operation under verification */
    aws_array_list_swap_contents(&from, &to);

    /* assertions */
    bool flag = aws_array_list_is_valid(&from);
    assert(flag);
    flag = aws_array_list_is_valid(&to);
    assert(flag);
    assert_array_list_equivalence(&from, &old_to, &old_byte_to);
    assert_array_list_equivalence(&to, &old_from, &old_byte_from);
}
