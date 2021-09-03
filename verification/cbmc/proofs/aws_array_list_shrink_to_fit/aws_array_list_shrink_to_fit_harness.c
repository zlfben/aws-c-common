/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>
/**
 * Runtime: 13s
 */
void aws_array_list_shrink_to_fit_harness() {
    /* data structure */
    struct aws_array_list list;
    __CPROVER_assume(list.current_size < UINT32_MAX);
    
    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    list.data = malloc(list.current_size);
    list.alloc = nondet_bool() ? NULL : aws_default_allocator();
    __CPROVER_assume(aws_array_list_is_valid(&list));
    __CPROVER_assume(list.current_size <= UINT32_MAX);

    /* remove some elements before shrinking the data structure */
    size_t n;
    aws_array_list_pop_front_n(&list, n);

    size_t remaining_size = list.current_size;

    /* save current state of the data structure */
    struct aws_array_list old = list;
    struct store_byte_from_buffer old_byte;
    save_byte_from_array((uint8_t *)list.data, list.current_size, &old_byte);

    /* perform operation under verification and assertions */
    if (!aws_array_list_shrink_to_fit(&list)) {
        assert(
            (list.current_size == 0 && list.data == NULL) ||
            (list.data != NULL && list.current_size == list.length * list.item_size));
    } else {
        /* In the case aws_array_list_shrink_to_fit is not successful, the list must not change */
        assert_array_list_equivalence(&list, &old, &old_byte);
    }
    bool flag = aws_array_list_is_valid(&list);
    assert(flag);
}
