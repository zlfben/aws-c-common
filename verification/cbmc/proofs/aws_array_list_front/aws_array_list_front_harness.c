/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 6s
 */
void aws_array_list_front_harness() {
    /* data structure */
    struct aws_array_list list;

    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    size_t item_size = list.item_size;

    list.data = malloc(list.current_size);
    list.alloc = nondet_bool() ? NULL : aws_default_allocator();
    __CPROVER_assume(aws_array_list_is_valid(&list));
    void *val = malloc(list.item_size);

    /* save current state of the data structure */
    struct aws_array_list old = list;
    struct store_byte_from_buffer old_byte;
    save_byte_from_array((uint8_t *)list.data, list.current_size, &old_byte);

    /* assume preconditions */
    __CPROVER_assume(aws_array_list_is_valid(&list));
    __CPROVER_assume(val && AWS_MEM_IS_WRITABLE(val, list.item_size));

    /* perform operation under verification */
    if (!aws_array_list_front(&list, val)) {
        /* In the case aws_array_list_front is successful, we can ensure the list isn't empty */

        size_t i;
        __CPROVER_assume(i>=0 && i<list.item_size);
        AWS_POSTCONDITION(((const uint8_t *)(val))[i] == ((const uint8_t *)(list.data))[i]);

        assert(list.data);
        assert(list.length);
    }

    /* assertions */
    bool flag = aws_array_list_is_valid(&list);
    assert(flag);
    assert_array_list_equivalence(&list, &old, &old_byte);
}
