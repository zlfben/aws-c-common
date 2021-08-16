/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_from_empty_array_harness() {
    size_t capacity;
    void *array;

    array = malloc(sizeof(*(array)) * (capacity));                                                                        \
    __CPROVER_assume(array != NULL);

    struct aws_byte_buf buf = aws_byte_buf_from_empty_array(array, capacity);
    bool flag = aws_byte_buf_is_valid(&buf);
    assert(flag);
    assert(buf.len == 0);
    assert(buf.capacity == capacity);
    assert(buf.allocator == NULL);
    if (buf.buffer) {
        assert_bytes_match(buf.buffer, array, capacity);
    }
}
