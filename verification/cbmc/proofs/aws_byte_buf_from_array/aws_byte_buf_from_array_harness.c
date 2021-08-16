/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_from_array_harness() {
    /* parameters */
    size_t length;
    uint8_t *array;

    /* assumptions. */
    array = malloc(sizeof(*(array)) * (length));                                                                        \
    __CPROVER_assume(array != NULL);
    
    /* operation under verification */
    struct aws_byte_buf buf = aws_byte_buf_from_array(array, length);

    /* assertions */
    bool flag = aws_byte_buf_is_valid(&buf);
    assert(flag);
    assert(buf.len == length);
    assert(buf.capacity == length);
    assert(buf.allocator == NULL);
    if (buf.buffer) {
        assert_bytes_match(buf.buffer, array, buf.len);
    }
}
