/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_init_copy_from_cursor_harness() {
    /* data structure */
    struct aws_byte_buf buf;

    /* parameters */
    struct aws_allocator *allocator;
    struct aws_byte_cursor cursor;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cursor, UINT32_MAX));
    // ensure_byte_cursor_has_allocated_buffer_member(&cursor);
    cursor.ptr = malloc(cursor.len);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cursor));

    ASSUME_DEFAULT_ALLOCATOR(allocator);

    if (aws_byte_buf_init_copy_from_cursor(&buf, allocator, cursor) == AWS_OP_SUCCESS) {
        uint8_t *buf_buf = buf.buffer;
        /* assertions */
        bool flag = aws_byte_buf_is_valid(&buf);
        assert(flag);
        flag = aws_byte_cursor_is_valid(&cursor);
        assert(flag);
        assert(buf.len == cursor.len);
        assert(buf.capacity == cursor.len);
        assert(buf.allocator == allocator);
        if (buf.buffer) {
            assert_bytes_match(buf.buffer, cursor.ptr, buf.len);
        }
    }
}
