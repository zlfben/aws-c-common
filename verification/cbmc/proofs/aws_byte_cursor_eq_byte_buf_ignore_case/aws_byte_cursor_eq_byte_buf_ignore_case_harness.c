/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_cursor_eq_byte_buf_ignore_case_harness() {
    /* parameters */
    struct aws_byte_cursor cur;
    struct aws_byte_buf buf;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, UINT32_MAX));
    // ensure_byte_cursor_has_allocated_buffer_member(&cur);
    cur.ptr = malloc(cur.len);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, UINT32_MAX));
    // ensure_byte_buf_has_allocated_buffer_member(&buf);
    buf.allocator = (nondet_bool()) ? NULL : aws_default_allocator();
    buf.buffer = malloc(sizeof(*(buf.buffer)) * buf.capacity);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the data structure */
    struct aws_byte_cursor old_cur = cur;
    struct store_byte_from_buffer old_byte_from_cur;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cur);
    struct aws_byte_buf old_buf = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    /* operation under verification */
    if (aws_byte_cursor_eq_byte_buf_ignore_case(&cur, &buf)) {
        assert(cur.len == buf.len);
    }

    /* assertions */
    bool flag = aws_byte_cursor_is_valid(&cur);
    assert(flag);
    flag = aws_byte_buf_is_valid(&buf);
    assert(flag);
    if (cur.len > 0) {
        assert_byte_from_buffer_matches(cur.ptr, &old_byte_from_cur);
    }
    assert_byte_buf_equivalence(&buf, &old_buf, &old_byte_from_buf);
}
