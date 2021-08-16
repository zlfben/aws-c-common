/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_advance_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    struct aws_byte_buf output;
    size_t len;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, UINT32_MAX));
    buf.allocator = (nondet_bool()) ? NULL : aws_default_allocator();
    buf.buffer = malloc(sizeof(*(buf.buffer)) * buf.capacity);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));
    if (nondet_bool()) {
        output = buf;
    } else {
        __CPROVER_assume(aws_byte_buf_is_bounded(&output, UINT32_MAX));
        output.allocator = (nondet_bool()) ? NULL : aws_default_allocator();
        output.buffer = malloc(sizeof(*(output.buffer)) * output.capacity);
        __CPROVER_assume(aws_byte_buf_is_valid(&output));
    }

    /* save current state of the parameters */
    struct aws_byte_buf old = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    /* operation under verification */
    if (aws_byte_buf_advance(&buf, &output, len)) {
        assert(buf.len == old.len + len);
        assert(buf.capacity == old.capacity);
        assert(buf.allocator == old.allocator);
        if (old.len > 0) {
            assert_byte_from_buffer_matches(buf.buffer, &old_byte_from_buf);
        }
        assert(output.len == 0);
        assert(output.capacity == len);
        assert(output.allocator == NULL);
    } else {
        assert_byte_buf_equivalence(&buf, &old, &old_byte_from_buf);
        assert(output.len == 0);
        assert(output.capacity == 0);
        assert(output.allocator == NULL);
        assert(output.buffer == NULL);
    }
    bool flag = aws_byte_buf_is_valid(&buf);
    assert(flag);
    flag = aws_byte_buf_is_valid(&output);
    assert(flag);
}
