/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_clean_up_harness() {
    struct aws_byte_buf buf;

    buf.allocator = (nondet_bool()) ? NULL : aws_default_allocator();
    buf.buffer = malloc(sizeof(*(buf.buffer)) * buf.capacity);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    aws_byte_buf_clean_up(&buf);
    assert(buf.allocator == NULL);
    assert(buf.buffer == NULL);
    assert(buf.len == 0);
    assert(buf.capacity == 0);
}
