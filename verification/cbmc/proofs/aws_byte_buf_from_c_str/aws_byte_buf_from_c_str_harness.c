/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

size_t strlen(const char *s)
{
    size_t len=0;
    while(s[len]!=0)
        len++;
    return len;
}

void aws_byte_buf_from_c_str_harness() {
    /* parameter */
    size_t allocated_str_len;
    __CPROVER_assume(allocated_str_len >= 0 && allocated_str_len < UINT32_MAX);
    const char *c_str = malloc(allocated_str_len);
    __CPROVER_assume(c_str == NULL || c_str[allocated_str_len - 1] == '\0');

    size_t str_len = strlen(c_str);

    /* operation under verification */
    struct aws_byte_buf buf = aws_byte_buf_from_c_str(c_str);

    /* assertions */
    bool flag = aws_byte_buf_is_valid(&buf);
    assert(flag);
    assert(buf.allocator == NULL);
    if (buf.buffer) {
        assert(buf.len == str_len);
        assert(buf.capacity == buf.len);
        assert_bytes_match(buf.buffer, (uint8_t *)c_str, buf.len);
    } else {
        if (c_str) {
            assert(str_len == 0);
        }
        assert(buf.len == 0);
        assert(buf.capacity == 0);
    }
}
