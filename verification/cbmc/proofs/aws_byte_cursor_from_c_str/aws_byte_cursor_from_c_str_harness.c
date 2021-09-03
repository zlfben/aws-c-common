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

void aws_byte_cursor_from_c_str_harness() {
    /* parameters */
    const char *c_str;
    size_t allocated_str_len;
    __CPROVER_assume(allocated_str_len <= UINT32_MAX);
    __CPROVER_assume(allocated_str_len>0);
    c_str = malloc(allocated_str_len); // c*c*l* shape
    if (allocated_str_len)
        __CPROVER_assume(c_str[allocated_str_len-1] == 0);
    size_t str_len = strlen(c_str);

    /* operation under verification */
    struct aws_byte_cursor cur = aws_byte_cursor_from_c_str(c_str);

    /* assertions */
    bool flag = aws_byte_cursor_is_valid(&cur);
    assert(flag);
    if (cur.ptr) { /* if ptr is NULL len shoud be 0, otherwise equal to c_str */
        size_t cur_len = cur.len;
        assert(cur.len == str_len);
        assert_bytes_match(cur.ptr, (uint8_t *)c_str, cur.len);
    } else {
        assert(cur.len == 0);
    }
}
