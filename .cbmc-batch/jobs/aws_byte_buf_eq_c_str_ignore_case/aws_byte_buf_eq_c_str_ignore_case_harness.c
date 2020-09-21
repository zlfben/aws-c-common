/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

size_t str_len;

size_t strlen(const char *s)
{
    size_t len=0;
    while(s[len]!=0) len++;
    return len;
}

void aws_byte_buf_eq_c_str_ignore_case_harness() {
    /* parameters */
    struct aws_byte_buf buf;

    char *c_str;
    size_t allocated_str_len;
    __CPROVER_assume(allocated_str_len > 0);
    c_str = bounded_malloc(allocated_str_len); // c*c*l* shape
    if (allocated_str_len)
        __CPROVER_assume(c_str[allocated_str_len-1] == 0);

    /* assumptions */
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the parameters */
    struct aws_byte_buf old = buf;
    struct store_byte_from_buffer old_byte;
    save_byte_from_array(buf.buffer, buf.len, &old_byte);
    str_len = (c_str) ? strlen(c_str) : 0;
    struct store_byte_from_buffer old_byte_from_str;
    save_byte_from_array((uint8_t *)c_str, str_len, &old_byte_from_str);

    /* operation under verification */
    if (aws_byte_buf_eq_c_str_ignore_case(&buf, c_str)) {
        assert(buf.len == str_len);
    }

    /* asserts both parameters remain unchanged */
    assert(AWS_BYTE_BUF_IS_VALID(&buf));
    assert_byte_buf_equivalence(&buf, &old, &old_byte);
    if (str_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)c_str, &old_byte_from_str);
    }
}
