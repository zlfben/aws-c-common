/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

size_t str_len;

void aws_byte_cursor_eq_c_str_harness() {
    /* parameters */
    struct aws_byte_cursor cur;
    char *c_str;
    size_t allocated_str_len;

    __CPROVER_assume(allocated_str_len > 0);
    c_str = bounded_malloc(allocated_str_len); // c*c*l* shape
    if (allocated_str_len)
        __CPROVER_assume(c_str[allocated_str_len-1] == 0);

    /* assumptions */
    // __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(AWS_BYTE_CURSOR_IS_VALID(&cur));

    /* save current state of the parameters */
    struct aws_byte_cursor old = cur;
    struct store_byte_from_buffer old_byte_from_cursor;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cursor);
    str_len = (c_str) ? strlen(c_str) : 0;
    struct store_byte_from_buffer old_byte_from_str;
    save_byte_from_array((uint8_t *)c_str, str_len, &old_byte_from_str);

    /* operation under verification */
    if (aws_byte_cursor_eq_c_str(&cur, c_str)) {
        assert(cur.len == str_len);
        if (cur.len > 0) {
            assert_bytes_match(cur.ptr, (uint8_t *)c_str, cur.len);
        }
    }

    /* asserts both parameters remain unchanged */
    assert(AWS_BYTE_CURSOR_IS_VALID(&cur));
    if (cur.len > 0) {
        assert_byte_from_buffer_matches(cur.ptr, &old_byte_from_cursor);
    }
    if (str_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)c_str, &old_byte_from_str);
    }
}
