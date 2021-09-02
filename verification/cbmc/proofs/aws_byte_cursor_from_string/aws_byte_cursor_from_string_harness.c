/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_byte_cursor_from_string_harness() {
    // struct aws_string *str = nondet_allocate_string_bounded_length(UINT32_MAX);
    size_t len;
    __CPROVER_assume(len < UINT32_MAX);
    struct aws_string *str = malloc(sizeof(struct aws_string) + len + 1);
    if (str != NULL) {
        *(struct aws_allocator **)(&str->allocator) = nondet_bool() ? aws_default_allocator() : NULL;
        *(size_t *)(&str->len) = len;
        *(uint8_t *)&str->bytes[len] = '\0';
    }

    __CPROVER_assume(aws_string_is_valid(str));
    struct aws_byte_cursor cursor = aws_byte_cursor_from_string(str);
    bool flag = aws_string_is_valid(str);
    assert(flag);
    flag = aws_byte_cursor_is_valid(&cursor);
    assert(flag);
    assert(cursor.len == str->len);
    assert(cursor.ptr == str->bytes);
    assert_bytes_match(str->bytes, cursor.ptr, str->len);
}
