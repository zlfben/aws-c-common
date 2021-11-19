#!/bin/bash

# whether verify the program or not
CHECK=true
USE_VIEWER=false

# paths to the benchmark repos
AWS_C_COMMON_PATH="../../.."
SRC_DIR=$AWS_C_COMMON_PATH

# executables
MAKE="make"
GOTO_INSTRUMENT="goto-instrument"
CBMC="cbmc"
KISSAT="kissat"
VIEWER="cbmc-viewer"

CBMC_FLAGS=""

# benchmark name + number of concrete indices
AWS_C_COMMON_TESTS=(
    # "aws_array_eq"
    # "aws_array_eq_c_str"
    # "aws_array_eq_c_str_ignore_case"
    # "aws_array_eq_ignore_case"
    # "aws_array_list_back"
    # "aws_array_list_capacity"
    # "aws_array_list_clear"
    # "aws_array_list_copy"
    # "aws_array_list_ensure_capacity"
    # "aws_array_list_erase"
    # "aws_array_list_front"
    # "aws_array_list_get_at"
    # "aws_array_list_get_at_ptr"
    # "aws_array_list_init_static"
    # "aws_array_list_length"
    # "aws_array_list_pop_back"
    # "aws_array_list_pop_front"
    # "aws_array_list_pop_front_n"
    # "aws_array_list_push_back"
    # "aws_array_list_set_at"
    # "aws_array_list_shrink_to_fit"
    # "aws_array_list_sort"
    # "aws_array_list_swap_contents"
    # "aws_byte_buf_advance"
    # "aws_byte_buf_append"
    # "aws_byte_buf_append_dynamic"
    # "aws_byte_buf_append_with_lookup"
    # "aws_byte_buf_clean_up"
    # "aws_byte_buf_clean_up_secure"
    # "aws_byte_buf_eq"
    # "aws_byte_buf_eq_c_str"
    "aws_byte_buf_eq_c_str_ignore_case"
    # "aws_byte_buf_eq_ignore_case"
    # "aws_byte_buf_from_array"
    # "aws_byte_buf_from_c_str"
    # "aws_byte_buf_from_empty_array"
    # "aws_byte_buf_init"
    # "aws_byte_buf_init_copy"
    # "aws_byte_buf_init_copy_from_cursor"
    # "aws_byte_buf_reset"
    # "aws_byte_buf_secure_zero"
    # "aws_byte_cursor_advance"
    # "aws_byte_cursor_advance_nospec"
    # "aws_byte_cursor_eq"
    # "aws_byte_cursor_eq_byte_buf"
    # "aws_byte_cursor_eq_byte_buf_ignore_case"
    # "aws_byte_cursor_eq_c_str"
    # "aws_byte_cursor_eq_c_str_ignore_case"
    # "aws_byte_cursor_eq_ignore_case"
    # "aws_byte_cursor_from_array"
    # "aws_byte_cursor_from_buf"
    # "aws_byte_cursor_from_c_str"
    # "aws_byte_cursor_from_string"
    # "aws_byte_cursor_read"
    # "aws_byte_cursor_read_and_fill_buffer"
)

cwd=$(realpath $(pwd))
for test in "${AWS_C_COMMON_TESTS[@]}"; do
    echo "===== $test ====="
    cd $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test
    proof_fold=$(realpath $(pwd))
    # compile program into goto-programs
    $MAKE veryclean > /dev/null 2>&1
    rm .ninja_deps
    $MAKE goto > /dev/null 2>&1
    echo "Goto programs built"
    cd $cwd
    # run goto-instrument to make abstracted goto-programs
    $GOTO_INSTRUMENT --use-rra $cwd/specifications/$test.json \
        $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.goto \
        $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.abst.goto

    # print the goto-programs into txts
    $GOTO_INSTRUMENT --show-goto-functions \
        $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.abst.goto \
        >> $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.abst.goto.txt

    # check the program
    if [ $CHECK = true ]; then
        time $CBMC $CBMC_FLAGS --external-sat-solver $KISSAT --xml-ui \
            $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.abst.goto
    fi

    # use viewer
    if [ $USE_VIEWER = true ]; then
        $CBMC $CBMC_FLAGS --cover location --xml-ui \
            $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.abst.goto \
            > $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/$test/coverage.xml
        $CBMC $CBMC_FLAGS --show-properties --xml-ui \
            $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.abst.goto \
            > $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/$test/property.xml
        $CBMC $CBMC_FLAGS --external-sat-solver $KISSAT --xml-ui \
            $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/$test/${test}_harness.c.abst.goto \
            > $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/result.xml
        
        $VIEWER \
            --coverage $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/coverage.xml \
            --goto $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/${test}_harness.c.abst.goto \
            --reportdir $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/html \
            --property $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/property.xml \
            --result $AWS_C_COMMON_PATH/verification/cbmc/proofs/$test/gotos$proof_fold/result.xml \
            --srcdir $SRC_DIR
    fi

done
