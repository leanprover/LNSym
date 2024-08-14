# Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Shilpi Goel

#!/bin/sh

GITDIR="$(git rev-parse --show-toplevel)"
COSIMDIR="${GITDIR}/Arm/Insts/Cosim"
INFILE=$1

if [ -e "${COSIMDIR}/tests/${INFILE}.o" ]; then

    # Disassemble cosim run <i>.
    base_cmd="objdump -d ${COSIMDIR}/tests/${INFILE}.o"

    # Get 1 line (i.e., 1 instruction) after a "modinst" match.  Given
    # the layout of instance.S, this will always be the instruction
    # under test.
    raw_inst="grep -A 1 \"modinst\" | tail -n 1"

    # Do not print the address -- just the instruction bytes and its
    # corresponding disassembly.
    snip_inst="awk '{\$2=\"\"; print}'"

    cmd=$base_cmd" | "$raw_inst" | "$snip_inst

    eval $cmd
    exit 0

else

    echo "Error: binary instance.o does not exist!"
    exit 1
fi
