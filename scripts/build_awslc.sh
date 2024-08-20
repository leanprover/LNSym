#!/bin/sh

# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Yan Peng

# Remember where LNSym is
LNSym_DIR = ${PWD}

# Install dependencies
brew install ninja

# Fetching and building AWS-LC
git clone https://github.com/aws/aws-lc.git $HOME/aws-lc
cd $HOME/aws-lc; mkdir aws-lc-build; cd aws-lc-build
cmake -GNinja -DKEEP_ASM_LOCAL_SYMBOLS=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo ../../aws-lc
ninja

# Move crypto_test to LNSym
cp -f crypto/crypto_test ${LNSym_DIR}/Tests/ELFParser/Data/crypto_test

cd ${LNSym_DIR}
