#!/bin/bash

# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Yan Peng

set -e
set -o xtrace

# Remember where LNSym is
LNSym_DIR=${PWD}

MICRO_ARCH="neoverse-n1"
TARGET="aarch64-unknown-linux-gnu"
export LDFLAGS="-fuse-ld=lld"

# Install dependencies
sudo apt-get update
sudo apt-get install -y git cmake clang ninja-build lld g++-aarch64-linux-gnu

# Fetching AWS-LC
git clone https://github.com/aws/aws-lc.git $HOME/aws-lc --depth 1
cd $HOME/aws-lc
# Build AWS-LC
mkdir aws-lc-build; cd aws-lc-build
cmake -GNinja \
      -DCMAKE_BUILD_TYPE=RelWithDebInfo \
      -DKEEP_ASM_LOCAL_SYMBOLS=1 \
      -DCMAKE_TOOLCHAIN_FILE="${LNSym_DIR}/scripts/build_awslc.cmake" \
      -DCMAKE_C_FLAGS="-mcpu=${MICRO_ARCH}" \
      -DCMAKE_CXX_FLAGS="-mcpu=${MICRO_ARCH}" \
      -DCMAKE_ASM_FLAGS="-mcpu=${MICRO_ARCH}" \
      -DCMAKE_C_COMPILER_TARGET=$TARGET \
      -DCMAKE_CXX_COMPILER_TARGET=$TARGET \
      -DCMAKE_ASM_COMPILER_TARGET=$TARGET \
      ../
ninja

# Move crypto_test to LNSym
cp -rf ../aws-lc-build ${LNSym_DIR}/Tests/ELFParser/Data/aws-lc-build
