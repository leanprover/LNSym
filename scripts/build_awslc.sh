#!/bin/bash

# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Yan Peng

set -e
set -o xtrace

# Remember where LNSym is
LNSym_DIR=${PWD}

# Fetching AWS-LC
git clone https://github.com/aws/aws-lc.git $HOME/aws-lc --depth 1
cd $HOME/aws-lc

docker build -t ubuntu-22.04-aarch:base -f tests/ci/docker_images/linux-aarch/ubuntu-22.04_base/Dockerfile tests/ci/docker_images/dependencies
docker build -t  ubuntu-22.04-gcc-12x tests/ci/docker_images/linux-aarch/ubuntu-22.04_gcc-12x/
docker run -v `pwd`:`pwd` -w `pwd` ubuntu-22.04-gcc-12x bash -c 'rm -rf build && mkdir -p build && cd build && cmake ../  -DCMAKE_BUILD_TYPE=RelWithDebInfo -DKEEP_ASM_LOCAL_SYMBOLS=1 && make -j4 crypto_test'
file build/crypto/crypto_test

# Move crypto_test to LNSym
cp -f build/crypto/crypto_test ${LNSym_DIR}/Tests/ELFParser/Data/crypto_test

