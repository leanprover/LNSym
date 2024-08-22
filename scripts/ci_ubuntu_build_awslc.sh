#!/bin/bash

# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Yan Peng

set -e
set -o xtrace

docker build -f ./scripts/Dockerfile -t build-awslc .
docker run -v `pwd`:`pwd` -w `pwd` build-awslc
