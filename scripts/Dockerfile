# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Yan Peng

FROM ubuntu:22.04
RUN apt-get update
RUN apt-get install -y git cmake clang golang \
  ninja-build lld g++-aarch64-linux-gnu

ENTRYPOINT ["./scripts/build_awslc.sh"]
