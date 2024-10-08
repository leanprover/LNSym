#!/bin/bash
# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Alex Keizer

# Helper script to get profiling data
# USAGE:
#   ./profile.sh Benchmark/file1.lean Benchmark/file2.lean ...
#
# The script will first build the `Benchmarks` target, which builds the
# dependencies but does not run the benchmarks themselves, and then
# invokes lean directly on each of the files passed as arguments, with
# - the `profiler` option set to true
# - the `trace.profiler.output` option set to
#     `data/profiles/[timestamp]_[commit hash]/[filename].json`, and
# - the stdout of the build logged in
#     `data/profiles/[timestamp]_[commit hash]/[filename].log`
#
# NOTE: if you pass a file which is not part of the Benchmarks target, then
#       you *have* to make sure its dependencies are built before invoking this
#       script

LAKE=lake
PROF="$LAKE env lean -Dprofiler=true"
OUT="data/profiles"

timestamp=$(date +"%Y-%m-%d_%H%M%S")
rev=$(git rev-parse --short HEAD)
echo "HEAD is on $rev"
out="$OUT/${timestamp}_${rev}"
mkdir -p "$out"

$LAKE build Benchmarks
for file in "$@"; do
    echo
    echo + $file
    echo
    base="$(basename "$file" ".lean")"
    $PROF -Dtrace.profiler.output="$out/$base.json" "$file" | tee "$base.log"
done
