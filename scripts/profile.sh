#!/bin/bash
# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Alex Keizer

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
