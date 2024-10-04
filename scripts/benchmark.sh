#!/bin/bash

LAKE=lake
BENCH="$LAKE env lean -Dweak.benchmark.runs=5"
OUT="data/benchmarks"

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
    $BENCH $file | tee "$out/$base"
done
