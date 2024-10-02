#!/bin/bash

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
