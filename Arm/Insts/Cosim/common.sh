#!/usr/bin/env bash
# Collect path manipulation for scripting used to drive cosimulator.
# Author: Siddharth Bhat

OUTFILE="$1" # basename for the output file
GITDIR="$(git rev-parse --show-toplevel)"
COSIMDIR="${GITDIR}/Arm/Insts/Cosim"
