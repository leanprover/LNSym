# LNSym: Native Code Symbolic Simulator in Lean
[![Makefile CI](https://github.com/leanprover/LNSym/actions/workflows/makefile.yml/badge.svg)](https://github.com/leanprover/LNSym/actions/workflows/makefile.yml)

LNSym is a symbolic simulator for Armv8 machine-code programs.

Please see the [LICENSE](./LICENSE) file for LNSym's licensing and
[CONTRIBUTING.md](./CONTRIBUTING.md) for external contribution
guidelines.

## Prerequisites

Install Lean4 and your preferred editor's plug-in on your machine by
following [these
instructions](https://leanprover-community.github.io/get_started.html).

## Build Instructions

Run `make` at the top-level of LNSym to fetch the Lean4 dependencies,
build this library (including the proofs), and run conformance
testing. Note that if you are not on an Aarch64 machine, conformance
testing will be skipped.

The default `make` command corresponds to the following invocation:

```make all VERBOSE=--verbose NUM_TESTS=20```

### Other Makefile targets

`clean`: remove build outputs.

`clean_all`: `clean` plus remove Lean dependencies.

`specs`: [run under `all`] builds only the specifications of
native-code programs of interest.

`proofs`: [run under `all`] builds only the proofs.

`tests`: [run under `all`] builds concrete tests.

`cosim`: [run under `all`] perform conformance testing.

`awslc_elf`: perform ELF loading tests for AWS-LC.

`benchmarks`: run benchmarks for the symbolic simulator.

`profiler`: run a single round of each benchmark, with the profiler enabled

### Makefile variables that can be passed in at the command line

`VERBOSE`: Verbose mode; prints disassembly of the instructions being
 tested. Default: on.

`NUM_TESTS`: Number of random tests/instruction class. Default: 20.

## Directory Overview

- `Arm`: Formalization of the Armv8 Aarch64 ISA
- `Specs`: Specifications of algorithms of interest
- `Proofs`: Proofs of Arm native-code programs
- `Tests`: Concrete tests of Arm native-code programs
