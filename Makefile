# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Shilpi Goel

SHELL := /bin/bash

LAKE = lake
LEAN = $(LAKE) env lean
GIT = git

NUM_TESTS?=3
VERBOSE?=--verbose

.PHONY: all
all: specs correctness proofs tests cosim
# Note that we don't include benchmarks in `all`,
# to avoid slowing down CI too much

.PHONY: specs
	time -p $(LAKE) build Specs

.PHONY: correctness
correctness:
	time -p $(LAKE) build Correctness

.PHONY: proofs
proofs:
	time -p $(LAKE) build Proofs

.PHONY: tests
tests:
	time -p $(LAKE) build Tests

.PHONY: awslc_elf
awslc_elf:
	./scripts/ci_ubuntu_build_awslc.sh; time -p $(LAKE) build AWSLCELFTests

.PHONY: cosim
cosim:
	time -p lake exe lnsym $(VERBOSE) --num-tests $(NUM_TESTS)

BENCHMARKS = \
	Benchmarks/SHA512_50.lean \
	Benchmarks/SHA512_50_noKernel_noLint.lean \
	Benchmarks/SHA512_75.lean \
	Benchmarks/SHA512_75_noKernel_noLint.lean \
	Benchmarks/SHA512_150.lean \
	Benchmarks/SHA512_150_noKernel_noLint.lean \
	Benchmarks/SHA512_225.lean \
	Benchmarks/SHA512_225_noKernel_noLint.lean \
	Benchmarks/SHA512_400.lean \
	Benchmarks/SHA512_400_noKernel_noLint.lean

.PHONY: benchmarks
benchmarks:
	./scripts/benchmark.sh $(BENCHMARKS)

.PHONY: profile
profile:
	./scripts/profile.sh $(BENCHMARKS)

.PHONY: clean clean_all
clean:
	$(LAKE) clean

clean_all: clean
# The lake-packages directory existed at v4.3.0-rc1, but since at
# least v4.5.0-rc1, the build outputs go in the .lake directory.
	rm -rf lake-packages
	rm -rf .lake
	rm -rf lakefile.olean
