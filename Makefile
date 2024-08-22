# Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Shilpi Goel

SHELL := /bin/bash

LAKE = lake

NUM_TESTS?=3
VERBOSE?=--verbose

.PHONY: all 
all: specs correctness proofs tests cosim

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
	time -p $(LAKE) build AWSLCELFTests

.PHONY: cosim
cosim:
	time -p lake exe lnsym $(VERBOSE) --num-tests $(NUM_TESTS)

.PHONY: clean clean_all
clean: 
	$(LAKE) clean

clean_all: clean
# The lake-packages directory existed at v4.3.0-rc1, but since at
# least v4.5.0-rc1, the build outputs go in the .lake directory.
	rm -rf lake-packages
	rm -rf .lake
	rm -rf lakefile.olean
