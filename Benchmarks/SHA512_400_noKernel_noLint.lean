/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Sym
import Benchmarks.Command
import Benchmarks.SHA512

open Benchmarks

disable_linters in
set_option debug.skipKernelTC true in
benchmark sha512_400_noKernel_noLint : SHA512Bench 400 := fun s0 _ h => by
  intros
  sym_n 400
  simp (config := {failIfUnchanged := false}) only [h, bitvec_rules]
  all_goals exact (sorry : Aligned ..)
  done
