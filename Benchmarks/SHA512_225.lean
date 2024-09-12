/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Sym
import Benchmarks.SHA512

set_option trace.Tactic.sym.heartbeats true in
theorem Benchmarks.sha512_225_instructions : SHA512Bench 225 := by
  unfold SHA512Bench
  intros
  sym_n 225
  done
