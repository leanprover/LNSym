/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Sym
import Benchmarks.SHA512

set_option linter.unusedVariables false in
set_option trace.Tactic.sym.heartbeats true in
#time theorem Benchmarks.sha512_400_instructions : SHA512Bench 400 := by
  unfold SHA512Bench
  intros
  sym_n 400
  done
