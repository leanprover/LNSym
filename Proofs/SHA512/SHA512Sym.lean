/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Util
import Tactics.Sym
import Proofs.SHA512.SHA512StepLemmas
import Lean
open BitVec

namespace SHA512

-- set_option debug.skipKernelTC true in
-- set_option profiler true in
-- set_option profiler.threshold 1 in
-- set_option pp.deepTerms false in
theorem sha512_block_armv8_test_4_sym (s0 s_final : ArmState)
  (h_s0_err : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_s0_pc : read_pc s0 = 0x1264c4#64)
  (h_s0_program : s0.program = program)
  (h_run : s_final = run 11 s0) :
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic Simulation
  sym_n 11
  try (clear h_step_1 h_step_2 h_step_3 h_step_4;
       clear h_step_5 h_step_6 h_step_7 h_step_8;
       clear h_step_9 h_step_10 h_step_11)
  -- Final Steps
  unfold run at h_run
  subst s_final
  rw [h_s11_err]
  done

/-
  -- sym_n 1
  -- let s0_x31 := (r (StateField.GPR 31#5) s0)
  -- simp only [state_value] at s0_x31
  -- have h_s0_x31 : s0_x31 = (r (StateField.GPR 31#5) s0) := by rfl
  -- simp (config := {ground := true}) only [← h_s0_x31] at h_step_1
  -- clear h_s0_x31
-/

end SHA512
