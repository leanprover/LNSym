/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Util
import Tactics.Sym
import Tactics.StepThms

namespace multi_insts_proofs

open BitVec

def test_program : Program :=
  def_program
  [(0x12650c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
    (0x126510#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
    (0x126514#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
    (0x126518#64 , 0x4ea31c7d#32)]      --  mov     v29.16b, v3.16b

#genStepEqTheorems test_program

theorem small_asm_snippet_sym_experiment_1 (s0 s_final : ArmState)
  (h_s0_pc : read_pc s0 = 0x12650c#64)
  (h_s0_program : s0.program = test_program)
  (h_s0_err : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_run : s_final = run 4 s0) :
  read_sfp 128 26#5 s_final = read_sfp 128 0#5 s0 ∧
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic Simulation
  sym_n 4
  done

/-
-- set_option profiler true in
-- set_option profiler.threshold 10 in
theorem small_asm_snippet_sym_experiment_1 (s0 s_final : ArmState)
  (h_s0_pc : read_pc s0 = 0x12650c#64)
  (h_s0_program : s0.program = test_program)
  (h_s0_err : read_err s0 = StateError.None)
  (h_run : s_final = run 4 s0) :
  read_sfp 128 26#5 s_final = read_sfp 128 0#5 s0 ∧
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic Simulation
  sym_i_n 0 4
  have h_s4_unchanged_final :
    ∀ (f : StateField), f ≠ StateField.PC ∧
                        f ≠ StateField.SFP 29#5 ∧
                        f ≠ StateField.SFP 28#5 ∧
                        f ≠ StateField.SFP 27#5 ∧
                        f ≠ StateField.SFP 26#5
                        →
                        r f s4 = r f s0 := by
    clear h_s1_changed h_s2_changed h_s3_changed h_s4_changed
    clear h_run h_s4_err h_s4_pc h_s4_program
    simp_all only [minimal_theory]
  have h_s4_changed_final :
    r StateField.PC s4 = 1205532#64 ∧
    r (StateField.SFP 29#5) s4 = zeroExtend 128 (r (StateField.SFP 3#5) s0) ∧
    r (StateField.SFP 28#5) s4 = zeroExtend 128 (r (StateField.SFP 2#5) s0) ∧
    r (StateField.SFP 27#5) s4 = zeroExtend 128 (r (StateField.SFP 1#5) s0) ∧
    r (StateField.SFP 26#5) s4 = zeroExtend 128 (r (StateField.SFP 0#5) s0) := by
      clear h_run h_s4_err h_s4_pc h_s4_program
      simp (config := {decide := true}) only
          [@zeroExtend_eq 128,
            h_s4_changed, h_s3_changed, h_s2_changed, h_s1_changed,
            h_s4_unchanged, h_s3_unchanged, h_s2_unchanged, h_s1_unchanged,
            minimal_theory]
      done
  clear h_s1_changed h_s2_changed h_s3_changed h_s4_changed
  clear h_s4_unchanged h_s3_unchanged h_s2_unchanged h_s1_unchanged
  -- Final Steps
  unfold run at h_run
  subst s_final
  simp only [@zeroExtend_eq 128, h_s4_err, h_s4_changed_final, minimal_theory]
  done
-/

end multi_insts_proofs
