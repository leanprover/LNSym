/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Util
import Tactics.Sym

section simple

open BitVec

def eor_program : Program :=
  def_program
  [(0x4005a8#64 , 0xca000000#32)]      --  eor	x0, x0, x0

theorem small_asm_snippet_sym (s0 s_final : ArmState)
  (h_s0_pc : read_pc s0 = 0x4005a8#64)
  (h_s0_program : s0.program = eor_program)
  (h_s0_err : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_run : s_final = run 1 s0) :
  read_gpr 64 0#5 s_final = 0x0#64 ∧
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic Simulation
  sym_n 1
  -- Wrapping up the result:
  unfold run at h_run
  simp_all (config := {decide := true}) only [state_simp_rules, minimal_theory, bitvec_rules]
  bv_decide
  done

end simple
