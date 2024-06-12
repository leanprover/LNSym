/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Util
import Tactics.Sym

section multi_insts_proofs

open BitVec

def test_program : Program :=
  def_program
  [(0x12650c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
    (0x126510#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
    (0x126514#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
    (0x126518#64 , 0x4ea31c7d#32)]      --  mov     v29.16b, v3.16b

theorem small_asm_snippet_sym (s0 s_final : ArmState)
  (h_s0_pc : read_pc s0 = 0x12650c#64)
  (h_s0_program : s0.program = test_program)
  (h_s0_ok : read_err s0 = StateError.None)
  (h_run : s_final = run 4 s0) :
  read_sfp 128 26#5 s_final = read_sfp 128 0#5 s0 ∧
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic Simulation
  sym_n 4 h_s0_program
  -- Wrapping up the result:
  unfold run at h_run
  subst s_final s_4
  simp_all (config := {decide := true}) only [state_simp_rules, minimal_theory, bitvec_rules]
  rw [@zeroExtend_eq 128]
  done

end multi_insts_proofs
