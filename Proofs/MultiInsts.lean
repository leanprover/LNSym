/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Tactics.Sym
import Auto

section multi_insts_proofs

open Std.BitVec

set_option auto.smt true
set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true
-- set_option trace.auto.smt.result true
-- set_option auto.proofReconstruction false

def test_program : program :=
  def_program
  #[(0x12650c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
    (0x126510#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
    (0x126514#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
    (0x126518#64 , 0x4ea31c7d#32)]      --  mov     v29.16b, v3.16b

theorem one_asm_snippet_sym_helper1 (q0_var : BitVec 128) :
  zeroExtend 128 (zeroExtend 128 (zeroExtend 128 q0_var ||| zeroExtend 128 q0_var)) = zeroExtend 128 q0_var := by
  auto

theorem one_asm_snippet_sym_helper2 (q0_var : BitVec 128) :
  q0_var ||| q0_var = q0_var := by auto

-- Todo: use sym_n to prove this theorem.
theorem small_asm_snippet_sym (s : ArmState)
  (h_pc : read_pc s = 0x12650c#64)
  (h_program : s.program = test_program.find?)
  (h_s_ok : read_err s = StateError.None)
  (h_s' : s' = run 4 s) :
  read_sfp 128 26#5 s' = read_sfp 128 0#5 s ∧
  read_err s' = StateError.None := by
    -- iterate 4 (sym1 [h_program])
    sym1 [h_program]
    sym1 [h_program]
    sym1 [h_program]
    sym1 [h_program]
    -- Wrapping up the result:
    -- generalize (r (StateField.SFP 0#5) s) = q0_var; unfold state_value at q0_var; simp at q0_var
    -- try (simp [one_asm_snippet_sym_helper1])
    simp only [one_asm_snippet_sym_helper2]
    done

end multi_insts_proofs
