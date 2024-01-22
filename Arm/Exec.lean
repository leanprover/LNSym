/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.BitVec
import Arm.Memory
import Arm.Decode
import Arm.Insts

def exec_inst (ai : ArmInst) (s : ArmState) : ArmState :=
  open ArmInst in
  match ai with
  | DPI (DataProcImmInst.Add_sub_imm i) =>
    DPI.exec_add_sub_imm i s
  | DPI (DataProcImmInst.PC_rel_addressing i) =>
    DPI.exec_pc_rel_addressing i s
  | DPI (DataProcImmInst.Logical_imm i) =>
    DPI.exec_logical_imm i s

  | BR (BranchInst.Compare_branch i) =>
    BR.exec_compare_branch i s
  | BR (BranchInst.Uncond_branch_imm i) =>
    BR.exec_uncond_branch_imm i s
  | BR (BranchInst.Uncond_branch_reg i) =>
    BR.exec_uncond_branch_reg i s

  | DPR (DataProcRegInst.Add_sub_carry i) =>
    DPR.exec_add_sub_carry i s
  | DPR (DataProcRegInst.Conditional_select i) =>
    DPR.exec_conditional_select i s
  | DPR (DataProcRegInst.Logical_shifted_reg i) =>
    DPR.exec_logical_shifted_reg i s

  | DPSFP (DataProcSFPInst.Crypto_two_reg_sha512 i) =>
    DPSFP.exec_crypto_two_reg_sha512 i s
  | DPSFP (DataProcSFPInst.Crypto_three_reg_sha512 i) =>
    DPSFP.exec_crypto_three_reg_sha512 i s
  | DPSFP (DataProcSFPInst.Advanced_simd_two_reg_misc i) =>
    DPSFP.exec_advanced_simd_two_reg_misc i s
  | DPSFP (DataProcSFPInst.Advanced_simd_extract i) =>
    DPSFP.exec_advanced_simd_extract i s
  | DPSFP (DataProcSFPInst.Advanced_simd_three_same i) =>
    DPSFP.exec_advanced_simd_three_same i s

  | LDST (LDSTInst.Reg_imm_post_indexed i) =>
    LDST.exec_reg_imm_post_indexed i s
  | LDST (LDSTInst.Reg_unsigned_imm i) =>
    LDST.exec_reg_unsigned_imm i s
  | LDST (LDSTInst.Reg_pair_pre_indexed i) =>
    LDST.exec_reg_pair_pre_indexed i s
  | LDST (LDSTInst.Advanced_simd_multiple_struct i) =>
    LDST.exec_advanced_simd_multiple_struct i s
  | LDST (LDSTInst.Advanced_simd_multiple_struct_post_indexed i) =>
    LDST.exec_advanced_simd_multiple_struct_post_indexed i s

  | _ =>
    write_err
      (StateError.Unimplemented s!"Unsupported ArmInst {ai} encountered in exec_inst!") s


def stepi (s : ArmState) : ArmState :=
  -- This function should be simulated away automatically because the
  -- the program will always be concrete. Even the PC can be symbolic,
  -- as long as we can establish that it points to some instruction in
  -- the program.
  let err := read_err s
  match err with
  -- We take a step only if the starting state is error-free.
  | StateError.None =>
    (let pc := read_pc s
     let raw_inst := fetch_inst pc s
     match raw_inst with
      | none =>
        write_err (StateError.NotFound s!"No instruction found at PC {pc}!") s
      | some i =>
        let eai := decode_raw_inst i
        match eai with
          | none =>
            write_err (StateError.Unimplemented s!"Could not decode instruction {i} at PC {pc}!") s
          | some arm_inst => exec_inst arm_inst s)
  | _ => s

def run (n : Nat) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 =>
    let s' := stepi s
    run n' s'

@[simp]
theorem run_opener_zero (s : ArmState) :
  run 0 s = s := by
  rfl

theorem run_opener_general
  (n : Nat) (s : ArmState) :
  run (n + 1) s = run n (stepi s) := by
  conv =>
    lhs
    unfold run
    simp

theorem run_plus (n1 : Nat) (n2 : Nat) (s : ArmState) :
  run (n1 + n2) s = run n2 (run n1 s) := by
  induction n1 generalizing s with
  | zero => simp
  | succ n n_ih =>
    simp [run_opener_general]
    conv =>
      lhs
      pattern (Nat.succ n + n2)
      apply Nat.succ_add
    conv =>
      lhs
      unfold run
    simp
    exact n_ih (stepi s)
