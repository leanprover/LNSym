/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- REV, REV16, REV32

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace DPR

open BitVec

private theorem shiftLeft_ge (x : Nat) (y : Nat) : x ≤ x <<< y := by
  have h₀ : 0 < 2 ^ y := by
    simp only [Nat.zero_lt_two, Nat.pow_pos]
  have h₁ : x ≤ x * 2 ^ y := by
    apply Nat.le_mul_of_pos_right
    simp only [h₀]
  simp only [Nat.mul_one] at h₁
  simp only [Nat.shiftLeft_eq]
  exact h₁

private theorem container_size_le_datasize (opc : Nat) (sf : Nat)
  (h₀ : opc ≥ 0) (h₁ : opc < 4) (h₃ : ¬(opc = 3 ∧ sf = 0)) :
  8 <<< opc ≤ 32 <<< sf := by
  have H1 : 8 = 2 ^ 3 := by decide
  have H2 : 32 = 2 ^ 5 := by decide
  have H3 : 3 + opc ≤ 5 + sf := by omega
  simp only [Nat.shiftLeft_eq, H1, H2, ← Nat.pow_add]
  refine Nat.pow_le_pow_right ?ha H3
  decide

private theorem container_size_dvd_datasize (opc : Nat) (sf : Nat)
  (h₀ : opc ≥ 0) (h₁ : opc < 4) (h₃ : ¬(opc = 3 ∧ sf = 0)):
  (8 <<< opc ∣ 32 <<< sf) := by
  have H1 : 8 = 2 ^ 3 := by decide
  have H2 : 32 = 2 ^ 5 := by decide
  have H3 : 3 + opc ≤ 5 + sf := by omega
  simp only [Nat.shiftLeft_eq, H1, H2, ← Nat.pow_add]
  apply Nat.pow_dvd_pow_iff_le_right'.mpr H3

private theorem opc_and_sf_constraint (x : BitVec 2) (y : BitVec 1)
  (h : ¬(x = 0b11#2 ∧ y = 0b0#1)) :
  ¬(x.toNat = 3 ∧ y.toNat = 0) := by
  revert h
  simp only [BitVec.toNat_eq_nat]
  have h₁ : 3 < 2 ^ 2 := by decide
  simp only [not_and, Nat.reducePow, h₁, true_and, Nat.pow_one, Nat.zero_lt_succ, imp_self]

@[state_simp_rules]
def exec_data_processing_rev
  (inst : Data_processing_one_source_cls) (s : ArmState) : ArmState :=
  let opc : BitVec 2 := extractLsb 1 0 inst.opcode
  if H₁ : opc = 0b11#2 ∧ inst.sf = 0b0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let container_size := 8 <<< opc.toNat
    let operand := read_gpr_zr datasize inst.Rn s
    let esize := 8
    have opc_h₁ : opc.toNat ≥ 0 := by simp only [ge_iff_le, Nat.zero_le]
    have opc_h₂ : opc.toNat < 4 := by
      refine BitVec.isLt (extractLsb 1 0 inst.opcode)
    have opc_sf_h : ¬(opc.toNat = 3 ∧ inst.sf.toNat = 0) := by
      apply opc_and_sf_constraint (extractLsb 1 0 inst.opcode) inst.sf H₁
    have h₀ : 0 < esize := by decide
    have h₁ : esize ≤ container_size := by apply shiftLeft_ge
    have h₂ : container_size ≤ datasize := by
      apply container_size_le_datasize opc.toNat inst.sf.toNat opc_h₁ opc_h₂ opc_sf_h
    have h₃ : esize ∣ container_size := by
      simp only [esize, container_size]
      generalize BitVec.toNat (extractLsb 1 0 inst.opcode) = x
      simp only [Nat.shiftLeft_eq]
      generalize 2 ^ x = n
      simp only [Nat.dvd_mul_right]
    have h₄ : container_size ∣ datasize := by
      apply container_size_dvd_datasize opc.toNat inst.sf.toNat opc_h₁ opc_h₂ opc_sf_h
    let result := rev_vector datasize container_size esize operand h₀ h₁ h₂ h₃ h₄
    -- State Updates
    let s := write_gpr_zr datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

@[state_simp_rules]
def exec_data_processing_one_source
  (inst : Data_processing_one_source_cls) (s : ArmState) : ArmState :=
  match inst.sf, inst.S, inst.opcode2, inst.opcode with
  | 0#1, 0#1, 0b00000#5, 0b000001#6 -- REV16 - 32-bit
  | 0#1, 0#1, 0b00000#5, 0b000010#6 -- REV - 32-bit
  | 1#1, 0#1, 0b00000#5, 0b000001#6 -- REV16 - 64-bit
  | 1#1, 0#1, 0b00000#5, 0b000010#6 -- REV32
  | 1#1, 0#1, 0b00000#5, 0b000011#6 -- REV - 64-bit
    => exec_data_processing_rev inst s
  | _, _, _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

partial def Data_processing_one_source_cls.rev_all.rand : IO (Option (BitVec 32)) := do
  let opc := ← BitVec.rand 2
  let sf := ← BitVec.rand 1
  -- When opc == 0b00#2, inst is instruction RBIT, RBIT is not modeled currently
  if opc == 0b00#2 || opc == 0b11#2 && sf == 0b0#1 then
    Data_processing_one_source_cls.rev_all.rand
  else
    let (inst : Data_processing_one_source_cls) :=
      { sf := sf,
        S := 0b0#1,
        opcode2 := 0b00000#5,
        opcode := 0b0000#4 ++ opc,
        Rn := ← GPRIndex.rand,
        Rd := ← GPRIndex.rand
      }
    pure (some (inst.toBitVec32))

/-- Generate random instructions of Data_processing_one_source_cls class. -/
def Data_processing_one_source_cls.rand : IO (Option (BitVec 32)) :=
  Data_processing_one_source_cls.rev_all.rand

end DPR
