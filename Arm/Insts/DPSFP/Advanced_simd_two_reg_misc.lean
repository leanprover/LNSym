/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- REV64

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open Std.BitVec

theorem Nat_lt_of_2_pow_dvd (x y : Nat) (h : x < y) : 2^x ∣ 2^y := by
  rw [Nat.pow_dvd_pow_iff_le_right]
  exact Nat.le_of_lt h
  simp

theorem Nat_lt_of_le_of_le (x y z : Nat) (h1 : x < y) (h2 : y <= z) : x <= z := by
  refine Nat.le_of_lt ?h
  exact Nat.lt_of_lt_of_le h1 h2

theorem pow2_helper1 (i : Nat) : 8 * 2 ^ i = 2 ^ (3 + i) := by
  have h : 8 = 2^3 := by rfl
  rw [h]
  exact (Nat.pow_add 2 3 i).symm

theorem pow2_helper2 (j : Nat) (h : j <= 6) : 64 / 2 ^ j = 2 ^ (6 - j) := by
  have h0 : 64 = 2^6 := by rfl
  rw [h0]
  refine Nat.pow_div ?h ?hx
  repeat simp_all!

theorem loose_bitvec2_bound (x : BitVec 2) : x.toNat <= 6 := by
  have h : x.toNat < 4 := by exact Fin.isLt ..
  apply Nat_lt_of_le_of_le (Std.BitVec.toNat x) 4 6 <;> trivial

theorem esize_dvd_container_size (x y : BitVec 2) :
  (8 <<< x.toNat < 64 >>> y.toNat) →
  8 <<< x.toNat ∣ 64 >>> y.toNat := by
    simp_all only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, IsUnit.mul_iff]
    generalize h_yvar : Std.BitVec.toNat y = yvar
    have yvar_limit : yvar <= 6 := by
      rw [← h_yvar]; simp [loose_bitvec2_bound]
    simp [pow2_helper1] at *
    rw [pow2_helper2] at *    
    rw [pow_lt_pow_iff_right] <;> simp_all only [Nat_lt_of_2_pow_dvd, implies_true, Nat.lt_succ_self] 
    repeat simp_all only
    done

theorem container_size_dvd_datasize_helper (x : Nat) (_ : x <= 6) :
  2 ^ (6 - x) ∣ (if q = 1#1 then 128 else 64) := by
    have h0 : 6 - x <= 6 := by simp
    have h1 : 2 ^ 6 ∣ 128 := by decide
    have h2 : 2 ^ 6 ∣ 64  := by decide
    split
    exact Nat.pow_dvd_of_le_of_pow_dvd h0 h1
    exact Nat.pow_dvd_of_le_of_pow_dvd h0 h2
    done

theorem container_size_dvd_datasize (x : BitVec 2) (q : BitVec 1) :
  64 >>> x.toNat ∣ (if q = 1#1 then 128 else 64) := by
    simp_all! [Nat.shiftRight_eq_div_pow]
    generalize h_xvar : Std.BitVec.toNat x = xvar at *
    have xvar_limit : xvar <= 6 := by
      rw [← h_xvar]; simp [loose_bitvec2_bound]
    rw [pow2_helper2] at *
    exact container_size_dvd_datasize_helper xvar xvar_limit
    repeat trivial
    done

@[simp]
def exec_advanced_simd_two_reg_misc
  (inst : Advanced_simd_two_reg_misc_cls) (s : ArmState) : ArmState :=
  open Std.BitVec in
  let datasize := if inst.Q == 1#1 then 128 else 64 -- 64 << Uint(inst.Q)
  let esize := 8 <<< inst.size.toNat
  let container_size := 64 >>> ((extractLsb 0 0 inst.opcode) ++ inst.U).toNat
  if h0 : container_size <= esize then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    have h1 : esize ∣ container_size := by
      simp only [not_le] at h0
      exact esize_dvd_container_size inst.size (extractLsb 0 0 inst.opcode ++ inst.U) h0
    have h2 : container_size ∣ datasize := by
      simp_all
      exact container_size_dvd_datasize (extractLsb 0 0 inst.opcode ++ inst.U) inst.Q
    have h3 : 0 < esize := by 
      simp_all only [Nat.sub_zero, Nat.shiftLeft_eq, not_le, IsUnit.mul_iff, beq_iff_eq]
      rw [mul_pos_iff_of_pos_left]
      simp only [gt_iff_lt, zero_lt_two, pow_pos]
      decide
    have h0' : esize <= container_size := by exact Nat.le_of_not_ge h0
    have h4 : container_size <= datasize := by
      refine Nat.le_of_dvd ?h h2; simp [datasize]; split <;> trivial
    let operand := read_sfp datasize inst.Rn s
    let result :=
      match inst.U, inst.opcode with
      | 0#1, 0b00000#5    -- REV64
      | 0#1, 0b00001#5    -- REV16
      | 1#1, 0b00000#5 => -- REV32
        some (rev_vector datasize container_size esize operand
               h3 h0' h4 h1 h2)
      | _, _ => none
    -- State Updates
    match result with
    | none => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
    | some res =>
      let s := write_sfp datasize inst.Rd res s
      let s := write_pc ((read_pc s) + 4#64) s
      s

----------------------------------------------------------------------

partial def Advanced_simd_two_reg_misc_cls.rev64_16.rand : IO (Option (BitVec 32)) := do
  let (inst : Advanced_simd_two_reg_misc_cls) :=
    { Q := ← BitVec.rand 1,
      U := ← pure 0b0#1,
      size := ← BitVec.rand 2,
      opcode := ← BitVec.rand 5 (lo := 0) (hi := 1), -- 0b00000 and 0b00001
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  let esize := 8 <<< inst.size.toNat
  let container_size := 64 >>> ((extractLsb 0 0 inst.opcode) ++ inst.U).toNat
  if container_size <= esize then
    -- Keep generating random instructions until a legal one is encountered.
    Advanced_simd_two_reg_misc_cls.rev64_16.rand
  else
    pure (some (inst.toBitVec32))

partial def Advanced_simd_two_reg_misc_cls.rev32.rand : IO (Option (BitVec 32)) := do
  let (inst : Advanced_simd_two_reg_misc_cls) :=
    { Q := ← BitVec.rand 1,
      U := ← pure 0b1#1,
      size := ← BitVec.rand 2,
      opcode := ← pure 0b00000#5,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  let esize := 8 <<< inst.size.toNat
  let container_size := 64 >>> ((extractLsb 0 0 inst.opcode) ++ inst.U).toNat
  if container_size <= esize then
    -- Keep generating random instructions until a legal one is encountered.
    Advanced_simd_two_reg_misc_cls.rev32.rand
  else
    pure (some (inst.toBitVec32))

/-- Generate random instructions of Advanced_simd_two_reg_misc_cls class. -/
def Advanced_simd_two_reg_misc_cls.rand : List (IO (Option (BitVec 32))) :=
  [Advanced_simd_two_reg_misc_cls.rev64_16.rand,
   Advanced_simd_two_reg_misc_cls.rev32.rand]
