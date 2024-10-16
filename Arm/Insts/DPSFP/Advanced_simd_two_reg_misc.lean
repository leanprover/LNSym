/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- REV64/32/16

import Arm.Decode
import Arm.State
import Arm.Insts.Common
import Arm.BitVec
import Arm.Insts.CosimM

----------------------------------------------------------------------

namespace DPSFP

open BitVec

theorem Nat_lt_of_2_pow_dvd (x y : Nat) (h : x < y) : 2^x ∣ 2^y := by
  rw [Nat.pow_dvd_pow_iff_le_right]
  exact Nat.le_of_lt h
  simp

theorem Nat_lt_of_le_of_le (x y z : Nat) (h1 : x < y) (h2 : y <= z) : x <= z := by
  refine Nat.le_of_lt ?h
  exact Nat.lt_of_lt_of_le h1 h2

theorem pow2_helper1 (i : Nat) : 8 * 2 ^ i = 2 ^ (3 + i) := by
  have h : 8 = 2^3 := rfl
  rw [h]
  exact (Nat.pow_add 2 3 i).symm

theorem pow2_helper2 (j : Nat) (h : j <= 6) : 64 / 2 ^ j = 2 ^ (6 - j) := by
  have h0 : 64 = 2^6 := rfl
  rw [h0]
  refine Nat.pow_div ?h ?hx
  repeat simp_all!

theorem loose_bitvec2_bound (x : BitVec 2) : x.toNat <= 6 := by
  have h : x.toNat < 4 := by exact Fin.isLt ..
  apply Nat_lt_of_le_of_le (BitVec.toNat x) 4 6 <;> trivial

theorem esize_dvd_container_size (x y : BitVec 2) :
  (8 <<< x.toNat < 64 >>> y.toNat) →
  8 <<< x.toNat ∣ 64 >>> y.toNat := by
    simp_all only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    generalize h_yvar : BitVec.toNat y = yvar
    have yvar_limit : yvar <= 6 := by
      rw [← h_yvar]; simp [loose_bitvec2_bound]
    simp [pow2_helper1] at *
    rw [pow2_helper2] at *
    rw [Nat.pow_lt_pow_iff_right] <;> simp_all only [Nat_lt_of_2_pow_dvd, implies_true, Nat.lt_succ_self]
    repeat simp_all only
    done

theorem container_size_dvd_datasize_helper (x : Nat) (_ : x <= 6) :
  2 ^ (6 - x) ∣ (if q = 1#1 then 128 else 64) := by
    have h0 : 6 - x <= 6 := by omega
    have h1 : 2 ^ 6 ∣ 128 := by decide
    have h2 : 2 ^ 6 ∣ 64  := by decide
    split
    exact Nat.pow_dvd_of_le_of_pow_dvd h0 h1
    exact Nat.pow_dvd_of_le_of_pow_dvd h0 h2
    done

theorem container_size_dvd_datasize (x : BitVec 2) (q : BitVec 1) :
  64 >>> x.toNat ∣ (if q = 1#1 then 128 else 64) := by
    simp_all! [Nat.shiftRight_eq_div_pow]
    generalize h_xvar : BitVec.toNat x = xvar at *
    have xvar_limit : xvar <= 6 := by
      rw [← h_xvar]; simp [loose_bitvec2_bound]
    rw [pow2_helper2] at *
    exact container_size_dvd_datasize_helper xvar xvar_limit
    repeat trivial
    done

/--
Vector instruction `REV64` that reverses the order of 1-byte elements in each
64-bit slice of the 128-bit input.

Ref.:
https://developer.arm.com/documentation/ddi0602/2024-06/SIMD-FP-Instructions/REV64--Reverse-elements-in-64-bit-doublew
-/
def vrev128_64_8 (x : BitVec 128) : BitVec 128 :=
  rev_vector 128 64 8 x
    (by decide) (by decide) (by decide)
    (by decide) (by decide)

@[state_simp_rules]
def exec_advanced_simd_two_reg_misc
  (inst : Advanced_simd_two_reg_misc_cls) (s : ArmState) : ArmState :=
  open BitVec in
  let datasize := if inst.Q = 1#1 then 128 else 64 -- 64 << Uint(inst.Q)
  let esize := 8 <<< inst.size.toNat
  let container_size := 64 >>> ((lsb inst.opcode 0) ++ inst.U).toNat
  if h0 : container_size <= esize then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    have h1 : esize ∣ container_size := by
      simp only [Nat.not_le] at h0
      exact esize_dvd_container_size inst.size (lsb inst.opcode 0 ++ inst.U) h0
    have h2 : container_size ∣ datasize := by
      simp_all [datasize]
      exact container_size_dvd_datasize (lsb inst.opcode 0 ++ inst.U) inst.Q
    have h3 : 0 < esize := by
      simp_all only [Nat.sub_zero, Nat.shiftLeft_eq, Nat.not_le, beq_iff_eq, esize]
      rw [Nat.mul_pos_iff_of_pos_left]
      simp only [gt_iff_lt, Nat.zero_lt_two, Nat.pow_pos]
      decide
    have h0' : esize <= container_size := by exact Nat.le_of_not_ge h0
    have h4 : container_size <= datasize := by
      refine Nat.le_of_dvd ?h h2; simp [datasize]; split <;> trivial
    let operand := read_sfp datasize inst.Rn s
    let result : Option (BitVec datasize) :=
      -- (FIXME) Define wrappers around `rev_vector` (like
      -- `vrev128_64_8`) to see cleaner terms during proofs.
        match inst.U, inst.opcode with
      | 0#1, 0b00000#5 => -- REV64
        if h_vrev128_64_8 : datasize = 128 ∧ container_size = 64 ∧ esize = 8 then
            have h_datasize : datasize = 128 := by simp_all only
            some ((vrev128_64_8 (operand.cast h_datasize)).cast h_datasize.symm)
          else
            some (rev_vector datasize container_size esize operand
                  h3 h0' h4 h1 h2)
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

partial def Advanced_simd_two_reg_misc_cls.rev64_16.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let (inst : Advanced_simd_two_reg_misc_cls) :=
    { Q := ← BitVec.rand 1,
      U := ← pure 0b0#1,
      size := ← BitVec.rand 2,
      opcode := ← BitVec.rand 5 (lo := 0) (hi := 1), -- 0b00000 and 0b00001
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  let esize := 8 <<< inst.size.toNat
  let container_size := 64 >>> ((lsb inst.opcode 0) ++ inst.U).toNat
  if container_size <= esize then
    -- Keep generating random instructions until a legal one is encountered.
    Advanced_simd_two_reg_misc_cls.rev64_16.rand
  else
    pure (some (inst.toBitVec32))

partial def Advanced_simd_two_reg_misc_cls.rev32.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let (inst : Advanced_simd_two_reg_misc_cls) :=
    { Q := ← BitVec.rand 1,
      U := ← pure 0b1#1,
      size := ← BitVec.rand 2,
      opcode := ← pure 0b00000#5,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  let esize := 8 <<< inst.size.toNat
  let container_size := 64 >>> ((lsb inst.opcode 0) ++ inst.U).toNat
  if container_size <= esize then
    -- Keep generating random instructions until a legal one is encountered.
    Advanced_simd_two_reg_misc_cls.rev32.rand
  else
    pure (some (inst.toBitVec32))

/-- Generate random instructions of Advanced_simd_two_reg_misc_cls class. -/
def Advanced_simd_two_reg_misc_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [Advanced_simd_two_reg_misc_cls.rev64_16.rand,
   Advanced_simd_two_reg_misc_cls.rev32.rand]
