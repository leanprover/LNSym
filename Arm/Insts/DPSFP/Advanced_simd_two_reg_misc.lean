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

/-- Reverse the order of `esize`-bit elements in `x`.-/
def rev_elems (n esize : Nat) (x : BitVec n) (h₀ : esize ∣ n) (h₁ : 0 < esize) : BitVec n :=
  if h0 : n <= esize then
    x
  else
    let element := Std.BitVec.zeroExtend esize x
    let rest_x := Std.BitVec.zeroExtend (n - esize) (x >>> esize)
    have h1 : esize <= n := by
      simp at h0; exact Nat.le_of_lt h0; done
    have h2 : esize ∣ (n - esize) := by
      refine Nat.dvd_sub ?H h₀ ?h₂
      · exact h1
      · simp only [Nat.dvd_refl]
      done
    have ?term_lemma : n - esize < n := by exact Nat.sub_lt_self h₁ h1
    let rest_ans := rev_elems (n - esize) esize rest_x h2 h₁
    have h3 : (esize + (n - esize)) = n := by
      simp_all only [ge_iff_le, Nat.add_sub_cancel', h1]
    h3 ▸ (element ++ rest_ans)
   termination_by n

example : rev_elems 4 4 0xA#4 (by decide) (by decide) = 0xA#4 := rfl
example : rev_elems 8 4 0xAB#8 (by decide) (by decide) = 0xBA#8 := rfl
example : rev_elems 8 4 (rev_elems 8 4 0xAB#8 (by decide) (by decide))
          (by decide) (by decide) = 0xAB#8 := by native_decide

theorem rev_elems_base :
  rev_elems esize esize x h₀ h₁ = x := by
  unfold rev_elems; simp; done

/-- Divide a bv of width `datasize` into containers, each of size
`container_size`, and within a container, reverse the order of `esize`-bit
elements. -/
def rev_vector (datasize container_size esize : Nat) (x : BitVec datasize)
  (h₀ : 0 < esize) (h₁ : esize <= container_size) (h₂ : container_size <= datasize)
  (h₃ : esize ∣ container_size) (h₄ : container_size ∣ datasize) :
  BitVec datasize :=
  if h0 : datasize = container_size then
    h0 ▸ (rev_elems container_size esize (h0 ▸ x) h₃ h₀)
  else
    let container := Std.BitVec.zeroExtend container_size x
    let new_container := rev_elems container_size esize container h₃ h₀
    let new_datasize := datasize - container_size
    let rest_x := Std.BitVec.zeroExtend new_datasize (x >>> container_size)
    have h₄' : container_size ∣ new_datasize := by
      have h : container_size ∣ container_size := Nat.dvd_refl _
      exact Nat.dvd_sub h₂ h₄ h
    have h₂' : container_size <= new_datasize := by
      refine Nat.le_of_dvd ?h h₄'
      omega
    have h1 : 0 < container_size := by exact Nat.lt_of_lt_of_le h₀ h₁
    have ?term_lemma : new_datasize < datasize := by exact Nat.sub_lt_self h1 h₂
    let rest_ans := rev_vector new_datasize container_size esize rest_x h₀ h₁ h₂' h₃ h₄'
    have h2 : new_datasize + container_size = datasize := by
        rw [Nat.sub_add_cancel h₂]
    h2 ▸ (rest_ans ++ new_container)
  termination_by datasize

example : rev_vector 32 16 8 0xaabbccdd#32 (by decide)
          (by decide) (by decide) (by decide) (by decide) =
          0xbbaaddcc#32 := by
          native_decide

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
    simp_all only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    generalize h_yvar : Std.BitVec.toNat y = yvar
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
      simp only [Nat.not_le] at h0
      exact esize_dvd_container_size inst.size (extractLsb 0 0 inst.opcode ++ inst.U) h0
    have h2 : container_size ∣ datasize := by
      simp_all [datasize]
      exact container_size_dvd_datasize (extractLsb 0 0 inst.opcode ++ inst.U) inst.Q
    have h3 : 0 < esize := by
      simp_all only [Nat.sub_zero, Nat.shiftLeft_eq, Nat.not_le, beq_iff_eq, esize]
      rw [Nat.mul_pos_iff_of_pos_left]
      simp only [gt_iff_lt, Nat.zero_lt_two, Nat.pow_pos]
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
