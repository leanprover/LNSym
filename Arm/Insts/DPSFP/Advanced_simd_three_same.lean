/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
-- ADD, ORR (vector)

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open Std.BitVec

theorem vector_op_helper_lemma (x y : Nat) (h : 0 < y) :
  x + y - 1 - x + 1 = y := by
    rw [Nat.add_sub_assoc h, Nat.add_sub_cancel_left, Nat.sub_add_cancel h]

def vector_op (e : Nat) (elems : Nat) (esize : Nat)
  (op : BitVec esize → BitVec esize → BitVec esize)
  (x : BitVec n) (y : BitVec n) (result : BitVec n)
  (H : esize > 0) : BitVec n :=
  if h₀ : elems ≤ e then
    result
  else
    have h₁ : e < elems := by
      simp at h₀; exact h₀
    let lo := e * esize
    let hi := lo + esize - 1
    let element1 := BitVec.extract x hi lo
    let element2 := BitVec.extract y hi lo
    have h : hi - lo + 1 = esize := by
      simp; apply vector_op_helper_lemma; simp [*] at *
    let elem_result := op (h ▸ element1) (h ▸ element2)
    let result := BitVec.partInstall hi lo (h.symm ▸ elem_result) result
    have ht1 : elems - (e + 1) < elems - e := by
      apply Nat.sub_succ_lt_self elems e h₁
    vector_op (e + 1) elems esize op x y result H
  termination_by vector_op e elems esize op x y result H => (elems - e)

-- #eval vector_op 0 2 4 Std.BitVec.add 0xAB 0x12 (Std.BitVec.zero 8)

@[simp]
def exec_add_vector (inst : Advanced_simd_three_same_cls) (s : ArmState) : ArmState :=
  if inst.size == 0b11#2 && inst.Q == 0b0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := if inst.Q = 1#1 then 128 else 64
    let esize := 8 <<< (Std.BitVec.toNat inst.size)
    have h_esize : esize > 0 := by
      simp_all only [Nat.shiftLeft_eq, gt_iff_lt, 
                     Nat.zero_lt_succ, mul_pos_iff_of_pos_left, 
                     zero_lt_two, pow_pos]
    let elements := datasize / esize
    let operand1 := read_sfp datasize inst.Rn s
    let operand2 := read_sfp datasize inst.Rm s
    let result := vector_op 0 elements esize Std.BitVec.add operand1 operand2 (Std.BitVec.zero datasize) h_esize
    let s := write_sfp datasize inst.Rd result s
    s

@[simp]
def exec_orr_vector_reg (inst : Advanced_simd_three_same_cls) (s : ArmState) : ArmState :=
  let datasize := if inst.Q = 1#1 then 128 else 64
  let operand1 := read_sfp datasize inst.Rn s
  let operand2 := read_sfp datasize inst.Rm s
  let result := operand1 ||| operand2
  let s := write_sfp datasize inst.Rd result s
  s

@[simp]
def exec_advanced_simd_three_same
  (inst : Advanced_simd_three_same_cls) (s : ArmState) : ArmState :=
  open Std.BitVec in
  let s :=
    match inst.U, inst.size, inst.opcode with
    | 0#1, _, 0b10000#5 => exec_add_vector inst s
    | 0#1, 0b10#2, 0b00011#5 => exec_orr_vector_reg inst s
    | _, _, _ =>
      write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  write_pc ((read_pc s) + 4#64) s

theorem pc_of_exec_advanced_simd_three_same
  (h_step : s' = exec_advanced_simd_three_same inst s)
  (h_no_err: read_err s' = None) :
  r StateField.PC s' =
  -- (r StateField.PC s) + 4#64 -- TODO: How do I use + here?
  (Std.BitVec.add (r StateField.PC s) 4#64) := by
  simp_all!
  simp [exec_advanced_simd_three_same, exec_orr_vector_reg, exec_add_vector]
  split
  · split <;> simp
  · simp
  · simp

----------------------------------------------------------------------

def Advanced_simd_three_same_cls.add64.rand : IO (Option (BitVec 32)) := do
  let (inst : Advanced_simd_three_same_cls) :=
    { Q := ← pure 0b0#1,
      U := ← pure 0b0#1,
      size := ← BitVec.rand 2 (lo := 0) (hi := 2),
      Rm := ← BitVec.rand 5,
      opcode := ← pure 0b10000#5,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  pure (inst.toBitVec32)

def Advanced_simd_three_same_cls.add128.rand : IO (Option (BitVec 32)) := do
  let (inst : Advanced_simd_three_same_cls) :=
    { Q := ← pure 0b1#1,
      U := ← pure 0b0#1,
      size := ← BitVec.rand 2,
      Rm := ← BitVec.rand 5,
      opcode := ← pure 0b10000#5,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  pure (inst.toBitVec32)

def Advanced_simd_three_same_cls.orr.rand : IO (Option (BitVec 32)) := do
  let (inst : Advanced_simd_three_same_cls) :=
    { Q := ← BitVec.rand 1,
      U := ← pure 0b0#1,
      size := ← pure 0b10#2,
      Rm := ← BitVec.rand 5,
      opcode := ← pure 0b00011#5,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  pure (inst.toBitVec32)

/-- Generate random instructions of Advanced_simd_three_same class. -/
def Advanced_simd_three_same_cls.rand : List (IO (Option (BitVec 32))) :=
  [Advanced_simd_three_same_cls.add64.rand,
   Advanced_simd_three_same_cls.add128.rand,
   Advanced_simd_three_same_cls.orr.rand]


end DPSFP
