/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- PMULL and PMULL2
-- Polynomial arithmetic over {0,1}:
-- Ref.:
-- https://developer.arm.com/documentation/ddi0602/2024-09/SIMD-FP-Instructions/PMULL--PMULL2--Polynomial-multiply-long-?lang=en

import Arm.Decode
import Arm.State
import Arm.Insts.Common
import Arm.Insts.CosimM

----------------------------------------------------------------------

namespace DPSFP

open BitVec

def polynomial_mult_aux (i : Nat) (result : BitVec (m+n))
  (op1 : BitVec m) (op2 : BitVec (m+n)) : BitVec (m+n) :=
  if h₀ : i ≥ m then
    result
  else
    let new_res := if lsb op1 i = 1 then result ^^^ (op2 <<< i) else result
    -- We replace `if` below by bitvec operations.
    -- have h : (1 * (m + n)) = m + n := by simp only [Nat.one_mul]
    -- let test := (replicate (m+n) (lsb op1 i)).cast h
    -- let then_branch := test &&& (result ^^^ (op2 <<< i))
    -- let else_branch := ~~~test &&& result
    -- let new_res := then_branch ||| else_branch
    polynomial_mult_aux (i+1) new_res op1 op2
  termination_by (m - i)

def polynomial_mult (op1 : BitVec m) (op2 : BitVec n) : BitVec (m+n) :=
  let result := 0#(m+n)
  let extended_op2 := zeroExtend (m+n) op2
  polynomial_mult_aux 0 result op1 extended_op2

def pmull_op (e : Nat) (esize : Nat) (elements : Nat) (x : BitVec n)
  (y : BitVec n) (result : BitVec (n*2)) : BitVec (n*2) :=
  if elements <= e then
    result
  else
    let element1 := elem_get x e esize
    let element2 := elem_get y e esize
    let elem_result := polynomial_mult element1 element2
    have h₁ : esize + esize = 2 * esize := by omega
    let result := elem_set result e (2 * esize) (BitVec.cast h₁ elem_result)
    pmull_op (e + 1) esize elements x y result
  termination_by (elements - e)

@[state_simp_rules]
def exec_pmull (inst : Advanced_simd_three_different_cls) (s : ArmState) : ArmState :=
  -- This function assumes IsFeatureImplemented(FEAT_PMULL) is true
  if inst.size = 0b01#2 ∨ inst.size = 0b10#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< inst.size.toNat
    let datasize := 64
    let part := inst.Q.toNat
    let elements := datasize / esize
    let operand1 := Vpart_read inst.Rn part datasize s
    let operand2 := Vpart_read inst.Rm part datasize s
    let result :=
      pmull_op 0 esize elements operand1 operand2 (BitVec.zero (2*datasize))
    let s := write_sfp (datasize*2) inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

@[state_simp_rules]
def exec_advanced_simd_three_different
  (inst : Advanced_simd_three_different_cls) (s : ArmState) : ArmState :=
  match inst.U, inst.opcode with
  | 0b0#1, 0b1110#4 => exec_pmull inst s
  | _, _ => write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

----------------------------------------------------------------------

partial def Advanced_simd_three_different_cls.pmull.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let size := ← BitVec.rand 2
  if size == 0b01#2 || size == 0b10#2 then
    Advanced_simd_three_different_cls.pmull.rand
  else
    let (inst : Advanced_simd_three_different_cls) :=
      { Q := ← BitVec.rand 1,
        U := 0b0#1,
        size := size,
        Rm := ← BitVec.rand 5,
        opcode := 0b1110#4,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (some (inst.toBitVec32))

/-- Generate random instructions of Advanced_simd_three_different class. -/
def Advanced_simd_three_different_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [Advanced_simd_three_different_cls.pmull.rand]

end DPSFP
