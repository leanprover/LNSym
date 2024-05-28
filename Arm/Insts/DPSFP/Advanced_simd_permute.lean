/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- TRN1, TRN2

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace DPSFP

open BitVec

def trn_aux (p : Nat) (pairs : Nat) (esize : Nat) (part : Nat)
  (operand1 : BitVec datasize) (operand2 : BitVec datasize)
  (result : BitVec datasize) (h : esize > 0) : BitVec datasize :=
  if h₀ : pairs <= p then
    result
  else
    let idx_from := 2 * p + part
    let op1_part := elem_get operand1 idx_from esize h
    let op2_part := elem_get operand2 idx_from esize h
    let result := elem_set result (2 * p) esize op1_part h
    let result := elem_set result (2 * p + 1) esize op2_part h
    have h₁ : pairs - (p + 1) < pairs - p := by omega
    trn_aux (p + 1) pairs esize part operand1 operand2 result h
  termination_by (pairs - p)

@[state_simp_rules]
def exec_trn (inst : Advanced_simd_permute_cls) (s : ArmState) : ArmState :=
  if inst.size ++ inst.Q == 0b110#3 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< inst.size.toNat
    let datasize := 64 <<< inst.Q.toNat
    let elements := datasize / esize
    let op := lsb inst.opcode 2
    let part := op.toNat
    let pairs := elements / 2
    let operand1 := read_sfp datasize inst.Rn s
    let operand2 := read_sfp datasize inst.Rm s
    have h : esize > 0 := by apply zero_lt_shift_left_pos (by decide)
    let result := trn_aux 0 pairs esize part operand1 operand2 (BitVec.zero datasize) h
    -- Update States
    let s := write_sfp datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

@[state_simp_rules]
def exec_advanced_simd_permute
  (inst : Advanced_simd_permute_cls) (s : ArmState) : ArmState :=
  match inst.opcode with
  | 0b010#3
  | 0b110#3 => exec_trn inst s
  | _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

partial def Advanced_simd_permute_cls.trn1.rand : IO (Option (BitVec 32)) := do
  let size := ← BitVec.rand 2
  let Q := ← BitVec.rand 1
  if size ++ Q == 0b110#3 then
    Advanced_simd_permute_cls.trn1.rand
  else
    let (inst : Advanced_simd_permute_cls) :=
      { Q := Q,
        size := size,
        Rm := ← BitVec.rand 5,
        opcode := 0b010#3,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (some (inst.toBitVec32))

partial def Advanced_simd_permute_cls.trn2.rand : IO (Option (BitVec 32)) := do
  let size := ← BitVec.rand 2
  let Q := ← BitVec.rand 1
  if size ++ Q == 0b110#3 then
    Advanced_simd_permute_cls.trn2.rand
  else
    let (inst : Advanced_simd_permute_cls) :=
      { Q := Q,
        size := size,
        Rm := ← BitVec.rand 5,
        opcode := 0b110#3,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (some (inst.toBitVec32))

/-- Generate random instructions of Advanced_simd_permute class. -/
def Advanced_simd_permute_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Advanced_simd_permute_cls.trn1.rand,
    Advanced_simd_permute_cls.trn2.rand ]

end DPSFP
