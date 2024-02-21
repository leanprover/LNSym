/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Yan Peng
-/
-- DUP (element) scalar

import Arm.Decode
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open Std.BitVec

theorem advanced_simd_scalar_copy_helper_lemma (x y : Nat):
  y + 8 <<< x - 1 - y + 1 = 8 <<< x := by sorry

@[simp]
def exec_advanced_simd_scalar_copy
  (inst : Advanced_simd_scalar_copy_cls) (s : ArmState) : ArmState :=
  let size := lowest_set_bit inst.imm5
  if h₀ : size > 3 || inst.imm4 != 0b0000#4 || inst.op != 0 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let index := extractLsb 4 (size + 1) inst.imm5
    let idxdsize := 64 <<< (extractLsb 4 4 inst.imm5).toNat
    let esize := 8 <<< size
    let datasize := esize
    let operand := read_sfp idxdsize inst.Rn s
    let lo := index.toNat * esize
    let hi := lo + esize - 1
    let result := extractLsb hi lo operand
    have h : hi - lo + 1 = datasize := by
      simp; apply advanced_simd_scalar_copy_helper_lemma
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp datasize inst.Rd (h ▸ result) s
    s

----------------------------------------------------------------------

partial def Advanced_simd_scalar_copy_cls.dup.rand : IO (Option (BitVec 32)) := do
  let imm5 := ← BitVec.rand 5
  if (Option.get! $ lowest_set_bit imm5) > 3 then
    Advanced_simd_scalar_copy_cls.dup.rand
  else
    let (inst : Advanced_simd_scalar_copy_cls) :=
      { op := 0b0#1
      , imm5 := imm5
      , imm4 := 0b0000#4
      , Rn := ← BitVec.rand 5
      , Rd := ← BitVec.rand 5
      }
    pure (some inst.toBitVec32)

/-- Generate random instructions of Advanced_simd_scalar_copy class. -/
def Advanced_simd_scalar_copy_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Advanced_simd_scalar_copy_cls.dup.rand ]

end DPSFP
