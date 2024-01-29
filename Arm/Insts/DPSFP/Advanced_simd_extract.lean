/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
-- EXT

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open Std.BitVec

@[simp]
def exec_advanced_simd_extract
  (inst : Advanced_simd_extract_cls) (s : ArmState) : ArmState :=
  open Std.BitVec in
  if inst.op2 ≠ 0#2 then
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  else if inst.Q == 0b0#1 && extractLsb 3 3 inst.imm4 == 0b1#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := if inst.Q = 1#1 then 128 else 64
    let position := inst.imm4.toNat <<< 3
    let hi := read_sfp datasize inst.Rm s
    let lo := read_sfp datasize inst.Rn s
    let concat := hi ++ lo
    let result := extractLsb (position + datasize - 1) position concat
    have h_datasize : 1 <= datasize := by simp_all!; split <;> decide
    have h : (position + datasize - 1 - position + 1) = datasize := by
      rw [Nat.add_sub_assoc, Nat.add_sub_self_left]
      exact Nat.sub_add_cancel h_datasize; trivial
    let s := write_sfp datasize inst.Rd (h ▸ result) s
    let s := write_pc ((read_pc s) + 4#64) s
    s

----------------------------------------------------------------------

def Advanced_simd_extract_cls.ext.rand_128 : IO (Option (BitVec 32)) := do
  let (inst : Advanced_simd_extract_cls) :=
    -- When Q is 1, there are no restrictions on imm4.
    { Q     := ← pure 0b1#1,
      op2   := ← pure 0b00#2, -- Picks EXT.
      Rm    := ← BitVec.rand 5,
      imm4  := ← BitVec.rand 4,
      Rn    := ← BitVec.rand 5,
      Rd    := ← BitVec.rand 5 }
  pure (some (inst.toBitVec32))

def Advanced_simd_extract_cls.ext.rand_64 : IO (Option (BitVec 32)) := do
  let (inst : Advanced_simd_extract_cls) :=
    -- When Q is 0, imm4<3> must not be 1.
    { Q     := ← pure 0b0#1,
      op2   := ← pure 0b00#2, -- Picks EXT.
      Rm    := ← BitVec.rand 5,
      imm4  := ← BitVec.rand 4 (lo := 0b0) (hi := 0b111),
      Rn    := ← BitVec.rand 5,
      Rd    := ← BitVec.rand 5 }
  pure (some (inst.toBitVec32))

/-- Generate random instructions of Advanced_simd_extract class. -/
def Advanced_simd_extract_cls.rand : List (IO (Option (BitVec 32))) :=
  [Advanced_simd_extract_cls.ext.rand_128,
   Advanced_simd_extract_cls.ext.rand_64]

end DPSFP
