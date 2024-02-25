/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- ADD, ADDS, SUB, SUBS (shifted registers): 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common

namespace DPR

open BitVec

@[simp]
def exec_add_sub_shifted_reg (inst : Add_sub_shifted_reg_cls) (s : ArmState) : ArmState :=
  let datasize := 32 <<< inst.sf.toNat
  if inst.shift == 0b11#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.sf == 0 && extractLsb 5 5 inst.imm6 == 1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let sub_op := inst.op == 1#1
    let setflags := inst.S == 1#1
    let shift_type := decode_shift inst.shift
    let operand1 := read_gpr_zr datasize inst.Rn s
    let operand2_unshifted := read_gpr_zr datasize inst.Rm s
    let operand2 := shift_reg operand2_unshifted shift_type inst.imm6
    let operand2 := if sub_op then ~~~operand2 else operand2
    let carry := if sub_op then 1 else 0
    let (result, pstate) := AddWithCarry operand1 operand2 carry
    -- State Updates
    let s'            := write_pc ((read_pc s) + 4#64) s
    let s'            := if setflags then write_pstate pstate s' else s'
    let s'            := write_gpr_zr datasize inst.Rd result s'
    s'

----------------------------------------------------------------------

/-- Generate random instructions of the DPR.Add_sub_shifted_reg class. -/
partial def Add_sub_shifted_reg_cls.rand : IO (Option (BitVec 32)) := do
  let shift := ← BitVec.rand 2
  let sf := ← BitVec.rand 1
  let imm6 := ← BitVec.rand 6
  if shift == 0b11#2 then
    Add_sub_shifted_reg_cls.rand
  else if sf == 0 && extractLsb 5 5 imm6 == 1 then
    Add_sub_shifted_reg_cls.rand
  else
    let (inst : Add_sub_shifted_reg_cls) :=
      { sf    := sf,
        op    := ← BitVec.rand 1,
        S     := ← BitVec.rand 1,
        shift := shift,
        Rm    := ← BitVec.rand 5,
        imm6  := imm6,
        Rn    := ← BitVec.rand 5,
        Rd    := ← BitVec.rand 5 }
    pure (some (inst.toBitVec32))

----------------------------------------------------------------------

end DPR
