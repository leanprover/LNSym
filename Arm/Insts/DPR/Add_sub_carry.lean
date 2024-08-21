/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- ADC, ADCS, SBC, SBCS: 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common

namespace DPR

open BitVec

@[state_simp_rules]
def exec_add_sub_carry (inst : Add_sub_carry_cls) (s : ArmState) : ArmState :=
    let sub_op        := inst.op = 1#1
    let setflags      := inst.S = 1#1
    let datasize      := if inst.sf = 1#1 then 64 else 32
    let operand1      := read_gpr_zr datasize inst.Rn s
    let operand2      := read_gpr_zr datasize inst.Rm s
    let operand2      := if sub_op then
                          ~~~operand2
                         else
                          operand2
    let (result, pstate) := AddWithCarry operand1 operand2 (read_flag PFlag.C s)
    -- State Updates
    let s'            := write_pc ((read_pc s) + 4#64) s
    let s'            := if setflags then write_pstate pstate s' else s'
    let s'            := write_gpr_zr datasize inst.Rd result s'
    s'

----------------------------------------------------------------------

/-- Generate random instructions of the DPR.Add_sub_carry class. -/
def Add_sub_carry_cls.rand : IO (Option (BitVec 32)) := do
  let (inst : Add_sub_carry_cls) :=
    { sf    := ← BitVec.rand 1,
      op    := ← BitVec.rand 1,
      S     := ← BitVec.rand 1,
      Rm    := ← BitVec.rand 5,
      Rn    := ← BitVec.rand 5,
      Rd    := ← GPRIndex.rand }
  pure (some (inst.toBitVec32))

----------------------------------------------------------------------

end DPR
