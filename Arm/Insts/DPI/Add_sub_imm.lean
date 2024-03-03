/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- ADD, ADDS, SUB, SUBS (immediate): 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common

namespace DPI

open BitVec

@[state_simp_rules]
def exec_add_sub_imm (inst : Add_sub_imm_cls) (s : ArmState) : ArmState :=
    let sub_op        := inst.op == 1#1
    let setflags      := inst.S == 1#1
    let datasize      := if inst.sf == 1#1 then 64 else 32
    let imm           := 0#52 ++ inst.imm12
    let imm           := if inst.sh == 0#1 then
                          imm
                        else
                          imm <<< 12
    let operand1      := read_gpr datasize inst.Rn s
    let (carry_in, operand2)
                      := if sub_op then
                          (1#1, ~~~imm)
                        else
                          (0#1, imm)
    let operand2      := BitVec.zeroExtend datasize operand2
    let (result, pstate) := AddWithCarry operand1 operand2 carry_in
    -- State Updates
    let s'            := write_pc ((read_pc s) + 4#64) s
    let s'            := if setflags then write_pstate pstate s' else s'
    let s'            := write_gpr datasize inst.Rd result s'
    s'

----------------------------------------------------------------------

/-- Generate random instructions of the DPI.Add_sub_imm class. -/
def Add_sub_imm_cls.inst.rand : IO (Option (BitVec 32)) := do
  let (inst : Add_sub_imm_cls) :=
    { sf    := ← BitVec.rand 1,
      op    := ← BitVec.rand 1,
      S     := ← BitVec.rand 1,
      sh    := ← BitVec.rand 1,
      imm12 := ← BitVec.rand 12,
       -- (FIXME) We want to avoid any use of SP (i.e., register index
       -- 31) since our simulation framework doesn't work in such
       -- cases. For now, we do sacrifice a little bit of the state
       -- space.
      Rn    := ← BitVec.rand 5 (lo := 0) (hi := 30),
      Rd    := ← BitVec.rand 5 (lo := 0) (hi := 30) }
  pure (some (inst.toBitVec32))

def Add_sub_imm_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Add_sub_imm_cls.inst.rand ]
----------------------------------------------------------------------

end DPI
