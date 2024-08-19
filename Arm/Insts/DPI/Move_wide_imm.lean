/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- MOVZ, MOVK and MOVN

import Arm.Decode
import Arm.Insts.Common

namespace DPI

open BitVec

@[state_simp_rules]
def exec_move_wide_imm (inst : Move_wide_imm_cls) (s : ArmState) : ArmState :=
  if inst.opc = 0b01#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.sf = 0#1 ∧ getLsb inst.hw 1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let pos := (inst.hw ++ 0b0000#4).toNat
    let result := if inst.opc = 0b11#2
                  then read_gpr datasize inst.Rd s
                  else BitVec.zero datasize
    have h : 16 = pos + 15 - pos + 1 := by omega
    let result := partInstall (pos + 15) pos (BitVec.cast h inst.imm16) result
    let result := if inst.opc = 0b00#2 then ~~~result else result
    -- State Update
    let s := write_gpr datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

----------------------------------------------------------------------

/-- Generate random instructions of the DPI.Move_wide_imm class. -/
partial def Move_wide_imm_cls.inst.rand : IO (Option (BitVec 32)) := do
  let opc := ← BitVec.rand 2
  let sf := ← BitVec.rand 1
  let hw := ← BitVec.rand 2
  if opc == 0b01#2 || sf == 0#1 && getLsb hw 1 then
    Move_wide_imm_cls.inst.rand
  else
    let (inst : Move_wide_imm_cls) :=
      { sf := sf,
        opc := opc,
        hw := hw,
        imm16 := ← BitVec.rand 16,
        Rd := ← GPRIndex.rand
      }
    pure (some inst.toBitVec32)


def Move_wide_imm_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Move_wide_imm_cls.inst.rand ]
----------------------------------------------------------------------

end DPI
