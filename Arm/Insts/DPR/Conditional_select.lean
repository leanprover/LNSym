/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- CSEL, CSINC, CSINV, CSNEG: 32- and 64-bit versions

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

namespace DPR

open Std.BitVec

@[simp]
def exec_conditional_select (inst : Conditional_select_cls) (s : ArmState) : ArmState :=
    let datasize := if inst.sf = 1#1 then 64 else 32
    let (unimplemented, result) :=
      match inst.op, inst.S, inst.op2 with
        | 0b0#1, 0b0#1, 0b00#2 => -- CSEL
          (false,
            if ConditionHolds inst.cond (read_pstate s) then
              read_gpr_zr datasize inst.Rn s
            else
              read_gpr_zr datasize inst.Rm s)
        | _, _, _ =>
          (true, Std.BitVec.ofNat datasize 0)
    -- State Updates
    if unimplemented then
      write_err
        (StateError.Unimplemented
          s!"Unsupported DPR.Conditional_select_cls {inst} encountered in exec_inst!")
      s
    else
      let s            := write_pc ((read_pc s) + 4#64) s
      let s            := write_gpr_zr datasize inst.Rd result s
      s

/-- Generate random instructions of the DPR.Conditional_select class. -/
def Conditional_select_cls.rand : IO (Option (BitVec 32)) := do
  let (inst : Conditional_select_cls) :=
    { sf    := ← BitVec.rand 1,
      op    := ← pure 0#1,
      S     := ← pure 0#1,
      Rm    := ← BitVec.rand 5,
      cond  := ← BitVec.rand 4,
      op2   := ← pure 0b00#2,
      Rn    := ← BitVec.rand 5,
      Rd    := ← BitVec.rand 5 }
  pure (some (inst.toBitVec32))

----------------------------------------------------------------------

end DPR
