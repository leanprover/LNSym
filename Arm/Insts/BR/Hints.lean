/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- NOP

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace BR

open BitVec

@[state_simp_rules]
def exec_hints (inst : Hints_cls) (s : ArmState) : ArmState :=
  if inst.CRm = 0b0000#4 ∧ inst.op2 = 0b000#3 then
    write_pc ((read_pc s) + 4#64) s
  else
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

def Hints_cls.nop.rand : IO (Option (BitVec 32)) := do
  let (inst : Hints_cls) :=
    { CRm := 0b0000#4,
      op2 := 0b000#3
    }
  pure (some (inst.toBitVec32))

/-- Generate random instructions of Hints_cls class. -/
def Hints_cls.rand : IO (Option (BitVec 32)) :=
  Hints_cls.nop.rand

end BR
