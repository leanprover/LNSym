/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Nathan Wetzler
-/
-- MADD, MSUB (32-, 64-bit); SMADDL, SMSUBL, SMULH, UMADDL, UMSUBL, UMULH

import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

----------------------------------------------------------------------

namespace DPR

open BitVec

@[state_simp_rules]
def exec_data_processing_madd
  (inst : Data_processing_three_source_cls) (s : ArmState) : ArmState :=
  let destsize := 32 <<< inst.sf.toNat
  let operand1 := read_gpr_zr destsize inst.Rn s
  let operand2 := read_gpr_zr destsize inst.Rm s
  let operand3 := read_gpr_zr destsize inst.Ra s
  -- let result := BitVec.add operand3 (BitVec.mul operand1 operand2)
  let result := operand3 + (operand1 * operand2)
  -- State Update
  let s := write_gpr_zr destsize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_data_processing_three_source
  (inst : Data_processing_three_source_cls) (s : ArmState) : ArmState :=
  let (illegal, unimplemented) :=
    match inst.sf, inst.op54, inst.op31, inst.o0 with
    | _, 0b00#2, 0b010#3, 0b1#1
    | _, 0b00#2, 0b011#3, _
    | _, 0b00#2, 0b100#3, _
    | _, 0b00#2, 0b110#3, 0b1#1
    | _, 0b00#2, 0b111#3, _
    | _, 0b01#2, _, _
    | _, 0b10#2, _, _
    | _, 0b11#2, _, _
      => (true, false) -- Unallocated
    | 0b0#1, 0b00#2, 0b000#3, 0b0#1 => (false, false) -- MADD (32-bit)
    | 0b0#1, 0b00#2, 0b000#3, 0b1#1 => (false, true)  -- MSUB (32-bit)
    | 0b0#1, 0b00#2, 0b001#3, 0b0#1
    | 0b0#1, 0b00#2, 0b001#3, 0b1#1
    | 0b0#1, 0b00#2, 0b010#3, 0b0#1
    | 0b0#1, 0b00#2, 0b101#3, 0b0#1
    | 0b0#1, 0b00#2, 0b101#3, 0b1#1
    | 0b0#1, 0b00#2, 0b110#3, 0b0#1
      => (true, false) -- Unallocated
    | 0b1#1, 0b00#2, 0b000#3, 0b0#1 => (false, false) -- MADD (64-bit)
    | 0b1#1, 0b00#2, 0b000#3, 0b1#1 => (false, true)  -- MSUB (64-bit)
    | 0b1#1, 0b00#2, 0b001#3, 0b0#1 => (false, true)  -- SMADDL
    | 0b1#1, 0b00#2, 0b001#3, 0b1#1 => (false, true)  -- SMSUBL
    | 0b1#1, 0b00#2, 0b010#3, 0b0#1 => (false, true)  -- SMULH
    | 0b1#1, 0b00#2, 0b101#3, 0b0#1 => (false, true)  -- UMADDL
    | 0b1#1, 0b00#2, 0b101#3, 0b1#1 => (false, true)  -- UMSUBL
    | 0b1#1, 0b00#2, 0b110#3, 0b0#1 => (false, true)  -- UMULH
    | _, _, _, _ => (true, false)
  if illegal then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if unimplemented then
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  else
    match inst.sf, inst.op54, inst.op31, inst.o0 with
    | 0b0#1, 0b00#2, 0b000#3, 0b0#1 => exec_data_processing_madd inst s -- MADD (32-bit)
    | 0b1#1, 0b00#2, 0b000#3, 0b0#1 => exec_data_processing_madd inst s -- MADD (64-bit)
    | _, _, _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

def Data_processing_three_source_cls.shift.rand
  (sf : BitVec 1) (op54 : BitVec 2) (op31 : BitVec 3) (o0 : BitVec 1)
  : IO (Option (BitVec 32)) := do
  let (inst : Data_processing_three_source_cls) :=
    { sf := sf,
      op54 := op54,
      op31 := op31,
      Rm := ← BitVec.rand 5,
      o0 := o0,
      Ra := ← BitVec.rand 5,
      Rn := ← BitVec.rand 5,
      Rd := ← GPRIndex.rand
    }
  pure (some inst.toBitVec32)

/-- Generate random instructions of Data_processing_three_source_cls class. -/
def Data_processing_three_source_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [ Data_processing_three_source_cls.shift.rand 0b0#1 0b00#2 0b000#3 0b0#1, -- MADD (32-bit)
    Data_processing_three_source_cls.shift.rand 0b1#1 0b00#2 0b000#3 0b0#1, -- MADD (64-bit)
  ]

end DPR
