/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- LSLV, LSRV, ASRV, RORV (32-, 64-bit)

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace DPR

open BitVec

@[state_simp_rules]
def exec_data_processing_shift
  (inst : Data_processing_two_source_cls) (s : ArmState) : ArmState :=
  let datasize := 32 <<< inst.sf.toNat
  let shift_type := decode_shift $ extractLsb 1 0 inst.opcode
  let operand2 := read_gpr_zr datasize inst.Rm s
  let amount := BitVec.ofInt 6 (operand2.toInt % datasize)
  let operand := read_gpr_zr datasize inst.Rn s
  let result := shift_reg operand shift_type amount
  -- State Update
  let s := write_gpr_zr datasize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_data_processing_two_source
  (inst : Data_processing_two_source_cls) (s : ArmState) : ArmState :=
  match inst.S, inst.opcode with
  | 0b0#1, 0b001000#6 -- LSLV 32-, 64-bit
  | 0b0#1, 0b001001#6 -- LSRV 32-, 64-bit
  | 0b0#1, 0b001010#6 -- ASRV 32-, 64-bit
  | 0b0#1, 0b001011#6 -- RORV 32-, 64-bit
    => exec_data_processing_shift inst s
  | _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

def Data_processing_two_source_cls.shift.rand
  (opcode : BitVec 6) : IO (Option (BitVec 32)) := do
  let (inst : Data_processing_two_source_cls) :=
    { sf := ← BitVec.rand 1,
      S := 0b0#1,
      Rm := ← BitVec.rand 5,
      opcode := opcode,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5
    }
  pure (some inst.toBitVec32)

/-- Generate random instructions of Data_processing_two_source_cls class. -/
def Data_processing_two_source_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Data_processing_two_source_cls.shift.rand 0b001000#6,
    Data_processing_two_source_cls.shift.rand 0b001001#6,
    Data_processing_two_source_cls.shift.rand 0b001010#6,
    Data_processing_two_source_cls.shift.rand 0b001011#6
  ]

end DPR
