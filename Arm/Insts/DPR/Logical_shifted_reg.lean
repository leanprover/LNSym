/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- AND, BIC, ORR, ORN, EOR, EON, ANDS, BICS: 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common

namespace DPR

open BitVec

@[state_simp_rules]
def decode_op (opc : BitVec 2) (N : BitVec 1) : LogicalShiftedRegType :=
  match opc, N with
  | 0b00, 0b0 => LogicalShiftedRegType.AND
  | 0b00, 0b1 => LogicalShiftedRegType.BIC
  | 0b01, 0b0 => LogicalShiftedRegType.ORR
  | 0b01, 0b1 => LogicalShiftedRegType.ORN
  | 0b10, 0b0 => LogicalShiftedRegType.EOR
  | 0b10, 0b1 => LogicalShiftedRegType.EON
  | 0b11, 0b0 => LogicalShiftedRegType.ANDS
  | 0b11, 0b1 => LogicalShiftedRegType.BICS

def logical_shifted_reg_update_pstate (bv : BitVec n) : PState :=
  have h: n - 1 - (n - 1) + 1 = 1 := by simp
  let N := h ▸ (BitVec.lsb bv (n-1))
  let Z := zero_flag_spec bv
  let C := 0#1
  let V := 0#1
  (make_pstate N Z C V)

@[state_simp_rules]
def exec_logical_shifted_reg_op (op : LogicalShiftedRegType) (opd1 : BitVec n) (opd2 : BitVec n)
  : (BitVec n × Option PState) :=
  match op with
  | LogicalShiftedRegType.AND => (opd1 &&& opd2, none)
  | LogicalShiftedRegType.BIC => (opd1 &&& ~~~opd2, none)
  | LogicalShiftedRegType.ORR => (opd1 ||| opd2, none)
  | LogicalShiftedRegType.ORN => (opd1 ||| ~~~opd2, none)
  | LogicalShiftedRegType.EOR => (opd1 ^^^ opd2, none)
  | LogicalShiftedRegType.EON => (opd1 ^^^ ~~~opd2, none)
  | LogicalShiftedRegType.ANDS =>
    let result := opd1 &&& opd2
    (result, some (logical_shifted_reg_update_pstate result))
  | LogicalShiftedRegType.BICS =>
    let result := opd1 &&& ~~~opd2
    (result, some (logical_shifted_reg_update_pstate result))

@[state_simp_rules]
def exec_logical_shifted_reg (inst : Logical_shifted_reg_cls) (s : ArmState) : ArmState :=
  if inst.sf = 0#1 ∧ inst.imm6 &&& 32 ≠ 0 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let operand1 := read_gpr_zr datasize inst.Rn s
    let operand2_unshifted := read_gpr_zr datasize inst.Rm s
    let shift_type := decode_shift inst.shift
    let operand2 := shift_reg operand2_unshifted shift_type inst.imm6
    let op := decode_op inst.opc inst.N
    let (result, maybe_pstate) := exec_logical_shifted_reg_op op operand1 operand2
    -- State Updates
    let s'            := write_pc ((read_pc s) + 4#64) s
    let s'            := match maybe_pstate with
                         | none => s'
                         | some pstate => write_pstate pstate s'
    let s'            := write_gpr_zr datasize inst.Rd result s'
    s'

----------------------------------------------------------------------

/-- Generate random instructions of the DPR.Logical_shifted_reg class. -/
partial def Logical_shifted_reg_cls.rand : IO (Option (BitVec 32)) := do
  let sf    := ← BitVec.rand 1
  let imm6  := ← BitVec.rand 6
  if sf = 0#1 ∧ imm6 &&& 32 ≠ 0 then
    Logical_shifted_reg_cls.rand
  else
    let (inst : Logical_shifted_reg_cls) :=
      { sf    := sf,
        opc   := ← BitVec.rand 2,
        shift := ← BitVec.rand 2,
        N     := ← BitVec.rand 1,
        Rm    := ← BitVec.rand 5,
        imm6  := imm6,
        Rn    := ← BitVec.rand 5,
        Rd    := ← BitVec.rand 5 }
    pure (some (inst.toBitVec32))

----------------------------------------------------------------------

end DPR
