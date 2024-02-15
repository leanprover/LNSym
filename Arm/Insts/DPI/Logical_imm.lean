/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- AND, ORR, EOR, ANDS (immediate): 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common

namespace DPI

open Std.BitVec

def decode_op (opc : BitVec 2) : LogicalImmType :=
  match opc with
  | 00#2 => LogicalImmType.AND
  | 01#2 => LogicalImmType.ORR
  | 10#2 => LogicalImmType.EOR
  | 11#2 => LogicalImmType.ANDS

def update_logical_imm_pstate (bv : BitVec n) : PState :=
  have h: n - 1 - (n - 1) + 1 = 1 := by simp
  let N := h ▸ (Std.BitVec.extractLsb (n-1) (n-1) bv)
  let Z := zero_flag_spec bv
  let C := 0#1
  let V := 0#1
  (make_pstate N Z C V)

def exec_logical_imm_op (op : LogicalImmType) (op1 : BitVec n) (op2 : BitVec n)
  : (BitVec n × Option PState) :=
  match op with
  | LogicalImmType.AND => (op1 &&& op2, none)
  | LogicalImmType.ORR => (op1 ||| op2, none)
  | LogicalImmType.EOR => (op1 ^^^ op2, none)
  | LogicalImmType.ANDS =>
    let result := op1 &&& op2
    (op1 &&& op2, some (update_logical_imm_pstate result))

@[simp]
def exec_logical_imm (inst : Logical_imm_cls) (s : ArmState) : ArmState :=
  if inst.sf = 0#1 ∧ inst.N ≠ 0 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let imm := decode_bit_masks inst.N inst.imms inst.immr true datasize
    match imm with
    | none => write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    | some (imm, _) =>
      let operand1 := read_gpr datasize inst.Rn s
      let op := decode_op inst.opc
      let (result, maybe_pstate) := exec_logical_imm_op op operand1 imm
      -- State Updates
      let s'            := write_pc ((read_pc s) + 4#64) s
      let s'            := match maybe_pstate with
                           | none => s'
                           | some pstate => write_pstate pstate s'
      let s'            := write_gpr datasize inst.Rd result s'
      s'

----------------------------------------------------------------------

/-- Generate random instructions of the DPI.Logical_imm class. -/
partial def Logical_imm_cls.rand : IO (Option (BitVec 32)) := do
  let opc := ← BitVec.rand 2
  let op  := decode_op opc
  -- (FIXME) We want to avoid use of SP (i.e., register index
  -- 31) for AND ORR and EOR since our simulation framework doesn't
  -- work in such cases.
  let hi  := if op = LogicalImmType.ANDS then 31 else 30
  let (inst : Logical_imm_cls) :=
    { sf    := ← BitVec.rand 1,
      opc   := opc,
      N     := ← BitVec.rand 1,
      immr  := ← BitVec.rand 6,
      imms  := ← BitVec.rand 6,
      Rn    := ← BitVec.rand 5 (lo := 0) (hi := hi),
      Rd    := ← BitVec.rand 5 (lo := 0) (hi := hi)
    }
  let datasize := 32 <<< inst.sf.toNat
  if inst.sf = 0#1 ∧ inst.N = 1#1 ∨ invalid_bit_masks inst.N inst.imms true datasize then
    Logical_imm_cls.rand
  else
    pure (some (inst.toBitVec32))

end DPI
