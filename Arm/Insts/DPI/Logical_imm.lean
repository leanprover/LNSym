/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- AND, ORR, EOR, ANDS (immediate): 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

namespace DPI

open BitVec

@[state_simp_rules]
def decode_op (opc : BitVec 2) : LogicalImmType :=
  match opc with
  | 00#2 => LogicalImmType.AND
  | 01#2 => LogicalImmType.ORR
  | 10#2 => LogicalImmType.EOR
  | 11#2 => LogicalImmType.ANDS

def update_logical_imm_pstate (bv : BitVec n) : PState :=
  let N : BitVec 1 := BitVec.lsb bv (n-1)
  let Z := zero_flag_spec bv
  let C := 0#1
  let V := 0#1
  (make_pstate N Z C V)

@[state_simp_rules]
def exec_logical_imm_op (op : LogicalImmType) (op1 : BitVec n) (op2 : BitVec n)
  : (BitVec n × Option PState) :=
  match op with
  | LogicalImmType.AND => (op1 &&& op2, none)
  | LogicalImmType.ORR => (op1 ||| op2, none)
  | LogicalImmType.EOR => (op1 ^^^ op2, none)
  | LogicalImmType.ANDS =>
    let result := op1 &&& op2
    (op1 &&& op2, some (update_logical_imm_pstate result))

/-!
Return `TRUE` if a bitmask immediate encoding would generate an
immediate value that could also be represented by a single `MOVZ` or
`MOVN` instruction.  Used as a condition for the preferred `MOV<-ORR`
alias.

Source:
https://developer.arm.com/documentation/ddi0602/2023-03/Shared-Pseudocode/aarch64-functions-movwpreferred?lang=en#impl-aarch64.MoveWidePreferred.4
-/
@[state_simp_rules]
def MoveWidePreferred (sf immN : BitVec 1) (imms immr : BitVec 6) : Bool :=
    -- NOTE: we need s and r to be integers, and not nats, because we
    -- perform int modulo operations here (see (0 - r % 16)).
    let s := imms.toInt
    let r := immr.toInt
    let width := if sf = 1#1 then 64 else 32

    -- element size must equal total immediate size
    -- NOTE: the second disjunct below is semantically equivalent to the ASL code
    -- !((immN:imms) IN {'1xxxxxx'})
    if sf = 1#1 ∧ immN ≠ 1#1 then
      false
    -- NOTE: the second conjunct below is semantically equivalent to the ASL code
    -- !((immN:imms) IN {'00xxxxx'})
    else if sf = 0#1 ∧ ¬(immN = 0#1 ∧ imms.extractLsb 5 5 = 0#1) then
      false

    -- for MOVZ must contain no more than 16 ones
    else if s < 16 then
        -- ones must not span halfword boundary when rotated
     let r' := (0 - r) % 16
     let s' := 15 - s
     r' <= s'

    -- for MOVN must contain no more than 16 zeros
    else if s >= width - 15 then
        -- zeros must not span halfword boundary when rotated
        let r' := r % 16
        let s' := s - (width - 15)
        r' <= s'
    else
      false

@[state_simp_rules]
def exec_logical_imm (inst : Logical_imm_cls) (s : ArmState) : ArmState :=
  if inst.sf = 0#1 ∧ inst.N ≠ 0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let imm := decode_bit_masks inst.N inst.imms inst.immr true datasize
    match imm with
    | none => write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    | some (imm, _) =>
      let op := decode_op inst.opc
      let operand1 := read_gpr datasize inst.Rn s
      let operand1 :=
        match op with
        | .ORR =>
          if inst.Rn = 31#5 ∧
            -- (TODO): a `dsimproc` for MoveWidePreferred?
             ¬ MoveWidePreferred inst.sf inst.N inst.imms inst.immr then
             BitVec.zero datasize
          else
            operand1
        | _ => operand1
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
partial def Logical_imm_cls.inst.rand : Cosim.CosimM (Option (BitVec 32)) := do
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
      Rn    := ← GPRIndex.rand (lo := 0) (hi := hi),
      Rd    := ← GPRIndex.rand (lo := 0) (hi := hi)
    }
  let datasize := 32 <<< inst.sf.toNat
  if inst.sf = 0#1 ∧ inst.N = 1#1 ∨ invalid_bit_masks inst.N inst.imms true datasize then
    Logical_imm_cls.inst.rand
  else
    pure (some (inst.toBitVec32))

def Logical_imm_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [ Logical_imm_cls.inst.rand ]

end DPI
