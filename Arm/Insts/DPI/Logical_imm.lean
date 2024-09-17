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

@[lnsimp, state_simp_rules]
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

@[lnsimp, state_simp_rules]
def exec_logical_imm_op (op : LogicalImmType) (op1 : BitVec n) (op2 : BitVec n)
  : (BitVec n × Option PState) :=
  match op with
  | LogicalImmType.AND => (op1 &&& op2, none)
  | LogicalImmType.ORR => (op1 ||| op2, none)
  | LogicalImmType.EOR => (op1 ^^^ op2, none)
  | LogicalImmType.ANDS =>
    let result := op1 &&& op2
    (op1 &&& op2, some (update_logical_imm_pstate result))

/--
Return `TRUE` if a bitmask immediate encoding would generate an
immediate value that could also be represented by a single `MOVZ` or
`MOVN` instruction.  Used as a condition for the preferred `MOV<-ORR`
alias.

Source:
https://developer.arm.com/documentation/ddi0602/2023-03/Shared-Pseudocode/aarch64-functions-movwpreferred?lang=en#impl-aarch64.MoveWidePreferred.4
-/
@[lnsimp, state_simp_rules]
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

/--
Instruction semantics for `Logical_imm_cls` instructions
`AND, ORR, EOR, ANDS (immediate): 32- and 64-bit versions`.

Note that `ORR` and `ANDS` have aliases, as follows:

```
MOV <Wd|WSP>, #<imm> / MOV <Xd|SP>, #<imm>
```
is equivalent to
`ORR <Wd|WSP>, WZR, #<imm> / ORR <Xd|SP>, XZR, #<imm>`
and
`TST <Wn>, #<imm> / TST <Xn>, #<imm>`
is equivalent to
`ANDS WZR, <Wn>, #<imm> / ANDS XZR, <Xn>, #<imm>`

Sources:
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/ANDS--immediate---Bitwise-AND--immediate---setting-flags-?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/TST--immediate---Test-bits--immediate---an-alias-of-ANDS--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/ORR--immediate---Bitwise-OR--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/MOV--bitmask-immediate---Move--bitmask-immediate---an-alias-of-ORR--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/EOR--immediate---Bitwise-Exclusive-OR--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/AND--immediate---Bitwise-AND--immediate--?lang=en
-/
@[lnsimp, state_simp_rules]
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
      let operand1 :=
        match op with
        | .ORR =>
          -- (TODO): a `dsimproc` for MoveWidePreferred?
          if  ¬ MoveWidePreferred inst.sf inst.N inst.imms inst.immr then
             -- MOV (bitmask immediate) is an alias of ORR when
             -- Rd == '11111' and Move Wide is not preferred.
             read_gpr_zr datasize inst.Rn s
          else
            read_gpr datasize inst.Rn s
        | _ => read_gpr datasize inst.Rn s
      let (result, maybe_pstate) := exec_logical_imm_op op operand1 imm
      -- State Updates
      let s'            := write_pc ((read_pc s) + 4#64) s
      let s'            := match maybe_pstate with
                           | none => s'
                           | some pstate => write_pstate pstate s'
      let s'            := match op with
                           | .ANDS =>
                              -- TST (immediate) is an alias of ANDS when
                              -- Rd == '11111'.
                              write_gpr_zr datasize inst.Rd result s'
                           | _ => write_gpr datasize inst.Rd result s'
      s'

----------------------------------------------------------------------

/-- Generate random instructions of the DPI.Logical_imm class. -/
partial def Logical_imm_cls.inst.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let sf ← BitVec.rand 1
  let N ← BitVec.rand 1
  let imms ← BitVec.rand 6
  let datasize := 32 <<< sf.toNat
  if sf = 0#1 ∧ N = 1#1 ∨ invalid_bit_masks N imms true datasize then
    -- Try again to generate a legal instruction of this class.
    Logical_imm_cls.inst.rand
  else
    let immr ← BitVec.rand 6
    let opc ← BitVec.rand 2
    let op := decode_op opc
    -- (FIXME) We do not want to read from or write to SP (GPR index 31) since
    -- our cosimulation framework does not account for effects to SP. However,
    -- we do want to use GPR index 31 when the semantics dictate that it be
    -- treated as ZR.
    let Rn_hi := if (op == .ORR ∧ ! MoveWidePreferred sf N imms immr) then 31 else 30
    let Rd_hi := if (op == .ANDS) then 31 else 30
    let (inst : Logical_imm_cls) :=
      { sf    := sf,
        opc   := opc,
        N     := N,
        immr  := immr,
        imms  := imms,
        Rn    := ← GPRIndex.rand (lo := 0) (hi := Rn_hi),
        Rd    := ← GPRIndex.rand (lo := 0) (hi := Rd_hi)
      }
    pure (some (inst.toBitVec32))

def Logical_imm_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [ Logical_imm_cls.inst.rand ]

end DPI
