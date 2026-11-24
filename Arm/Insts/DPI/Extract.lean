/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Boris Nagaev
-/

-- EXTR: 32- and 64-bit versions (aliased as ROR (immediate) when Rn = Rm)

import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

namespace DPI

open BitVec

/-- EXTR (Arm ARM C6.2.126): `Rd = (Rn:Rm)<lsb+datasize-1:lsb>` with `lsb = imms`. -/
@[state_simp_rules]
def exec_extract (inst : Extract_cls) (s : ArmState) : ArmState :=
  if inst.op21 ≠ 0b00#2 ∨ inst.o0 ≠ 0b0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.N ≠ inst.sf ∨ (inst.sf = 0b0#1 ∧ lsb inst.imms 5 ≠ 0b0#1) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := if inst.sf = 1#1 then 64 else 32
    let operand1 := read_gpr_zr datasize inst.Rn s
    let operand2 := read_gpr_zr datasize inst.Rm s
    let concat := operand1 ++ operand2
    let result : BitVec datasize := concat.extractLsb' inst.imms.toNat datasize
    let s := write_gpr_zr datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

----------------------------------------------------------------------

/-- Generate random legal EXTR instructions. -/
def Extract_cls.extr.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let sf ← BitVec.rand 1
  let hi ← BitVec.rand 1
  let lo ← BitVec.rand 5
  -- 32-bit EXTR requires imms<5> = 0.
  let imms := (if sf = 1#1 then hi else 0#1) ++ lo
  let inst : Extract_cls :=
    { sf    := sf,
      op21  := 0b00#2,
      N     := sf,
      o0    := 0b0#1,
      Rm    := ← GPRIndex.rand,
      imms  := imms,
      Rn    := ← GPRIndex.rand,
      Rd    := ← GPRIndex.rand }
  pure (some inst.toBitVec32)

/-- List of functions to generate random instructions of the DPI.Extract class. -/
def Extract_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [Extract_cls.extr.rand]

end DPI
