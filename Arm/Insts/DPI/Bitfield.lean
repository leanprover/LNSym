/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Nevine
-/
-- For now, support only UBFM (immediate) aliased as LSR (immediate):
-- 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common

namespace DPI

open Std.BitVec

@[simp]
def exec_bitfield (inst: Bitfield_cls) (s : ArmState) : ArmState :=
  -- TODO: match opc
  let immr5 := inst.immr >>> 5
  let imms5 := inst.imms >>> 5
  if (inst.sf == 1 && inst.N != 1) ||
     (inst.sf == 0 && (inst.N != 0 || immr5 != 0 || imms5 != 0)) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize  := if inst.sf == 1#1 then 64 else 32
    let wtmask    := decode_bit_masks inst.N inst.imms inst.immr false datasize
    match wtmask with
    | none => write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    | some (wmask, tmask) =>
      let src := read_gpr datasize inst.Rn s
      let bot := (BitVec.ror src inst.immr.toNat) &&& wmask
      let result := bot &&& tmask
      let s := write_gpr datasize inst.Rd result s
      let s := write_pc ((read_pc s) + 4#64) s
      s


----------------------------------------------------------------------

/-- Generate random instructions of the DPI.Bitfield class. -/
partial def bitfield_rand_aux (sf : BitVec 1) (N : BitVec 1) (immr : BitVec 6) (imms : BitVec 6) :
IO (Option (BitVec 32)) := do
  if sf == 1 && N != 1 then
    let N := 0b1#1
    bitfield_rand_aux sf N immr imms
  else if sf == 0 && (N != 0 || extractLsb 5 5 immr != 0 || extractLsb 5 5 imms != 0) then
    let sf := ← BitVec.rand 1
    let N := sf
    let immr := sf ++ (← BitVec.rand 5)
    let imms := sf ++ (← BitVec.rand 5)
    bitfield_rand_aux sf N immr imms
  else
  let (inst : Bitfield_cls) :=
    { sf    := sf,
      opc   := ← pure 0b10#2,
      N     := N,
      immr  := immr,
      imms  := imms,
       -- TODO: Do we need to limit Rn and Rd to be up to 30 as in Add_sub_imm?
      Rn    := ← BitVec.rand 5,
      Rd    := ← BitVec.rand 5 }
  pure (some (inst.toBitVec32))

partial def Bitfield_cls.ubfm.rand : IO (Option (BitVec 32)) := do
  let sf := ← BitVec.rand 1
  let N := ← BitVec.rand 1
  let immr := ← BitVec.rand 6
  let imms := ← BitVec.rand 6
  bitfield_rand_aux sf N immr imms

partial def Bitfield_cls.lsr.rand : IO (Option (BitVec 32)) := do
  let N := ← BitVec.rand 1
  let sf := N
  let immr := ← BitVec.rand 6
  let imms := N <<< 5 ++ 0b11111#5
  bitfield_rand_aux sf N immr imms

def Bitfield_cls.rand : List (IO (Option (BitVec 32))) :=
  [Bitfield_cls.lsr.rand,
   Bitfield_cls.ubfm.rand]
----------------------------------------------------------------------

end DPI
