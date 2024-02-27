/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- FMOV (general)

import Arm.Decode
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open BitVec

@[simp]
def fmov_general_aux (intsize : Nat) (fltsize : Nat) (op : FPConvOp)
  (part : Nat) (inst : Conversion_between_FP_and_Int_cls) (s : ArmState)
  (H : 0 < fltsize)
  : ArmState :=
  -- Assume CheckFPEnabled64()
  match op with
  | FPConvOp.FPConvOp_MOV_FtoI =>
    let fltval := Vpart_read inst.Rn part fltsize s H
    let intval := zeroExtend intsize fltval
    -- State Update
    let s := write_gpr intsize inst.Rd intval s
    let s := write_pc ((read_pc s) + 4#64) s
    s
  | FPConvOp.FPConvOp_MOV_ItoF =>
    let intval := read_gpr intsize inst.Rn s
    let fltval := extractLsb (fltsize - 1) 0 intval
    -- State Update
    have h₀ : fltsize - 1 - 0 + 1 = fltsize := by omega
    let s := Vpart_write inst.Rd part fltsize (h₀ ▸ fltval) s
    let s := write_pc ((read_pc s) + 4#64) s
    s
  | _ => write_err (StateError.Other s!"fmov_general_aux called with non-FMOV op!") s

@[simp]
def exec_fmov_general
  (inst : Conversion_between_FP_and_Int_cls) (s : ArmState): ArmState :=
  let intsize := 32 <<< inst.sf.toNat
  let decode_fltsize := if inst.ftype == 0b10#2 then 64 else (8 <<< (inst.ftype ^^^ 0b10#2).toNat)
  have H: 0 < decode_fltsize := by
    simp only [decode_fltsize, beq_iff_eq]
    split
    · decide
    · generalize BitVec.toNat (inst.ftype ^^^ 2#2) = x
      apply zero_lt_shift_left_pos (by decide)
  match (extractLsb 2 1 inst.opcode) ++ inst.rmode with
  | 1100 =>  -- FMOV
    if decode_fltsize != 16 && decode_fltsize != intsize then
      write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    else
      let op := if extractLsb 0 0 inst.opcode == 1
                then FPConvOp.FPConvOp_MOV_ItoF
                else FPConvOp.FPConvOp_MOV_FtoI
      let part := 0
      fmov_general_aux intsize decode_fltsize op part inst s H
  | 1101 => -- FMOV D[1]
    if intsize != 64 || inst.ftype != 0b10#2 then
      write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    else
      let op := if extractLsb 0 0 inst.opcode == 1
                then FPConvOp.FPConvOp_MOV_ItoF
                else FPConvOp.FPConvOp_MOV_FtoI
      let part := 1
      fmov_general_aux intsize decode_fltsize op part inst s H
    | _ => write_err (StateError.Other s!"exec_fmov_general called with non-FMOV instructions!") s

@[simp]
def exec_conversion_between_FP_and_Int
  (inst : Conversion_between_FP_and_Int_cls) (s : ArmState) : ArmState :=
  if inst.ftype == 0b10#2 && (extractLsb 2 1 inst.opcode) ++ inst.rmode != 0b1101#4 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    -- Assume IsFeatureImplemented(FEAT_FP16) is true
  else
    match_bv inst.sf ++ inst.S ++ inst.ftype ++ inst.rmode ++ inst.opcode with
    | [_sf:1, 0, _ftype:2, 0, _rmode0:1, 11, _opcode0:1] => exec_fmov_general inst s
    | _ => write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

----------------------------------------------------------------------

partial def Conversion_between_FP_and_Int_cls.fmov_general.rand : IO (Option (BitVec 32)) := do
  let ftype := ← BitVec.rand 2
  let rmode := ← (0b0#1 ++ ·) <$> BitVec.rand 1
  let opcode := ← (0b11#2++ ·) <$> BitVec.rand 1
  let sf := ← BitVec.rand 1
  let intsize := 32 <<< sf.toNat
  let decode_fltsize := if ftype == 0b10#2 then 64 else (8 <<< (ftype ^^^ 0b10#2).toNat)
  if ftype == 0b10#2 && (extractLsb 2 1 opcode) ++ rmode != 0b1101#4
  || decode_fltsize != 16 && decode_fltsize != intsize
  || intsize != 64 || ftype != 0b10#2 then
    Conversion_between_FP_and_Int_cls.fmov_general.rand
  else
    let (inst : Conversion_between_FP_and_Int_cls) :=
      { sf := sf,
        S := 0b0#1,
        ftype := ftype,
        rmode  := rmode,
        opcode := opcode,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5 }
    pure (inst.toBitVec32)

/-- Generate random instructions of Conversion_between_FP_and_Int class. -/
def Conversion_between_FP_and_Int_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Conversion_between_FP_and_Int_cls.fmov_general.rand ]

end DPSFP
