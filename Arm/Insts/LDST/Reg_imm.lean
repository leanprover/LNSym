/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
-- LDR/STR (immediate, post-indexed and unsigned offset, GPR and SIMD&FP)
-- LDRB/STRB (immediate, post-indexed and unsigned offset, GPR)

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace LDST

open BitVec

structure Reg_imm_cls where
  size      : BitVec 2
  opc       : BitVec 2
  Rn        : BitVec 5
  Rt        : BitVec 5
  SIMD?     : Bool
  wback     : Bool
  postindex : Bool
  imm       : BitVec 12 ⊕ (BitVec 9)
deriving DecidableEq, Repr

instance : ToString Reg_imm_cls where toString a := toString (repr a)

@[simp]
def reg_imm_operation (inst_str : String) (op : BitVec 1)
  (wback : Bool) (postindex : Bool) (SIMD? : Bool)
  (datasize : Nat) (regsize : Option Nat) (Rn : BitVec 5)
  (Rt : BitVec 5) (offset : BitVec 64) (s : ArmState)
  (H : 8 ∣ datasize) : ArmState :=
  let address := read_gpr 64 Rn s
  if Rn == 31#5 && not (CheckSPAlignment s) then
      write_err (StateError.Fault s!"[Inst: {inst_str}] SP {address} is not aligned!") s
      -- Note: we do not need to model the ASL function
      -- "CreateAccDescGPR" here, given the simplicity of our memory
      -- model
  else
    let address := if postindex then address else address + offset
    have h : datasize / 8 * 8 = datasize := by
      exact Nat.div_mul_cancel H
    let s :=
      match op with
      | 0#1 => -- STORE
        let data := ldst_read SIMD? datasize Rt s
        write_mem_bytes (datasize / 8) address (h.symm ▸ data) s
      | _ => -- LOAD
        let data := read_mem_bytes (datasize / 8) address s
        if SIMD? then write_sfp datasize Rt (h.symm ▸ data) s
        else write_gpr regsize.get! Rt (zeroExtend regsize.get! data) s
    if wback then
      let address := if postindex then address + offset else address
      write_gpr 64 Rn address s
    else
      s

@[simp]
def reg_imm_constrain_unpredictable (wback : Bool) (SIMD? : Bool) (Rn : BitVec 5)
  (Rt : BitVec 5) : Bool :=
  if SIMD? then false else wback && Rn == Rt && Rn != 31#5

@[simp]
def supported_reg_imm (size : BitVec 2) (opc : BitVec 2) (SIMD? : Bool) : Bool :=
  match size, opc, SIMD? with
  | 0b00#2, 0b00#2, false => true -- STRB, 32-bit, GPR
  | 0b00#2, 0b01#2, false => true -- LDRB, 32-bit, GPR
  | 0b10#2, 0b00#2, false => true -- STR, 32-bit, GPR
  | 0b10#2, 0b01#2, false => true -- LDR, 32-bit, GPR
  | 0b11#2, 0b00#2, false => true -- STR, 64-bit, GPR
  | 0b11#2, 0b01#2, false => true -- LDR, 64-bit, GPR
  | _, 0b00#2, true => true      -- STR, 8-bit, 16-bit, 32-bit, 64-bit, SIMD&FP
  | _, 0b01#2, true => true      -- LDR, 8-bit, 16-bit, 32-bit, 64-bit, SIMD&FP
  | 0b00#2, 0b10#2, true => true -- STR, 128-bit, SIMD&FP
  | 0b00#2, 0b11#2, true => true -- LDR, 128-bit, SIMD&FP
  | _, _, _ => false -- other instructions that are not supported or illegal

@[simp]
def exec_reg_imm_common
  (inst : Reg_imm_cls) (inst_str : String) (s : ArmState) : ArmState :=
  let scale :=
    if inst.SIMD? then ((extractLsb 1 1 inst.opc) ++ inst.size).toNat
    else inst.size.toNat
  -- Only allow supported LDST Reg immediate instructions
  if not $ supported_reg_imm inst.size inst.opc inst.SIMD? then
    write_err (StateError.Illegal "Unsupported or Illegal instruction {inst_str} encountered!") s
  -- UNDEFINED case in LDR/STR SIMD/FP instructions
  -- FIXME: prove that this branch condition is trivially false
  else if inst.SIMD? && scale > 4 then
    write_err (StateError.Illegal "Illegal instruction {inst_str} encountered!") s
  -- constrain unpredictable when GPR
  else if reg_imm_constrain_unpredictable inst.wback inst.SIMD? inst.Rn inst.Rt then
    write_err (StateError.Illegal "Illegal instruction {inst_str} encountered!") s
  else
    let offset := match inst.imm with
      | Sum.inl imm12 => (BitVec.zeroExtend 64 imm12) <<< scale
      | Sum.inr imm9 => signExtend 64 imm9
    let datasize := 8 <<< scale
    let regsize :=
      if inst.SIMD? then none
      else if inst.size == 0b11#2 then some 64 else some 32
    have H : 8 ∣ datasize := by
      simp_all! only [Nat.shiftLeft_eq, Nat.dvd_mul_right, datasize]
    -- State Updates
    let s' := reg_imm_operation inst_str
              (extractLsb 0 0 inst.opc) inst.wback inst.postindex
              inst.SIMD? datasize regsize inst.Rn inst.Rt offset s (H)
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'

@[simp]
def exec_reg_imm_unsigned_offset
  (inst : Reg_unsigned_imm_cls) (s : ArmState) : ArmState :=
  let (extracted_inst : Reg_imm_cls) :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := inst.V == 1#1,
      wback     := false,
      postindex := false,
      imm       := Sum.inl inst.imm12 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

@[simp]
def exec_reg_imm_post_indexed
  (inst : Reg_imm_post_indexed_cls) (s : ArmState) : ArmState :=
  let (extracted_inst : Reg_imm_cls) :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := inst.V == 1#1,
      wback     := true,
      postindex := true,
      imm       := Sum.inr inst.imm9 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

end LDST
