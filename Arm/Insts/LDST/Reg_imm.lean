/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
-- LDR/STR (immediate, SIMD&FP)

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace LDST

open Std.BitVec

@[simp]
def reg_imm_operation (inst_str : String) (op : BitVec 1)
  (wback : Bool) (postindex : Bool) (datasize : Nat)
  (Rn : BitVec 5) (Rt : BitVec 5) (offset : BitVec 64)
  (s : ArmState)  (H : 8 ∣ datasize) : ArmState :=
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
        let data := read_sfp datasize Rt s
        write_mem_bytes (datasize / 8) address (h.symm ▸ data) s
      | _ => -- LOAD
        let data := read_mem_bytes (datasize / 8) address s
        write_sfp datasize Rt (h.symm ▸ data) s
    if wback then
      let address := if postindex then address + offset else address
      write_gpr 64 Rn address s
    else
      s

@[simp]
def exec_reg_unsigned_imm
  (inst : Reg_unsigned_imm_cls) (s : ArmState) : ArmState :=
  -- Decoding for all variants for post-indexed encoding:
  let wback := false
  let postindex := false
  have h_scale : (1 - 1 + 1 + 2) = 3 := by decide
  let scale := (BitVec.extract inst.opc 1 1) ++ inst.size
  let scale := (h_scale ▸ scale)
  -- (FIXME) Why can't I use scale > 4#3 here?
  if Std.BitVec.ult 4#3 scale then
    write_err (StateError.Illegal "Illegal instruction {inst} encountered!") s
  else
    let offset := (Std.BitVec.zeroExtend 64 inst.imm12) <<< scale.toNat
    let datasize := 8 <<< scale.toNat
    have H : 8 ∣ datasize := by
      simp_all! only [Nat.shiftLeft_eq, dvd_mul_right]
    -- State Updates
    let s' := reg_imm_operation s!"{inst}"
              (BitVec.extract inst.opc 0 0) wback postindex datasize
              inst.Rn inst.Rt offset
              s (H)
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'

@[simp]
def exec_reg_imm_post_indexed
  (inst : Reg_imm_post_indexed_cls) (s : ArmState) : ArmState :=
  -- Decoding for all variants for post-indexed encoding:
  open Std.BitVec in
  let wback := true
  let postindex := true
  let scale := (BitVec.extract inst.opc 1 1) ++ inst.size
  -- (FIXME) Why can't I use scale > 4#3 here?
  if Std.BitVec.ult 4#3 scale then
    write_err (StateError.Illegal "Illegal instruction {inst} encountered!") s
  else
    let datasize := 8 <<< scale.toNat
    let offset := signExtend 64 inst.imm9
    have H : 8 ∣ datasize := by
      simp_all! only [Nat.shiftLeft_eq, dvd_mul_right]
    -- State Updates
    let s' := reg_imm_operation s!"{inst}"
              (BitVec.extract inst.opc 0 0) wback postindex datasize
              inst.Rn inst.Rt offset
              s (H)
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'

end LDST
