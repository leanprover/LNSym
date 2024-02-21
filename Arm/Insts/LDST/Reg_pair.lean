/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
-- LDP, STP (pre-index, post-index and signed offset, GPR and SIMD&FP)

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace LDST

open Std.BitVec

structure Reg_pair_cls where
  opc       : BitVec 2
  SIMD?     : Bool
  L?        : Bool
  wback     : Bool
  postindex : Bool
  imm7      : BitVec 7
  Rt2       : BitVec 5
  Rn        : BitVec 5
  Rt        : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_pair_cls where toString a := toString (repr a)

@[simp]
def reg_pair_constrain_unpredictable (wback : Bool) (inst : Reg_pair_cls) : Bool :=
  match inst.SIMD?, inst.L? with
  | false, false => wback && ((inst.Rt == inst.Rn) || inst.Rt2 == inst.Rn) && inst.Rn != 31#5
  | false, true => (wback && ((inst.Rt == inst.Rn) || inst.Rt2 == inst.Rn) && inst.Rn != 31#5 )
                || (inst.Rt == inst.Rt2)
  | true, false => false
  | true, true => inst.Rt == inst.Rt2

@[simp]
def reg_pair_operation (inst : Reg_pair_cls) (inst_str : String) (signed : Bool)
  (datasize : Nat) (offset : BitVec 64) (s : ArmState)
  (H1 : 8 ∣ datasize) (H2 : 0 < datasize) : ArmState :=
  -- Note: we do not need to model the ASL function
  -- "CreateAccDescGPR" here, given the simplicity of our memory
  -- model
  let address := read_gpr 64 inst.Rn s
  if inst.Rn == 31#5 && not (CheckSPAlignment s) then
    write_err (StateError.Fault s!"[Inst: {inst_str}] SP {address} is not aligned!") s
  else
    let address := if inst.postindex then address else address + offset
    let s :=
      match inst.L? with
      | false => -- STORE
        have h1 : datasize / 8 * 8 = datasize := by
          exact Nat.div_mul_cancel H1
        have h2 : datasize + datasize = 2 * datasize := by
          simp_arith
        have h3 : (2 * (datasize / 8) * 8) = datasize + datasize := by
          rw [Nat.mul_assoc, h1, h2]
        let data1 := ldst_read inst.SIMD? datasize inst.Rt s
        let data2 := ldst_read inst.SIMD? datasize inst.Rt2 s
        -- (FIXME): Implement and check HaveLSE2Ext and BigEndian features.
        let full_data := data2 ++ data1
        write_mem_bytes (2 * (datasize / 8)) address (h3 ▸ full_data) s
      | _ => -- LOAD
        have h4 : datasize - 1 - 0 + 1 = datasize := by
          simp; apply Nat.sub_add_cancel H2
        have H2': 1 <= datasize := by trivial
        have h5 : 2 * datasize - 1 - datasize + 1 = datasize := by
          rw [Nat.add_mul 1 1 datasize]; simp
          rw [Nat.add_sub_assoc H2']
          rw [Nat.add_sub_self_left datasize (datasize - 1)]
          rw [Nat.sub_add_cancel]
          trivial
        let full_data := read_mem_bytes (2 * (datasize / 8)) address s
        let data1 := extractLsb (datasize - 1) 0 full_data
        let data2 := extractLsb ((2 * datasize) - 1) datasize full_data
        if not inst.SIMD? && signed then
          let s := write_gpr 64 inst.Rt (signExtend 64 data1) s
          write_gpr 64 inst.Rt2 (signExtend 64 data2) s
        else
          let s:= ldst_write inst.SIMD? datasize inst.Rt (h4 ▸ data1) s
          ldst_write inst.SIMD? datasize inst.Rt2 (h5 ▸ data2) s
    if inst.wback then
      let address := if inst.postindex then address + offset else address
      write_gpr 64 inst.Rn address s
    else
      s

@[simp]
def exec_reg_pair_common (inst : Reg_pair_cls) (inst_str : String) (s : ArmState) : ArmState :=
  if -- UNDEFINED case for none-SIMD Reg Pair
     not inst.SIMD? &&
     ((not inst.L? && extractLsb 0 0 inst.opc == 1#1) || (inst.opc == 0b11#2))
     -- UNDEFINED case for SIMD Reg Pair
     || inst.SIMD? && (inst.opc == 0b11#2)
     -- constrain unpredictable
     || reg_pair_constrain_unpredictable inst.wback inst
  then
    write_err (StateError.Illegal "Illegal instruction {inst_str} encountered!") s
  else
    let signed := (extractLsb 0 0 inst.opc) != 0#1
    let scale := if not inst.SIMD?
                 then 2 + (Std.BitVec.toNat (extractLsb 1 1 inst.opc))
                 else 2 + (Std.BitVec.toNat inst.opc)
    have H0 : scale > 0 := by simp_all!; split <;> simp
    let datasize := 8 <<< scale
    let offset := (signExtend 64 inst.imm7) <<< scale
    have H1 : 8 ∣ datasize := by
      simp_all! only [gt_iff_lt, Nat.shiftLeft_eq, dvd_mul_right]
    have H2 : datasize > 0 := by
      simp_all! only [Nat.shiftLeft_eq, dvd_mul_right]
      generalize (if (!inst.SIMD?) = true
                  then 2 + Std.BitVec.toNat (extractLsb 1 1 inst.opc)
                  else 2 + Std.BitVec.toNat inst.opc) = x
      have hb : 2 ^ x > 0 := by exact Nat.pow_two_pos x
      exact Nat.mul_pos (by decide) hb
    -- State Updates
    let s' := reg_pair_operation inst inst_str signed datasize offset s H1 H2
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'

@[simp]
def exec_reg_pair_pre_indexed
  (inst : Reg_pair_pre_indexed_cls) (s : ArmState) : ArmState :=
  let (extracted_inst : Reg_pair_cls) :=
    { opc := inst.opc
    , SIMD? := inst.V == 1#1
    , L? := inst.L == 1#1
    , wback := true
    , postindex := false
    , imm7 := inst.imm7
    , Rt2 := inst.Rt2
    , Rn := inst.Rn
    , Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s

@[simp]
def exec_reg_pair_post_indexed
  (inst : Reg_pair_post_indexed_cls) (s : ArmState) : ArmState :=
  let (extracted_inst : Reg_pair_cls) :=
    { opc := inst.opc,
      SIMD? := inst.V == 1#1,
      L? := inst.L == 1#1,
      wback := true,
      postindex := true,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s

@[simp]
def exec_reg_pair_signed_offset
  (inst : Reg_pair_signed_offset_cls) (s : ArmState) : ArmState :=
  let (extracted_inst : Reg_pair_cls) :=
    { opc := inst.opc,
      SIMD? := inst.V == 1#1,
      L? := inst.L == 1#1,
      wback := false,
      postindex := false,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s

end LDST
