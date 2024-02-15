/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- LDP, STP

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace LDST

open Std.BitVec

@[simp]
def reg_pair_scalar_operation (inst_str : String) (load_op : BitVec 1)
  (wback : Bool) (postindex : Bool) (signed : Bool)
  (datasize : Nat)
  (Rn : BitVec 5) (Rt : BitVec 5) (Rt2 : BitVec 5) (offset : BitVec 64)
  (s : ArmState)  (H1 : 8 ∣ datasize) (H2 : 0 < datasize) : ArmState :=
  let address := read_gpr 64 Rn s
  if Rn == 31#5 && not (CheckSPAlignment s) then
      write_err (StateError.Fault s!"[Inst: {inst_str}] SP {address} is not aligned!") s
      -- Note: we do not need to model the ASL function
      -- "CreateAccDescGPR" here, given the simplicity of our memory
      -- model
  else
    let address := if postindex then address else address + offset
    let s :=
      match load_op with
      | 0#1 => -- STORE
        have h1 : datasize / 8 * 8 = datasize := by
          exact Nat.div_mul_cancel H1
        have h2 : datasize + datasize = 2 * datasize := by
          simp_arith
        have h3 : (2 * (datasize / 8) * 8) = datasize + datasize := by
          rw [Nat.mul_assoc, h1, h2]
        let data1 := read_sfp datasize Rt s
        let data2 := read_sfp datasize Rt2 s
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
        if signed then
          let s := write_gpr 64 Rt (signExtend 64 data1) s
          write_gpr 64 Rt2 (signExtend 64 data2) s
        else
          let s:= write_gpr datasize Rt (h4 ▸ data1) s
          write_gpr datasize Rt2 (h5 ▸ data2) s
    if wback then
      let address := if postindex then address + offset else address
      write_gpr 64 Rn address s
    else
      s

@[simp]
def exec_reg_pair_pre_indexed
  (inst : Reg_pair_pre_indexed_cls) (s : ArmState) : ArmState :=
  -- Decoding for all variants for pre-indexed encoding:
  open Std.BitVec in
  let wback := true
  let postindex := false
  let signed := (extractLsb 0 0 inst.opc) != 0#1
  let scale := 2 + (Std.BitVec.toNat (extractLsb 1 1 inst.opc))
  have H0 : scale > 0 := by omega
  if (inst.L == 0#1 && extractLsb 0 0 inst.opc == 1#1) || (inst.opc == 0b11#2) then
    write_err (StateError.Illegal "Illegal instruction {inst} encountered!") s
  else
    let datasize := 8 <<< scale
    let offset := (signExtend 64 inst.imm7) <<< scale
    have H1 : 8 ∣ datasize := by
      simp_all! only [gt_iff_lt, Nat.shiftLeft_eq, Nat.dvd_mul_right]
    have H2 : datasize > 0 := by
      simp_all! only [Nat.shiftLeft_eq, Nat.dvd_mul_right]
      generalize (2 + Std.BitVec.toNat (extractLsb 1 1 inst.opc)) = x
      have hb : 2 ^ x > 0 := by exact Nat.two_pow_pos x
      exact Nat.mul_pos (by decide) hb
    -- State Updates
    let s' := reg_pair_scalar_operation s!"{inst}" inst.L wback postindex signed
              datasize inst.Rn inst.Rt inst.Rt2 offset s (H1) (H2)
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'
