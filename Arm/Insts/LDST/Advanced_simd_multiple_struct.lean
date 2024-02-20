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

structure Multiple_struct_inst_fields where
  Q       : BitVec 1
  L       : BitVec 1
  Rm      : Option (BitVec 5) := none
  opcode  : BitVec 4
  size    : BitVec 2
  Rn      : BitVec 5
  Rt      : BitVec 5
deriving DecidableEq, Repr

@[simp]
def ld1_st1_operation (wback : Bool) (inst : Multiple_struct_inst_fields)
  (inst_str : String) (s : ArmState)
  (H_opcode : inst.opcode ∈
              [0b0000#4, 0b0010#4, 0b0100#4, 0b0110#4, 0b0111#4,
              0b1000#4, 0b1010#4])
  : ArmState :=
  let datasize := if inst.Q = 1#1 then 128 else 64
  have H : 8 ∣ datasize := by simp [datasize]; split <;> decide
  let datasize_bytes := datasize / 8
  let t  := inst.Rt
  let t2 := t + 1
  let t3 := t + 2
  let t4 := t + 3
  let (rpt, selem) :=
  match inst.opcode with
    | 0b0000#4 => (1, 4) -- LD/ST4: 4 registers
    | 0b0010#4 => (4, 1) -- LD/ST1: 4 registers
    | 0b0100#4 => (1, 3) -- LD/ST3: 3 registers
    | 0b0110#4 => (3, 1) -- LD/ST1: 3 registers
    | 0b0111#4 => (1, 1) -- LD/ST1: 1 register
    | 0b1000#4 => (1, 2) -- LD/ST2: 2 registers
    | _        => (2, 1) -- LD/ST1: 2 registers (opcode: 0b1010#4)
  if inst.size = 0b11#2 && datasize = 64 && selem ≠ 1 then
    write_err (StateError.Illegal s!"Illegal instruction {inst_str} encountered!") s
  else
    let address := read_gpr 64 inst.Rn s
    if inst.Rn == 31#5 && not (CheckSPAlignment s) then
      write_err (StateError.Fault s!"[Inst: {inst_str}] SP {address} is not aligned!") s
    else
      have h : datasize / 8 * 8 = datasize := by
        exact Nat.div_mul_cancel H
      let (offs, s) :=
      match (rpt, selem) with
        | (1, 1) => -- one register
          if inst.L = 1#1 then -- LD1
            let data := h ▸ read_mem_bytes datasize_bytes address s
            let s := write_sfp datasize t data s
            (datasize_bytes, s)
          else -- ST1
            let data := h.symm ▸ read_sfp datasize t s
            let s := write_mem_bytes datasize_bytes address data s
            (datasize_bytes, s)
        | (2, 1) => -- two registers
          if inst.L = 1#1 then -- LD1
            let data1 := h ▸ read_mem_bytes datasize_bytes address s
            let data2 := h ▸ read_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 datasize_bytes)) s
            let s := write_sfp datasize t data1 s
            let s := write_sfp datasize t2 data2 s
            (2 * datasize_bytes, s)
          else -- ST1
            let data1 := h.symm ▸ read_sfp datasize t s
            let data2 := h.symm ▸ read_sfp datasize t2 s
            let s := write_mem_bytes datasize_bytes address data1 s
            let s := write_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 datasize_bytes)) data2 s
            (2 * datasize_bytes, s)
        | (3, 1) => -- three registers
          if inst.L = 1#1 then -- LD1
            let data1 := h ▸ read_mem_bytes datasize_bytes address s
            let data2 := h ▸ read_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 datasize_bytes)) s
            let data3 := h ▸ read_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 (2 * datasize_bytes))) s
            let s := write_sfp datasize t data1 s
            let s := write_sfp datasize t2 data2 s
            let s := write_sfp datasize t3 data3 s
            (3 * datasize_bytes, s)
          else -- ST1
            let data1 := h.symm ▸ read_sfp datasize t s
            let data2 := h.symm ▸ read_sfp datasize t2 s
            let data3 := h.symm ▸ read_sfp datasize t3 s
            let s := write_mem_bytes datasize_bytes address data1 s
            let s := write_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 datasize_bytes)) data2 s
            let s := write_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 (2 * datasize_bytes))) data3 s
            (3 * datasize_bytes, s)
        | _ => -- four registers
          if inst.L = 1#1 then -- LD1
            let data1 := h ▸ read_mem_bytes datasize_bytes address s
            let data2 := h ▸ read_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 datasize_bytes)) s
            let data3 := h ▸ read_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 (2 * datasize_bytes))) s
            let data4 := h ▸ read_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 (3 * datasize_bytes))) s
            let s := write_sfp datasize t data1 s
            let s := write_sfp datasize t2 data2 s
            let s := write_sfp datasize t3 data3 s
            let s := write_sfp datasize t4 data4 s
            (4 * datasize_bytes, s)
          else -- ST1
            let data1 := h.symm ▸ read_sfp datasize t s
            let data2 := h.symm ▸ read_sfp datasize t2 s
            let data3 := h.symm ▸ read_sfp datasize t3 s
            let data4 := h.symm ▸ read_sfp datasize t4 s
            let s := write_mem_bytes datasize_bytes address data1 s
            let s := write_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 datasize_bytes)) data2 s
            let s := write_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 (2 * datasize_bytes))) data3 s
            let s := write_mem_bytes datasize_bytes (address + (Std.BitVec.ofNat 64 (3 * datasize_bytes))) data4 s
            (4 * datasize_bytes, s)
      let offs := if wback && not (inst.Rm == some 31#5) then
                     read_gpr 64 (Option.getD inst.Rm 0#5) s
                  else
                    Std.BitVec.ofNat 64 offs
      let address := address + offs
      let s := if wback then write_gpr 64 inst.Rn address s else s
      let s := write_pc ((read_pc s) + 4#64) s
      s

@[simp]
def exec_advanced_simd_multiple_struct
  (inst : Advanced_simd_multiple_struct_cls) (s : ArmState) : ArmState :=
  open Std.BitVec in
  match h₀: inst.opcode with
    | 0b0010#4 | 0b0110#4 | 0b0111#4 | 0b1010#4 =>
      ld1_st1_operation false
        {Q := inst.Q, L := inst.L, opcode := inst.opcode,
         size := inst.size, Rn := inst.Rn, Rt := inst.Rt }
        s!"{inst}" s
        (by simp_all only [List.mem_cons]; decide)
    | _ =>
      write_err
        (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!")
      s

@[simp]
def exec_advanced_simd_multiple_struct_post_indexed
  (inst : Advanced_simd_multiple_struct_post_indexed_cls) (s : ArmState) : ArmState :=
  open Std.BitVec in
  match h₀ : inst.opcode with
    | 0b0010#4 | 0b0110#4 | 0b0111#4 | 0b1010#4 =>
      ld1_st1_operation true
        {Q := inst.Q, L := inst.L, Rm := inst.Rm, opcode := inst.opcode,
         size := inst.size, Rn := inst.Rn, Rt := inst.Rt }
        s!"{inst}" s
        (by simp_all only [List.mem_cons]; decide)
    | _ =>
      write_err
        (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!")
      s
