/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- DUP, INS, SMOV, UMOV

import Arm.Decode
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open BitVec

def dup_aux (e : Nat) (elements : Nat) (esize : Nat)
  (element : BitVec esize) (result : BitVec datasize) (H : 0 < esize) : BitVec datasize :=
  if h₀ : elements <= e then
    result
  else
    let lo := e * esize
    let hi := lo + esize -1
    have h₁ : hi - lo + 1 = esize := by simp [hi, lo]; omega
    let result := BitVec.partInstall hi lo (h₁ ▸ element) result
    have h : elements - (e + 1) < elements - e := by omega
    dup_aux (e + 1) elements esize element result H
  termination_by (elements - e)

def exec_dup_element (inst : Advanced_simd_copy_cls) (s : ArmState) : ArmState :=
  let size := lowest_set_bit inst.imm5
  if size > 3 || (size == 3 && inst.Q == 0) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let index := (extractLsb 4 (size + 1) inst.imm5).toNat
    let idxdsize := 64 <<< (extractLsb 4 4 inst.imm5).toNat
    let esize := 8 <<< size
    let datasize := 64 <<< inst.Q.toNat
    let elements := datasize / esize
    let operand := read_sfp idxdsize inst.Rn s
    let lo := index * esize
    let hi := lo + esize - 1
    let element := extractLsb hi lo operand
    have h₀ : 0 < esize := by apply zero_lt_shift_left_pos (by decide)
    have h₁ : hi - lo + 1 = esize := by simp [hi, lo]; omega
    let result := dup_aux 0 elements esize (h₁ ▸ element) (BitVec.zero datasize) h₀
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp datasize inst.Rd result s
    s
    
def exec_dup_general (inst : Advanced_simd_copy_cls) (s : ArmState) : ArmState :=
  let size := lowest_set_bit inst.imm5
  if size > 3 || (size == 3 && inst.Q == 0) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< size
    let datasize := 64 <<< inst.Q.toNat
    let elements := datasize / esize
    let element := read_gpr esize inst.Rn s
    have h₀ : 0 < esize := by apply zero_lt_shift_left_pos (by decide)
    let result := dup_aux 0 elements esize element (BitVec.zero datasize) h₀
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp datasize inst.Rd result s
    s

def exec_ins_element (inst : Advanced_simd_copy_cls) (s : ArmState) : ArmState :=
  let size := lowest_set_bit inst.imm5
  if size > 3 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let dst_index := (extractLsb 4 (size + 1) inst.imm5).toNat
    let src_index := (extractLsb 3 size inst.imm4).toNat
    let idxdsize := 64 <<< (extractLsb 3 3 inst.imm4).toNat
    let esize := 8 <<< size
    let operand := read_sfp idxdsize inst.Rn s
    let result := read_sfp 128 inst.Rd s
    let lo_src := src_index * esize
    let hi_src := lo_src + esize - 1
    let elem := extractLsb hi_src lo_src operand
    let lo_dst := dst_index * esize
    let hi_dst := lo_dst + esize - 1
    have h₀ : 0 < esize := by apply zero_lt_shift_left_pos (by decide)
    have h : hi_dst - lo_dst + 1 = hi_src - lo_src + 1 := by
      simp [hi_dst, lo_dst, hi_src, lo_src]
      omega
    let result := BitVec.partInstall hi_dst lo_dst (h ▸ elem) result
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp 128 inst.Rd result s
    s

def exec_ins_general (inst : Advanced_simd_copy_cls) (s : ArmState) : ArmState :=
  let size := lowest_set_bit inst.imm5
  if size > 3 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let index := (extractLsb 4 (size + 1) inst.imm5).toNat
    let esize := 8 <<< size
    let element := read_gpr esize inst.Rn s
    let result := read_sfp 128 inst.Rd s
    let lo := index * esize
    let hi := lo + esize -1
    have h₀ : 0 < esize := by apply zero_lt_shift_left_pos (by decide)
    have h : hi - lo + 1 = esize := by simp [hi, lo]; omega
    let result := BitVec.partInstall hi lo (h ▸ element) result
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp 128 inst.Rd result s
    s

def exec_smov_umov (inst : Advanced_simd_copy_cls) (s : ArmState) (signed : Bool): ArmState :=
  let size := lowest_set_bit inst.imm5
  let esize := 8 <<< size
  let datasize := 32 <<< inst.Q.toNat
  if signed && (size > 2 || datasize <= esize) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if (not signed)
       && (size > 3 || datasize == 64 && esize < 64 || datasize == 32 && esize >= 64) then
     write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let index := (extractLsb 4 (size + 1) inst.imm5).toNat
    let idxdsize := 64 <<< (extractLsb 4 4 inst.imm5).toNat
    -- if index == 0 then CheckFPEnabled64 else CheckFPAdvSIMDEnabled64
    let operand := read_sfp idxdsize inst.Rn s
    let lo := index * esize
    let hi := lo + esize - 1
    let element := extractLsb hi lo operand
    let result := if signed then signExtend datasize element else zeroExtend datasize element
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_gpr datasize inst.Rd result s
    s

@[simp]
def exec_advanced_simd_copy
  (inst : Advanced_simd_copy_cls) (s : ArmState) : ArmState :=
  match_bv inst.Q ++ inst.op ++ inst.imm5 ++ inst.imm4 with
  | [_Q:1, 0, _imm5:5, 0000] => exec_dup_element inst s
  | [_Q:1, 0, _imm5:5, 0001] => exec_dup_general inst s
  | [_Q:1, 0, _imm5:5, 0101] => exec_smov_umov inst s true
  | [_Q:1, 0, _imm5:5, 0111] => exec_smov_umov inst s false
  | [1, 0, _imm5:5, 0011] => exec_ins_general inst s
  | [1, 1, _imm5:5, _imm4:4] => exec_ins_element inst s
  | _ => write_err (StateError.Illegal s!"Illegal {inst} encountered!") s

----------------------------------------------------------------------

partial def Advanced_simd_copy_cls.dup_element.rand : IO (Option (BitVec 32)) := do
  let Q := ← BitVec.rand 1
  let imm5 := ← BitVec.rand 5
  let size := lowest_set_bit imm5
  if size > 3 || (size == 3 && Q == 0) then
    Advanced_simd_copy_cls.dup_element.rand
  else
    let (inst : Advanced_simd_copy_cls) :=
      { Q := Q,
        op := 0b0#1,
        imm5 := imm5,
        imm4 := 0b0000#4,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (inst.toBitVec32)

partial def Advanced_simd_copy_cls.dup_general.rand : IO (Option (BitVec 32)) := do
  let Q := ← BitVec.rand 1
  let imm5 := ← BitVec.rand 5
  let size := lowest_set_bit imm5
  if size > 3 || (size == 3 && Q == 0) then
    Advanced_simd_copy_cls.dup_general.rand
  else
    let (inst : Advanced_simd_copy_cls) :=
      { Q := Q,
        op := 0b0#1,
        imm5 := imm5,
        imm4 := 0b0001#4,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (inst.toBitVec32)

partial def Advanced_simd_copy_cls.ins_element.rand : IO (Option (BitVec 32)) := do
  let imm5 := ← BitVec.rand 5
  let size := lowest_set_bit imm5
  if size > 3 then
    Advanced_simd_copy_cls.ins_element.rand
  else
    let (inst : Advanced_simd_copy_cls) :=
      { Q := 0b1#1,
        op := 0b1#1,
        imm5 := imm5,
        imm4 := ← BitVec.rand 4,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (inst.toBitVec32)

partial def Advanced_simd_copy_cls.ins_general.rand : IO (Option (BitVec 32)) := do
  let imm5 := ← BitVec.rand 5
  let size := lowest_set_bit imm5
  if size > 3 then
    Advanced_simd_copy_cls.ins_general.rand
  else
    let (inst : Advanced_simd_copy_cls) :=
      { Q := 0b1#1,
        op := 0b0#1,
        imm5 := imm5,
        imm4 := 0b0011#4,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (inst.toBitVec32)

partial def Advanced_simd_copy_cls.smov.rand : IO (Option (BitVec 32)) := do
  let Q := ← BitVec.rand 1
  let imm5 := ← BitVec.rand 5
  let size := lowest_set_bit imm5
  let esize := 8 <<< size
  let datasize := 32 <<< Q.toNat
  if size > 2 || datasize <= esize then
    Advanced_simd_copy_cls.smov.rand
  else
    let (inst : Advanced_simd_copy_cls) :=
      { Q := Q,
        op := 0b0#1,
        imm5 := imm5,
        imm4 := 0b0101#4,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (inst.toBitVec32)

partial def Advanced_simd_copy_cls.umov.rand : IO (Option (BitVec 32)) := do
  let Q := ← BitVec.rand 1
  let imm5 := ← BitVec.rand 5
  let size := lowest_set_bit imm5
  let esize := 8 <<< size
  let datasize := 32 <<< Q.toNat
  if size > 3 || datasize == 64 && esize < 64 || datasize == 32 && esize >= 64 then
    Advanced_simd_copy_cls.umov.rand
  else
    let (inst : Advanced_simd_copy_cls) :=
      { Q := Q,
        op := 0b0#1,
        imm5 := imm5,
        imm4 := 0b0111#4,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
    }
    pure (inst.toBitVec32)

/-- Generate random instructions of Advanced_simd_copy class. -/
def Advanced_simd_copy_cls.rand : List (IO (Option (BitVec 32))) :=
[   Advanced_simd_copy_cls.dup_element.rand,
    Advanced_simd_copy_cls.dup_general.rand,
    Advanced_simd_copy_cls.ins_element.rand,
    Advanced_simd_copy_cls.ins_general.rand,
    Advanced_simd_copy_cls.smov.rand,
    Advanced_simd_copy_cls.umov.rand ]

end DPSFP
