/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- TBL and TBX (Single, Two, Three, Four register table)

import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

----------------------------------------------------------------------

namespace DPSFP

open BitVec

def create_table (i : Nat) (regs : Nat) (Rn : BitVec 5) (table : BitVec (128 * regs))
  (s : ArmState) : BitVec (128 * regs) :=
  if h₀ : regs <= i then
    table
  else
    let val := read_sfp 128 Rn s
    have h₁ : 128 = 128 * i + 127 - 128 * i + 1 := by omega
    let table := BitVec.partInstall (128 * i + 127) (128 * i) (BitVec.cast h₁ val) table
    let Rn := (Rn + 1) % 32
    have h₂ : regs - (i + 1) < regs - i := by omega
    create_table (i + 1) regs Rn table s
  termination_by (regs - i)

def tblx_aux (i : Nat) (elements : Nat) (indices : BitVec datasize)
  (regs : Nat) (table : BitVec (128 * regs)) (result: BitVec datasize)
  : BitVec datasize :=
  if h₀ : elements <= i then
    result
  else
    have h₁ : 8 > 0 := by decide
    let index := (elem_get indices i 8).toNat
    let result :=
      if index < 16 * regs then
        let val := elem_get table index 8
        elem_set result i 8 val h₁
      else
        result
    have h₂ : elements - (i + 1) < elements - i := by omega
    tblx_aux (i + 1) elements indices regs table result
  termination_by (elements - i)

@[state_simp_rules]
def exec_tblx (inst : Advanced_simd_table_lookup_cls) (s : ArmState) : ArmState :=
  let datasize := 64 <<< inst.Q.toNat
  let elements := datasize / 8
  let regs := inst.len.toNat + 1
  let is_tbl := (inst.op = 0b0#1)
  let indices := read_sfp datasize inst.Rm s
  let table := BitVec.zero (128 * regs)
  let table := create_table 0 regs inst.Rn table s
  let result := if is_tbl
                then BitVec.zero datasize
                else read_sfp datasize inst.Rd s
  let result := tblx_aux 0 elements indices regs table result
  -- State Updates
  let s := write_sfp datasize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_advanced_simd_table_lookup
  (inst : Advanced_simd_table_lookup_cls) (s : ArmState) : ArmState :=
  if inst.op2 = 0b00#2 then
    exec_tblx inst s
  else write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

def Advanced_simd_table_lookup_cls.tbl.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let (inst : Advanced_simd_table_lookup_cls) :=
    { Q := ← BitVec.rand 1,
      op2 := 0b00#2,
      Rm := ← BitVec.rand 5,
      len := ← BitVec.rand 2,
      op := ← BitVec.rand 1,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5
    }
  pure (some (inst.toBitVec32))

/-- Generate random instructions of Advanced_simd_table_lookup class. -/
def Advanced_simd_table_lookup_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [ Advanced_simd_table_lookup_cls.tbl.rand ]

end DPSFP
