/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- SHL, SSHR and USHR, SSRA and USRA, SRSHR and URSHR, SRSRA and URSRA (scalar)

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace DPSFP

open BitVec

@[state_simp_rules]
def exec_shift_right_scalar
  (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState) : ArmState :=
  if extractLsb 3 3 inst.immh != 0b1#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< 3
    have h : esize > 0 := by decide
    let datasize := esize
    let (info : ShiftInfo) :=
      { esize := esize,
        elements := 1,
        shift := (esize * 2) - (inst.immh ++ inst.immb).toNat,
        unsigned := inst.U == 0b1#1,
        round := (extractLsb 2 2 inst.opcode) == 0b1#1,
        accumulate := (extractLsb 1 1 inst.opcode) == 0b1#1,
        h := h
       }
    let result := shift_right_common info datasize inst.Rn inst.Rd s
    -- State Update
    let s := write_sfp datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

@[state_simp_rules]
def exec_shl_scalar
  (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState) : ArmState :=
  if extractLsb 3 3 inst.immh != 0b1#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< 3
    have h : esize > 0 := by decide
    let datasize := esize
    let (info : ShiftInfo) :=
      { esize := esize,
        elements := 1,
        shift := (inst.immh ++ inst.immb).toNat - esize,
        h := h
      }
    let result := shift_left_common info datasize inst.Rn s
    -- State Update
    let s := write_sfp datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

@[state_simp_rules]
def exec_advanced_simd_scalar_shift_by_immediate
  (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState) : ArmState :=
  match inst.U, inst.opcode with
  | 0b0#1, 0b01010#5 => exec_shl_scalar inst s
  | 0b0#1, 0b00000#5
  | 0b0#1, 0b00010#5
  | 0b0#1, 0b00100#5
  | 0b0#1, 0b00110#5
  | 0b1#1, 0b00000#5
  | 0b1#1, 0b00010#5
  | 0b1#1, 0b00100#5
  | 0b1#1, 0b00110#5 => exec_shift_right_scalar inst s
  | _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  
----------------------------------------------------------------------

partial def Advanced_simd_scalar_shift_by_immediate_cls.shr_all.rand
  (opcode : BitVec 5) : IO (Option (BitVec 32)) := do
  let immh := ← BitVec.rand 4
  if extractLsb 3 3 immh != 0b1#1 then
    Advanced_simd_scalar_shift_by_immediate_cls.shr_all.rand opcode
  else
    let (inst : Advanced_simd_scalar_shift_by_immediate_cls) :=
      { U := ← BitVec.rand 1,
        immh := immh,
        immb := ← BitVec.rand 3,
        opcode := opcode,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (some inst.toBitVec32)

partial def Advanced_simd_scalar_shift_by_immediate_cls.shl.rand
  : IO (Option (BitVec 32)) := do
  let immh := ← BitVec.rand 4
  if extractLsb 3 3 immh != 0b1#1 then
    Advanced_simd_scalar_shift_by_immediate_cls.shl.rand
  else
    let (inst : Advanced_simd_scalar_shift_by_immediate_cls) :=
      { U := 0b0#1,
        immh := immh,
        immb := ← BitVec.rand 3,
        opcode := 0b01010#5,
        Rn := ← BitVec.rand 5,
        Rd := ← BitVec.rand 5
      }
    pure (some inst.toBitVec32)

/-- Generate random instructions of Advanced_simd_scalar_shift_by_immediate_cls class. -/
def Advanced_simd_scalar_shift_by_immediate_cls.rand : List (IO (Option (BitVec 32))) :=
[ Advanced_simd_scalar_shift_by_immediate_cls.shl.rand,               -- SHL
  Advanced_simd_scalar_shift_by_immediate_cls.shr_all.rand 0b00000#5, -- SSHR, USHR
  Advanced_simd_scalar_shift_by_immediate_cls.shr_all.rand 0b00010#5, -- SSRA, USRA
  Advanced_simd_scalar_shift_by_immediate_cls.shr_all.rand 0b00100#5, -- SRSHR, URSHR
  Advanced_simd_scalar_shift_by_immediate_cls.shr_all.rand 0b00110#5  -- SRSRA, URSRA
  ]

end DPSFP
