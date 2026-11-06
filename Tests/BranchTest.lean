/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Arm.Exec

/-!
Unit tests for the PC-relative immediate branches (B, BL, B.cond, CBZ/CBNZ).

The architecture computes the offset as `SignExtend(imm:'00', 64)`, i.e. the
two zero bits are appended *before* sign extension; these tests cover offsets
outside the window where shifting at the immediate's own width happens to
agree (|offset| ≥ 32 MiB for B/BL, ≥ 256 KiB for B.cond/CBZ/CBNZ), plus small
and negative offsets. See https://github.com/leanprover/LNSym/issues/250.
-/

section BranchTest

open BitVec

/-- PC after executing the single instruction `word` at PC 0 in the default
state (all registers and flags zero). -/
private def pcAfter (word : BitVec 32) : BitVec 64 :=
  read_pc (run 1 (set_program ArmState.default [(0#64, word)]))

-- B (imm26)
example : pcAfter 0x15000000#32 = 0x4000000#64 := by native_decide            -- b .+64MiB
example : pcAfter 0x14800000#32 = 0x2000000#64 := by native_decide            -- b .+32MiB
example : pcAfter 0x17000000#32 = 0xfffffffffc000000#64 := by native_decide   -- b .-64MiB
example : pcAfter 0x14000001#32 = 0x4#64 := by native_decide                  -- b .+4
example : pcAfter 0x17ffffff#32 = 0xfffffffffffffffc#64 := by native_decide   -- b .-4
-- BL (imm26): same target, and x30 gets the return address
example : pcAfter 0x95000000#32 = 0x4000000#64 := by native_decide            -- bl .+64MiB
example : read_gpr 64 30#5
    (run 1 (set_program ArmState.default [(0#64, 0x95000000#32)])) = 0x4#64 := by
  native_decide
-- B.cond (imm19); AL is always taken
example : pcAfter 0x5440000e#32 = 0x80000#64 := by native_decide              -- b.al .+512KiB
example : pcAfter 0x54c0000e#32 = 0xfffffffffff80000#64 := by native_decide   -- b.al .-512KiB
example : pcAfter 0x54ffffee#32 = 0xfffffffffffffffc#64 := by native_decide   -- b.al .-4
-- CBZ / CBNZ (imm19); x0 = 0 in the default state
example : pcAfter 0xb4400000#32 = 0x80000#64 := by native_decide              -- cbz x0, .+512KiB
example : pcAfter 0xb4c00000#32 = 0xfffffffffff80000#64 := by native_decide   -- cbz x0, .-512KiB
example : pcAfter 0xb5400000#32 = 0x4#64 := by native_decide                  -- cbnz x0 (not taken)

end BranchTest
