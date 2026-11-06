/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Arm.Decode

/-!
`LDST.mayModifiedRegs` reports the data registers of loads and the base
register of writeback forms; stores without writeback modify no registers.
See https://github.com/leanprover/LNSym/issues/252.
-/

section MayModifiedRegsTest

-- Single register, unsigned offset (no writeback)
example : LDST.mayModifiedRegs 0xf9400408#32 = .ok [.GPR 8#5] := by rfl          -- ldr x8, [x0, #8]
example : LDST.mayModifiedRegs 0xf9000408#32 = .ok [] := by rfl                  -- str x8, [x0, #8]
example : LDST.mayModifiedRegs 0x3dc00000#32 = .ok [.SFP 0#5] := by rfl          -- ldr q0, [x0]
-- Single register, post-indexed (writeback)
example : LDST.mayModifiedRegs 0xf8408408#32 = .ok [.GPR 8#5, .GPR 0#5] := by rfl  -- ldr x8, [x0], #8
example : LDST.mayModifiedRegs 0xf8008408#32 = .ok [.GPR 0#5] := by rfl            -- str x8, [x0], #8
-- Single register, unscaled offset (no writeback)
example : LDST.mayModifiedRegs 0xf8401008#32 = .ok [.GPR 8#5] := by rfl          -- ldur x8, [x0, #1]
example : LDST.mayModifiedRegs 0xf8001008#32 = .ok [] := by rfl                  -- stur x8, [x0, #1]
-- Pairs
example : LDST.mayModifiedRegs 0xa9400801#32 = .ok [.GPR 1#5, .GPR 2#5] := by rfl            -- ldp x1, x2, [x0]
example : LDST.mayModifiedRegs 0xa9000801#32 = .ok [] := by rfl                               -- stp x1, x2, [x0]
example : LDST.mayModifiedRegs 0xa8c10801#32 = .ok [.GPR 1#5, .GPR 2#5, .GPR 0#5] := by rfl  -- ldp x1, x2, [x0], #16
example : LDST.mayModifiedRegs 0xa9bf0801#32 = .ok [.GPR 0#5] := by rfl                       -- stp x1, x2, [x0, #-16]!
example : LDST.mayModifiedRegs 0xad400400#32 = .ok [.SFP 0#5, .SFP 1#5] := by rfl            -- ldp q0, q1, [x0]
-- Multiple structures: all `rpt * selem` registers
example : LDST.mayModifiedRegs 0x4c400000#32 =
    .ok [.SFP 0#5, .SFP 1#5, .SFP 2#5, .SFP 3#5] := by rfl                      -- ld4 {v0.16b-v3.16b}, [x0]
example : LDST.mayModifiedRegs 0x4c00a000#32 = .ok [] := by rfl                  -- st1 {v0.16b, v1.16b}, [x0]
example : LDST.mayModifiedRegs 0x4cdfa000#32 =
    .ok [.SFP 0#5, .SFP 1#5, .GPR 0#5] := by rfl                                -- ld1 {v0.16b, v1.16b}, [x0], #32
example : LDST.mayModifiedRegs 0x4c9fa000#32 = .ok [.GPR 0#5] := by rfl          -- st1 {v0.16b, v1.16b}, [x0], #32

end MayModifiedRegsTest
