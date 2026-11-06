/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Arm.Exec

/-!
Register 31 is the zero register (XZR/WZR) in the operand positions below, not
SP: reads give zero and writes are discarded. Each case starts with SP = 0x1000
and X0 = 0 and runs one instruction at PC 0.
See https://github.com/leanprover/LNSym/issues/251.
-/

section XZRTest

open BitVec

private def entry (word : BitVec 32) : ArmState :=
  set_program (w (.GPR 31#5) 0x1000#64 ArmState.default) [(0#64, word)]

private def after (word : BitVec 32) : ArmState := run 1 (entry word)

-- (1) MOVZ/MOVN/MOVK with Rd = 31: SP is unchanged.
example : r (.GPR 31#5) (after 0xd280001f#32) = 0x1000#64 := by native_decide  -- movz xzr, #0
example : r (.GPR 31#5) (after 0x9280001f#32) = 0x1000#64 := by native_decide  -- movn xzr, #0
example : r (.GPR 31#5) (after 0xf280001f#32) = 0x1000#64 := by native_decide  -- movk xzr, #0
example : r (.GPR 31#5) (after 0x5280001f#32) = 0x1000#64 := by native_decide  -- movz wzr, #0

-- (2) CBZ/CBNZ with Rt = 31: the operand is zero.
example : read_pc (after 0xb400005f#32) = 0x8#64 := by native_decide  -- cbz xzr, .+8 (taken)
example : read_pc (after 0xb500005f#32) = 0x4#64 := by native_decide  -- cbnz xzr, .+8 (not taken)
example : read_pc (after 0x3400005f#32) = 0x8#64 := by native_decide  -- cbz wzr, .+8 (taken)

-- (3) Load/store data register 31 (base X0 = 0; memory starts all zero).
-- Loads into XZR are discarded; stores of XZR write zeros.
private def mem1 : ArmState :=  -- non-zero memory at 0..15 so a store of zero is visible
  write_mem_bytes 16 0#64 (BitVec.allOnes 128) (entry 0#32)
private def afterMem (word : BitVec 32) : ArmState :=
  run 1 (set_program mem1 [(0#64, word)])

example : r (.GPR 31#5) (afterMem 0xf940001f#32) = 0x1000#64 := by native_decide  -- ldr xzr, [x0]
example : read_mem_bytes 8 0#64 (afterMem 0xf900001f#32) = 0#64 := by native_decide  -- str xzr, [x0]
example : read_mem_bytes 4 0#64 (afterMem 0xb900001f#32) = 0#32 := by native_decide  -- str wzr, [x0]
example : r (.GPR 31#5) (afterMem 0xa940041f#32) = 0x1000#64 := by native_decide  -- ldp xzr, x1, [x0]
example : read_mem_bytes 8 0#64 (afterMem 0xa900041f#32) = 0#64 := by native_decide  -- stp xzr, x1, [x0]
example : read_mem_bytes 8 8#64 (afterMem 0xa9007c01#32) = 0#64 := by native_decide  -- stp x1, xzr, [x0]
example : read_mem_bytes 16 0#64 (afterMem 0xa9007c1f#32) = 0#128 := by native_decide -- stp xzr, xzr, [x0]
example : r (.GPR 31#5) (afterMem 0x6940041f#32) = 0x1000#64 := by native_decide  -- ldpsw xzr, x1, [x0]
-- The base register 31 is still SP: str x1, [sp] stores at 0x1000.
example : read_mem_bytes 8 0x1000#64
    (run 1 (set_program (w (.GPR 1#5) 0x2a#64 (entry 0#32)) [(0#64, 0xf90003e1#32)])) =
    0x2a#64 := by native_decide

-- (4) Logical immediate with Rn = 31: the source is zero.
example : r (.GPR 0#5) (after 0x9240fbe0#32) = 0#64 := by native_decide  -- and  x0, xzr, #0x7fff...
example : r (.GPR 0#5) (after 0xb24003e0#32) = 1#64 := by native_decide  -- orr  x0, xzr, #1 (mov)
example : r (.GPR 0#5) (after 0xd24003e0#32) = 1#64 := by native_decide  -- eor  x0, xzr, #1
example : r (.GPR 0#5) (after 0xf240fbe0#32) = 0#64 := by native_decide  -- ands x0, xzr, #0x7fff...
-- Destination 31 of non-flag-setting AND/ORR/EOR immediate is still SP.
example : r (.GPR 31#5) (after 0xb240001f#32) = 1#64 := by native_decide  -- orr sp, x0, #1

end XZRTest
