/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Arm.Exec

/-!
SMOV/UMOV (Advanced SIMD copy to a general-purpose register): register 31 as
destination is the zero register, and both the `X` (`Q = 1`) and `W` (`Q = 0`)
forms have a GPR destination. See https://github.com/leanprover/LNSym/issues/253.
-/

section SMovUMovTest

open BitVec

/-- SP = 0x1000, v1 holds bytes 0x00..0x0f (byte `i` = `i`). -/
private def entry (word : BitVec 32) : ArmState :=
  let s := w (.GPR 31#5) 0x1000#64 ArmState.default
  let s := w (.SFP 1#5) 0x0f0e0d0c0b0a09080706050403020100#128 s
  set_program s [(0#64, word)]

private def after (word : BitVec 32) : ArmState := run 1 (entry word)

-- Element extraction, W and X forms.
example : r (.GPR 0#5) (after 0x0e0a3c20#32) = 0x0504#64 := by native_decide              -- umov w0, v1.h[2]
example : r (.GPR 0#5) (after 0x0e072c20#32) = 0x03#64 := by native_decide                -- smov w0, v1.b[3]
example : r (.GPR 0#5) (after 0x4e183c20#32) = 0x0f0e0d0c0b0a0908#64 := by native_decide  -- umov x0, v1.d[1]
example : r (.GPR 0#5) (after 0x4e0c2c20#32) = 0x07060504#64 := by native_decide          -- smov x0, v1.s[1]

-- Rd = 31 is the zero register: SP is unchanged.
example : r (.GPR 31#5) (after 0x0e0a3c3f#32) = 0x1000#64 := by native_decide  -- umov wzr, v1.h[2]
example : r (.GPR 31#5) (after 0x4e0c2c3f#32) = 0x1000#64 := by native_decide  -- smov xzr, v1.s[1]
example : r (.GPR 31#5) (after 0x4e183c3f#32) = 0x1000#64 := by native_decide  -- umov xzr, v1.d[1]

-- The modified-register footprint names the GPR for both Q values.
example : DPSFP.MayModifyRegs 0x0e0a3c20#32 = .ok [.GPR 0#5] := by rfl  -- umov w0, v1.h[2]
example : DPSFP.MayModifyRegs 0x0e072c20#32 = .ok [.GPR 0#5] := by rfl  -- smov w0, v1.b[3]
example : DPSFP.MayModifyRegs 0x4e183c20#32 = .ok [.GPR 0#5] := by rfl  -- umov x0, v1.d[1]

end SMovUMovTest
