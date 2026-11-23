/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Boris Nagaev
-/

import Arm.Exec

/-!
Encodings that the Arm ARM marks UNDEFINED stop execution with
`StateError.Illegal`, leaving PC and the destination register unchanged.
Cosimulation cannot cover this: it generates only legal encodings. Each case
starts with X0 = 0x5555555555555555, X1 = 0x0123456789abcdef and
X2 = 0xfedcba9876543210, and runs one instruction at PC 0.
-/

section UndefinedEncodingTest

open BitVec

private def entry (word : BitVec 32) : ArmState :=
  set_program
    (w (.GPR 2#5) 0xfedcba9876543210#64
      (w (.GPR 1#5) 0x0123456789abcdef#64
        (w (.GPR 0#5) 0x5555555555555555#64 ArmState.default)))
    [(0#64, word)]

private def after (word : BitVec 32) : ArmState := run 1 (entry word)

/-- The instruction is rejected as illegal, and PC and X0 are unchanged. -/
private def rejected (word : BitVec 32) : Bool :=
  let s := after word
  (match read_err s with | .Illegal _ => true | _ => false) &&
    read_pc s == 0#64 && r (.GPR 0#5) s == 0x5555555555555555#64

-- EXTR: UNDEFINED if op21 ≠ 00, o0 ≠ 0, N ≠ sf, or imms<5> = 1 with sf = 0.
example : rejected 0xb3c2d020#32 := by native_decide  -- extr x0, x1, x2, #52 with op21 = 01
example : rejected 0xd3c2d020#32 := by native_decide  -- extr x0, x1, x2, #52 with op21 = 10
example : rejected 0x93e2d020#32 := by native_decide  -- extr x0, x1, x2, #52 with o0 = 1
example : rejected 0x9382d020#32 := by native_decide  -- extr x0, x1, x2, #52 with N = 0
example : rejected 0x13c21020#32 := by native_decide  -- extr w0, w1, w2, #4 with N = 1
example : rejected 0x13828020#32 := by native_decide  -- extr w0, w1, w2 with imms = 32
-- The largest legal 32-bit shift is accepted.
example : read_err (after 0x13827c20#32) = .None := by native_decide              -- extr w0, w1, w2, #31
example : r (.GPR 0#5) (after 0x13827c20#32) = 0x13579bde#64 := by native_decide -- extr w0, w1, w2, #31

end UndefinedEncodingTest
