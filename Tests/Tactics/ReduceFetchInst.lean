/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Reflect.FetchAndDecode
import Tests.«AES-GCM».GCMGmultV8Program
import Tests.SHA2.SHA512ProgramTest

/-! ## Tests for `refuceFetchInst` simproc -/

/--
error: unsolved goals
s : ArmState
z : Option (BitVec 32)
h : s.program = GCMGmultV8Program.gcm_gmult_v8_program
⊢ some 1279294481#32 = z
-/
#guard_msgs in example (h : s.program = GCMGmultV8Program.gcm_gmult_v8_program) :
    fetch_inst 0x7d8800#64 s = z := by
  simp (config := {ground := false}) only [reduceFetchInst]

/--
error: unsolved goals
s : ArmState
z : Option (BitVec 32)
h : s.program = sha512_program_map
⊢ some 2847898621#32 = z
-/
#guard_msgs in example (h : s.program = sha512_program_map) :
    fetch_inst 0x1264c0#64 s = z := by
  simp (config := {ground := false}) only [reduceFetchInst]

/--
error: unsolved goals
s : ArmState
z : Option (BitVec 32)
h : s.program = sha512_program_map
⊢ some 4165011453#32 = z
-/
#guard_msgs in example (h : s.program = sha512_program_map) :
    fetch_inst 0x126c98#64 s = z := by
  simp (config := {ground := false}) only [reduceFetchInst]

/-! ## Tests for `reduceDecodeInst` simproc -/

/--
error: unsolved goals
z : Option ArmInst
⊢ some
      (ArmInst.LDST
        (LDSTInst.Advanced_simd_multiple_struct
          { _fixed1 := 0#1, Q := 1#1, _fixed2 := 24#7, L := 1#1, _fixed3 := 0#6, opcode := 7#4, size := 3#2, Rn := 0#5,
            Rt := 17#5 })) =
    z
-/
#guard_msgs in example : decode_raw_inst 1279294481#32 = z := by
  simp (config := {ground := false}) only [reduceDecodeInst]
