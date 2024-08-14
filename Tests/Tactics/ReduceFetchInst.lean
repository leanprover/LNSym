/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Reflect.FetchAndDecode
import Tests.«AES-GCM».GCMGmultV8Program
import Proofs.SHA512.SHA512Program

/-! ## Tests for `refuceFetchInst` simproc -/

example (h : s.program = GCMGmultV8Program.gcm_gmult_v8_program) :
    fetch_inst 0x7d8800#64 s = (some 1279294481#32) := by
  simp (config := {ground := false}) only [reduceFetchInst]

example (h : s.program = sha512_program) :
    fetch_inst 0x1264c4#64 s = (some 0x910003fd#32) := by
  simp (config := {ground := false}) only [reduceFetchInst]

example (h : s.program = sha512_program) :
    fetch_inst 0x126c94#64 s = (some 0x4c002c00#32) := by
  simp (config := {ground := false}) only [reduceFetchInst]
