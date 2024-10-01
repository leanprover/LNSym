/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Sym.FetchAndDecode
import Tests.«AES-GCM».GCMGmultV8Program
import Tests.SHA2.SHA512Program

/-! ## Tests for `refuceFetchInst` simproc -/

example (h : s.program = GCMGmultV8Program.gcm_gmult_v8_program) :
    fetch_inst 0x7d8800#64 s = (some 1279294481#32) := by
  simp (config := {ground := false}) only [reduceFetchInst]

example (h : s.program = SHA512.program) :
    fetch_inst 0x1264c0#64 s = (some 0xa9bf7bfd#32) := by
  simp (config := {ground := false}) only [reduceFetchInst]

example (h : s.program = SHA512.program) :
    fetch_inst 0x126c98#64 s = (some 0xf84107fd#32) := by
  simp (config := {ground := false}) only [reduceFetchInst]
