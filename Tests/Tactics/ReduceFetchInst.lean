/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Reflect.FetchAndDecode
import Tests.«AES-GCM».GCMGmultV8Program

/-! ## Tests for `refuceFetchInst` simproc -/

example (h : s.program = GCMGmultV8Program.gcm_gmult_v8_program) :
    fetch_inst 0x7d8800#64 s = (some 1279294481#32) := by
  simp (config := {ground := false}) only [reduceFetchInst]
