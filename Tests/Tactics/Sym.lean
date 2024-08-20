/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Proofs.«AES-GCM».GCMGmultV8Sym

namespace GCMGmultV8Program

-- Test the behaviour of `sym_n` when `h_err` and `h_sp` are not present
/-- warning: declaration uses 'sorry' -/ -- `guard_msgs` silences the warning
#guard_msgs in example (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    read_err sf = .None := by
  simp (config := {ground := true}) only [Option.some.injEq] at h_s0_pc h_run
  sym_n 1
  · sorry
  · exact (sorry : CheckSPAlignment s0)
  · exact (sorry : read_err s0 = .None)
  done
