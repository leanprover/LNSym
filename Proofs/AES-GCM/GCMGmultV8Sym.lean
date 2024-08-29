/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.StepThms

namespace GCMGmultV8Program

#genStepEqTheorems gcm_gmult_v8_program

set_option diagnostics true in
theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    read_err sf = .None := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 27
  done
