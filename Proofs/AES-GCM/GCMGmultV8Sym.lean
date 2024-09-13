/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.StepThms
import Arm.Memory.SeparateAutomation
import Arm.Syntax

namespace GCMGmultV8Program
open ArmStateNotation

#genStepEqTheorems gcm_gmult_v8_program

/-
xxx: GCMGmultV8 Helem HTable
-/

-- set_option pp.deepTerms true in
-- set_option pp.deepTerms.threshold 1 in
set_option trace.simp_mem.info true in
theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_Helem : Helem = s0[read_gpr 64 0#5 s0, 16])
    (h_HTable : HTable = s0[read_gpr 64 1#5 s0, 256])
    (h_mem_sep : Memory.Region.pairwiseSeparate
                 [(read_gpr 64 0#5 s0, 16),
                  (read_gpr 64 1#5 s0, 256)])
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    read_err sf = .None ∧
    -- Helem address is unmodified.
    read_gpr 64 0#5 sf = read_gpr 64 0#5 s0 ∧
    -- let sf' := write_mem_bytes 16 (r (StateField.GPR 0#5) sf) 0 sf
    -- HTable is unmodified
    sf[read_gpr 64 1#5 s0, 256] = HTable
    -- ∧
    -- sf[read_gpr 64 0#5 s0, 16] = xxx
  := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 27
  -- Epilogue
  -- simp only [memory_rules, read_gpr] at *
  -- simp_mem
  -- simp only [bitvec_rules, Nat.sub_self]
  -- done
  sorry
