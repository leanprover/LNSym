/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.Aggregate
import Tactics.StepThms
import Tactics.CSE
import Arm.Memory.SeparateAutomation
import Arm.Syntax

namespace GCMGmultV8Program
open ArmStateNotation

#genStepEqTheorems gcm_gmult_v8_program

/-
xxx: GCMGmultV8 Xi HTable
-/

set_option pp.deepTerms false in
set_option pp.deepTerms.threshold 50 in
-- set_option trace.simp_mem.info true in
theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_Xi : Xi = s0[read_gpr 64 0#5 s0, 16])
    (h_HTable : HTable = s0[read_gpr 64 1#5 s0, 256])
    (h_mem_sep : Memory.Region.pairwiseSeparate
                 [(read_gpr 64 0#5 s0, 16),
                  (read_gpr 64 1#5 s0, 256)])
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    -- The final state is error-free.
    read_err sf = .None ∧
    -- The program is unmodified in `sf`.
    sf.program = gcm_gmult_v8_program ∧
    -- The stack pointer is still aligned in `sf`.
    CheckSPAlignment sf ∧
    -- The final state returns to the address in register `x30` in `s0`.
    read_pc sf = r (StateField.GPR 30#5) s0 ∧
    -- HTable is unmodified.
    sf[read_gpr 64 1#5 s0, 256] = HTable ∧
    -- Frame conditions.
    -- Note that the following also covers that the Xi address in .GPR 0
    -- is unmodified.
    REGS_UNCHANGED_EXCEPT [.SFP 0, .SFP 1, .SFP 2, .SFP 3,
                           .SFP 17, .SFP 18, .SFP 19, .SFP 20,
                           .SFP 21, .PC]
                          (sf, s0) ∧
    -- Memory frame condition.
    MEM_UNCHANGED_EXCEPT [(r (.GPR 0) s0, 128)] (sf, s0) := by
  simp_all only [state_simp_rules, -h_run] -- prelude
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected

  sym_n 27
  -- Epilogue
  simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  simp only [memory_rules] at *
  sym_aggregate

  -- stop
  -- Split conjunction
  repeat' apply And.intro
  · simp only [List.mem_cons, List.mem_singleton, not_or, and_imp]
    sym_aggregate
  · intro n addr h_separate
    simp_mem (config := { useOmegaToClose := false })
    -- Aggregate the memory (non)effects.
    simp only [*]
  done
