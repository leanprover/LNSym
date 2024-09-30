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
xxx: GCMGmultV8 Helem HTable
-/

set_option pp.deepTerms false in
set_option pp.deepTerms.threshold 20 in
-- set_option trace.simp_mem.info true in
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
    -- HTable is unmodified
    sf[read_gpr 64 1#5 s0, 256] = HTable
    -- ∧
    -- sf[read_gpr 64 0#5 s0, 16] = xxx
  := by
  simp_all only [state_simp_rules, -h_run] -- prelude
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 27
  -- Epilogue
  simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  simp only [memory_rules] at *
  sym_aggregate
  -- Aggregate the memory effects.
  -- (FIXME) This will be tackled by `sym_aggregate` when `sym_n` and `simp_mem`
  -- are merged.
  simp only [*]
  /-
  (FIXME @bollu) `simp_mem; rfl` creates a malformed proof here. The tactic produces
  no goals, but we get the following error message:

  application type mismatch
  Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
    (Eq.mp (congrArg (Eq HTable) (Memory.State.read_mem_bytes_eq_mem_read_bytes s0))
      (Eq.mp (congrArg (fun x => HTable = read_mem_bytes 256 x s0) zeroExtend_eq_of_r_gpr) h_HTable))
  argument has type
    HTable = Memory.read_bytes 256 (r (StateField.GPR 1#5) s0) s0.mem
  but function has type
    Memory.read_bytes 256 (r (StateField.GPR 1#5) s0) s0.mem = HTable →
    mem_subset' (r (StateField.GPR 1#5) s0) 256 (r (StateField.GPR 1#5) s0) 256 →
      Memory.read_bytes 256 (r (StateField.GPR 1#5) s0) s0.mem =
        HTable.extractLsBytes (BitVec.toNat (r (StateField.GPR 1#5) s0) - BitVec.toNat (r (StateField.GPR 1#5) s0)) 256

  simp_mem; rfl
  -/
  rw [Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate']
  simp_mem
  done
