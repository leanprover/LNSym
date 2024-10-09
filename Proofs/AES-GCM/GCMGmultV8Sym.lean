/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer, Shilpi Goel
-/
import Specs.GCMV8
import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.Aggregate
import Tactics.StepThms
import Tactics.CSE
import Tactics.ClearNamed
import Arm.Memory.SeparateAutomation
import Arm.Syntax

namespace GCMGmultV8Program
open ArmStateNotation

#genStepEqTheorems gcm_gmult_v8_program

private theorem lsb_from_extractLsb'_of_append_self (x : BitVec 128) :
  BitVec.extractLsb' 64 64 (BitVec.extractLsb' 64 128 (x ++ x)) =
  BitVec.extractLsb' 0 64 x := by
  bv_decide

private theorem msb_from_extractLsb'_of_append_self (x : BitVec 128) :
  BitVec.extractLsb' 0 64 (BitVec.extractLsb' 64 128 (x ++ x)) =
  BitVec.extractLsb' 64 64 x := by
  bv_decide

theorem extractLsb'_zero_extractLsb'_of_le (h : len1 ≤ len2) :
  BitVec.extractLsb' 0 len1 (BitVec.extractLsb' start len2 x) =
  BitVec.extractLsb' start len1 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_extractLsb', Fin.is_lt,
             decide_True, Nat.zero_add, Bool.true_and,
             Bool.and_iff_right_iff_imp, decide_eq_true_eq]
  omega

theorem extractLsb'_extractLsb'_zero_of_le (h : start + len1 ≤ len2):
  BitVec.extractLsb' start len1 (BitVec.extractLsb' 0 len2 x) =
  BitVec.extractLsb' start len1 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_extractLsb', Fin.is_lt,
            decide_True, Nat.zero_add, Bool.true_and,
            Bool.and_iff_right_iff_imp, decide_eq_true_eq]
  omega

set_option pp.deepTerms false in
set_option pp.deepTerms.threshold 50 in
-- set_option trace.simp_mem.info true in
theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_Xi : Xi = s0[read_gpr 64 0#5 s0, 16])
    (h_HTable : HTable = s0[read_gpr 64 1#5 s0, 32])
    (h_mem_sep : Memory.Region.pairwiseSeparate
                 [(read_gpr 64 0#5 s0, 16),
                  (read_gpr 64 1#5 s0, 32)])
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    -- The final state is error-free.
    read_err sf = .None ∧
    -- The program is unmodified in `sf`.
    sf.program = gcm_gmult_v8_program ∧
    -- The stack pointer is still aligned in `sf`.
    CheckSPAlignment sf ∧
    -- The final state returns to the address in register `x30` in `s0`.
    read_pc sf = r (StateField.GPR 30#5) s0 ∧
    -- (TODO) Delete the following conjunct because it is covered by the
    -- MEM_UNCHANGED_EXCEPT frame condition. We keep it around because it
    -- exposes the issue with `simp_mem` that @bollu will fix.
    -- HTable is unmodified.
    sf[read_gpr 64 1#5 s0, 32] = HTable ∧
    -- Frame conditions.
    -- Note that the following also covers that the Xi address in .GPR 0
    -- is unmodified.
    REGS_UNCHANGED_EXCEPT [.SFP 0, .SFP 1, .SFP 2, .SFP 3,
                           .SFP 17, .SFP 18, .SFP 19, .SFP 20,
                           .SFP 21, .PC]
                          (sf, s0) ∧
    -- Memory frame condition.
    MEM_UNCHANGED_EXCEPT [(r (.GPR 0) s0, 16)] (sf, s0) ∧
    sf[r (.GPR 0) s0, 16] = GCMV8.GCMGmultV8_alt (HTable.extractLsb' 0 128) Xi := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  simp only [Nat.reduceMul] at Xi HTable
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 27
  -- Epilogue
  simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  simp only [memory_rules] at *
  sym_aggregate
  -- Split conjunction
  repeat' apply And.intro
  · -- Aggregate the memory (non)effects.
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
  · simp only [List.mem_cons, List.mem_singleton, not_or, and_imp]
    sym_aggregate
  · intro n addr h_separate
    simp_mem (config := { useOmegaToClose := false })
    -- Aggregate the memory (non)effects.
    simp only [*]
  · clear_named [h_s, stepi_]
    clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26
    -- Simplifying the LHS
    have h_HTable_low :
      Memory.read_bytes 16 (r (StateField.GPR 1#5) s0) s0.mem = HTable.extractLsb' 0 128 := by
      -- (FIXME @bollu) use `simp_mem` instead of the rw below.
      rw [@Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
           32 (r (StateField.GPR 1#5) s0) HTable (r (StateField.GPR 1#5) s0) 16 _ h_HTable.symm]
      · simp only [Nat.reduceMul, BitVec.extractLsBytes, Nat.sub_self, Nat.zero_mul]
      · simp_mem
    have h_HTable_high :
      (Memory.read_bytes 16 (r (StateField.GPR 1#5) s0 + 16#64) s0.mem) = HTable.extractLsb' 128 128 := by
      -- (FIXME @bollu) use `simp_mem` instead of the rw below.
      rw [@Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
          32 (r (StateField.GPR 1#5) s0) HTable (r (StateField.GPR 1#5) s0 + 16#64) 16 _ h_HTable.symm]
      repeat sorry
    simp only [h_HTable_high, h_HTable_low, ←h_Xi]
    /-
    simp/ground below to reduce
    (BitVec.extractLsb' 0 64
                      (shift_left_common_aux 0
                        { esize := 64, elements := 2, shift := 57, unsigned := true, round := false,
                          accumulate := false }
                        300249147283180997173565830086854304225#128 0#128))
    -/
    simp (config := {ground := true}) only
    simp only [msb_from_extractLsb'_of_append_self,
               lsb_from_extractLsb'_of_append_self,
               BitVec.partInstall]
    -- (FIXME @bollu) cse leaves the goal unchanged here, quietly, likely due to
    -- subexpressions occurring in dep. contexts. Maybe a message here would be helpful.
    generalize h_Xi_rev : rev_vector 128 64 8 Xi _ _ _ _ _ = Xi_rev
    -- Simplifying the RHS
    simp only [←h_HTable, GCMV8.GCMGmultV8_alt,
               GCMV8.lo, GCMV8.hi,
               GCMV8.gcm_polyval]
    repeat rw [extractLsb'_zero_extractLsb'_of_le (by decide)]
    repeat rw [extractLsb'_extractLsb'_zero_of_le (by decide)]

    sorry
  done

end GCMGmultV8Program
