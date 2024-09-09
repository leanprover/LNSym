/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Tests.«AES-GCM».AESHWEncryptProgram
import Tactics.Sym
import Tactics.StepThms
import Tactics.Aggregate
import Correctness.ArmSpec

namespace AESHWEncryptProgram

#genStepEqTheorems aes_hw_encrypt_program

abbrev in_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 0#5) s
abbrev key_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 2#5) s
abbrev round_addr (s : ArmState) : BitVec 64 := (r (StateField.GPR 2#5) s) + 240#64
abbrev out_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 1#5) s

theorem aes_hw_encrypt_program_run_60 (s0 sf : ArmState)
    (h_s0_program : s0.program = aes_hw_encrypt_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = aes_hw_encrypt_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run 60 s0)
    -- AES256 rounds = 14, the address of rounds is stored in x2
    (h_rounds : 14 = read_mem_bytes 4 (round_addr s0) s0)
    -- memory separation
    (h_mem : Memory.Region.pairwiseSeparate
      [⟨(in_addr s0), 128⟩,
       ⟨(key_addr s0), 1984⟩, -- 240*8 bits key schedule and 64 bits rounds
       ⟨(out_addr s0), 128⟩ ])
    : read_err sf = .None := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `aes_hw_encrypt_program.min` is somehow
  --    unable to be reflected
  -- TODO: branching condition currently not supported so manually unroll loops
  -- sym_n 13 fails with "tactic 'rewrite' failed, motive is not type correct"
  sym_n 12
  init_next_step h_run h_step_13 s13
  replace h_step_13 := h_step_13.symm
  rw [aes_hw_encrypt_program.stepi_eq_0x79f5d0] at h_step_13<;> try assumption
  simp only [round_addr] at h_rounds
  sym_aggregate at h_step_13
  simp (config := {ground := true}) only [h_rounds.symm, minimal_theory] at h_step_13
  (intro_fetch_decode_lemmas h_step_13 h_s12_program "h_s12")
  -- -- Add hypotheses that are needed for next loop iteration
  -- -- This is an aggregated result
  -- have h_s13_x3 : read_gpr 32 3#5 s13 = 10#32 := by
  --   simp only [h_s1_x3, h_s2_non_effects, h_s3_non_effects, h_s4_x3,
  --              h_s5_non_effects, h_s6_non_effects, h_s7_non_effects,
  --              h_s8_non_effects, h_s9_x3, h_s10_non_effects,
  --              h_s11_non_effects, h_s12_non_effects, h_step_13,
  --              state_simp_rules, bitvec_rules, minimal_theory]
  --   simp (config := {ground := true}) only [h_rounds.symm, minimal_theory]
  --
  sym_n 7 at s13
  init_next_step h_run h_step_21 s21
  replace h_step_21 := h_step_21.symm
  rw [aes_hw_encrypt_program.stepi_eq_0x79f5d0] at h_step_21<;> try assumption
  -- simp only [state_simp_rules] at h_s13_x3
  sym_aggregate at h_step_21
  simp (config := {ground := true}) only [minimal_theory] at h_step_21
  (intro_fetch_decode_lemmas h_step_21 h_s20_program "h_s20")
  -- Add hypotheses that are needed for next loop iteration
  -- This is an aggregated result
  have h_s21_x3 : read_gpr 32 3#5 s21 = 8#32 := by
    simp only [h_s20_non_effects, h_s19_non_effects, h_s18_non_effects,
               h_s17_x3, h_s16_non_effects, h_s15_non_effects,
               h_s14_non_effects, h_step_21,
               state_simp_rules, bitvec_rules, minimal_theory]
    simp (config := {ground := true}) only [h_s13_x3, minimal_theory]
  --
  sym_n 7 at s21
  init_next_step h_run h_step_29 s29
  replace h_step_29 := h_step_29.symm
  rw [aes_hw_encrypt_program.stepi_eq_0x79f5d0] at h_step_29<;> try assumption
  simp only [state_simp_rules] at h_s21_x3
  simp only [h_s28_non_effects, h_s27_non_effects, h_s26_non_effects,
             h_s25_flagN, h_s25_flagV, h_s25_flagZ,
             h_s25_flagC, h_s24_non_effects, h_s23_non_effects,
             h_s22_non_effects, state_simp_rules, bitvec_rules,
             minimal_theory,
             -- hypothesis that states x3's value
             h_s21_x3] at h_step_29
  simp (config := {ground := true}) only [minimal_theory] at h_step_29
  (intro_fetch_decode_lemmas h_step_29 h_s28_program "h_s28")
  -- Add hypotheses that are needed for next loop iteration
  -- This is an aggregated result
  have h_s29_x3 : read_gpr 32 3#5 s29 = 6#32 := by
    simp only [h_s28_non_effects, h_s27_non_effects, h_s26_non_effects,
               h_s25_x3, h_s24_non_effects, h_s23_non_effects,
               h_s22_non_effects, h_step_29,
               state_simp_rules, bitvec_rules, minimal_theory]
    simp (config := {ground := true}) only [h_s21_x3, minimal_theory]
  --
  sym_n 7 at s29
  init_next_step h_run h_step_37 s37
  replace h_step_37 := h_step_37.symm
  rw [aes_hw_encrypt_program.stepi_eq_0x79f5d0] at h_step_37<;> try assumption
  simp only [state_simp_rules] at h_s29_x3
  simp only [h_s36_non_effects, h_s35_non_effects, h_s34_non_effects,
             h_s33_flagN, h_s33_flagV, h_s33_flagZ,
             h_s33_flagC, h_s32_non_effects, h_s31_non_effects,
             h_s30_non_effects, state_simp_rules, bitvec_rules,
             minimal_theory,
             -- hypothesis that states x3's value
             h_s29_x3] at h_step_37
  simp (config := {ground := true}) only [minimal_theory] at h_step_37
  (intro_fetch_decode_lemmas h_step_37 h_s36_program "h_s36")
  -- Add hypotheses that are needed for next loop iteration
  -- This is an aggregated result
  have h_s37_x3 : read_gpr 32 3#5 s37 = 4#32 := by
    simp only [h_s36_non_effects, h_s35_non_effects, h_s34_non_effects,
               h_s33_x3, h_s32_non_effects, h_s31_non_effects,
               h_s30_non_effects, h_step_37,
               state_simp_rules, bitvec_rules, minimal_theory]
    simp (config := {ground := true}) only [h_s29_x3, minimal_theory]
  --
  sym_n 7 at s37
  init_next_step h_run h_step_45 s45
  replace h_step_45 := h_step_45.symm
  rw [aes_hw_encrypt_program.stepi_eq_0x79f5d0] at h_step_45<;> try assumption
  simp only [state_simp_rules] at h_s37_x3
  simp only [h_s44_non_effects, h_s43_non_effects, h_s42_non_effects,
             h_s41_flagN, h_s41_flagV, h_s41_flagZ,
             h_s41_flagC, h_s40_non_effects, h_s39_non_effects,
             h_s38_non_effects, state_simp_rules, bitvec_rules,
             minimal_theory,
             -- hypothesis that states x3's value
             h_s37_x3] at h_step_45
  simp (config := {ground := true}) only [minimal_theory] at h_step_45
  (intro_fetch_decode_lemmas h_step_45 h_s44_program "h_s44")
  -- Add hypotheses that are needed for next loop iteration
  -- This is an aggregated result
  have h_s45_x3 : read_gpr 32 3#5 s45 = 2#32 := by
    simp only [h_s44_non_effects, h_s43_non_effects, h_s42_non_effects,
               h_s41_x3, h_s40_non_effects, h_s39_non_effects,
               h_s38_non_effects, h_step_45,
               state_simp_rules, bitvec_rules, minimal_theory]
    simp (config := {ground := true}) only [h_s37_x3, minimal_theory]
  --
  sym_n 7 at s45
  init_next_step h_run h_step_53 s53
  replace h_step_53 := h_step_53.symm
  rw [aes_hw_encrypt_program.stepi_eq_0x79f5d0] at h_step_53<;> try assumption
  simp only [state_simp_rules] at h_s45_x3
  simp only [h_s52_non_effects, h_s51_non_effects, h_s50_non_effects,
             h_s49_flagN, h_s49_flagV, h_s49_flagZ,
             h_s49_flagC, h_s48_non_effects, h_s47_non_effects,
             h_s46_non_effects, state_simp_rules, bitvec_rules,
             minimal_theory,
             -- hypothesis that states x3's value
             h_s45_x3] at h_step_53
  simp (config := {ground := true}) only [minimal_theory] at h_step_53
  (intro_fetch_decode_lemmas h_step_53 h_s52_program "h_s52")
  --
  sym_n 7 at s53
  done
