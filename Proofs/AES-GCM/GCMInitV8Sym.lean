/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Proofs.«AES-GCM».GCMInitV8Pre
import Tactics.Sym
import Tactics.Aggregate
import Specs.GCMV8

namespace GCMInitV8Program

set_option bv.ac_nf false

abbrev H_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 1#5) s
abbrev Htable_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 0#5) s

set_option maxRecDepth 8000 in
-- set_option profiler true in
theorem gcm_init_v8_program_run_152 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_init_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_init_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run gcm_init_v8_program.length s0)
    (_h_mem : Memory.Region.pairwiseSeparate
      [ ⟨(H_addr s0), 128⟩,
        ⟨(Htable_addr s0), 2048⟩ ])
    : read_err sf = .None := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_init_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 152
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
set_option sat.timeout 120 in
-- set_option pp.deepTerms true in
-- set_option pp.maxSteps 10000 in
-- set_option trace.profiler true in
-- set_option linter.unusedVariables false in
-- set_option profiler true in
theorem gcm_init_v8_program_correct (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_init_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_init_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run gcm_init_v8_program.length s0)
    (h_mem : Memory.Region.pairwiseSeparate
      [ ⟨(H_addr s0), 128⟩,
        ⟨(Htable_addr s0), 2048⟩ ])
    : -- effects
      -- no instruction decoding error
      read_err sf = .None
      -- program is unchanged
    ∧ sf.program = gcm_init_v8_program
      -- SP is still aligned
    ∧ CheckSPAlignment sf
      -- PC is updated
    ∧ read_pc sf = read_gpr 64 30#5 s0
    -- Htable_addr ptr is moved to the start of the 10th element
    ∧ Htable_addr sf = Htable_addr s0 + (9 * 16#64)
    -- H_addr ptr stays the same
    ∧ H_addr sf = H_addr s0
    -- v20 - v31 stores results of Htable
    ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
      read_sfp 128 20#5 sf =
      (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 0
    --
    -- TODO: Commenting out memory related conjuncts since it seems
    -- to make symbolic execution stuck
    --   -- First 12 elements in Htable is correct
    -- ∧ read_mem_bytes 192 (Htable_addr s0) sf
    --   = revflat (GCMV8.GCMInitV8 (read_mem_bytes 16 (H_addr s0) s0))
    --
    -- non-effects
    -- State values that shouldn't change do not change
    -- TODO: figure out all registers that are used ...
    -- ∧ (∀ (f : StateField), ¬ (f = StateField.PC) ∧
    --                        ¬ (f = (StateField.GPR 29#5)) →
    --     r f sf = r f s0)
    --
    -- -- Memory safety: memory location that should not change did
    -- -- not change
    -- -- The addr exclude output region Htable
    -- ∧ (∀ (n : Nat) (addr : BitVec 64) (h: addr < (Htable_addr sf) ∨ addr >= (Htable_addr sf) + 128*12),
    --     read_mem_bytes n addr sf = read_mem_bytes n addr s0)
    := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_init_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 152
  simp only [Htable_addr, state_value] -- TODO: state_value is needed, why
  apply And.intro  
  · bv_decide
  · sorry
  -- [Shilpi] Commenting out the following because the CI fails with 
  -- "INTERNAL PANIC: out of memory"
  /-
    simp only
    [shift_left_common_aux_64_2
    , shift_right_common_aux_64_2_tff
    , shift_right_common_aux_32_4_fff
    , DPSFP.AdvSIMDExpandImm
    , DPSFP.dup_aux_0_4_32]
    generalize read_mem_bytes 16 (r (StateField.GPR 1#5) s0) s0 = Hinit
    -- change the type of Hinit to be BitVec 128, assuming that's def-eq
    change BitVec 128 at Hinit
    simp only [GCMV8.GCMInitV8, GCMV8.lo, List.get!, GCMV8.hi,
      GCMV8.gcm_init_H, GCMV8.refpoly, GCMV8.pmod, GCMV8.pmod.pmodTR,
      GCMV8.reduce, GCMV8.degree, GCMV8.degree.degreeTR]
    simp only [Nat.reduceAdd, BitVec.ushiftRight_eq, BitVec.reduceExtracLsb',
      BitVec.reduceHShiftLeft, BitVec.reduceAppend, BitVec.reduceHShiftRight, BitVec.ofNat_eq_ofNat,
      BitVec.reduceEq, ↓reduceIte, BitVec.zero_eq, Nat.sub_self, BitVec.ushiftRight_zero_eq,
      BitVec.reduceAnd, BitVec.toNat_ofNat, Nat.pow_one, Nat.reduceMod, Nat.mul_zero, Nat.add_zero,
      Nat.zero_mod, Nat.zero_add, Nat.sub_zero, Nat.mul_one, Nat.zero_mul, Nat.one_mul,
      Nat.reduceSub, BitVec.reduceMul, BitVec.reduceXOr, BitVec.mul_one, Nat.add_one_sub_one,
      BitVec.one_mul]
    -- bv_check "GCMInitV8Sym.lean-GCMInitV8Program.gcm_init_v8_program_correct-117-4.lrat"
    -- TODO: proof works in vscode but timeout in the CI -- need to investigate further
    -/

