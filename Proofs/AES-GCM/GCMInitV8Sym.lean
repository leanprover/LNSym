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
import Tactics.ExtractGoal

namespace GCMInitV8Program

set_option bv.ac_nf false

abbrev H_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 1#5) s
abbrev Htable_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 0#5) s

abbrev lo (x : BitVec 128) : BitVec 64 := BitVec.extractLsb' 0 64 x
abbrev hi (x : BitVec 128) : BitVec 64 := BitVec.extractLsb' 64 64 x

-- define a function that represents gcm_init_H in the assembly
def gcm_init_H_asm (H : BitVec 128) : BitVec 128 :=
  let v19 := 0xe1e1e1e1e1e1e1e1e1e1e1e1e1e1e1e1#128
  let v19 := BitVec.shiftLeft (hi v19) 57 ++ BitVec.shiftLeft (lo v19) 57
  let v18 := BitVec.ushiftRight (hi v19) 63 ++ BitVec.ushiftRight (lo v19) 63
  let v17_1 := BitVec.extractLsb' 32 32 (hi H)
  let v16 := (lo v19) ++ (hi v18)
  let v18 := BitVec.ushiftRight (hi H) 63 ++ BitVec.ushiftRight (lo H) 63
  let v17 := BitVec.sshiftRight v17_1 31 ++ BitVec.sshiftRight v17_1 31 ++
    BitVec.sshiftRight v17_1 31 ++ BitVec.sshiftRight v17_1 31
  let v18 := v18 &&& v16
  let v3 := (hi H) <<< 1 ++ (lo H) <<< 1
  let v18 := (lo v18) ++ (hi v18)
  let v16 := v16 &&& v17
  let v3 := v3 ||| v18
  let v20 := v3 ^^^ v16
  v20

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
set_option sat.timeout 120 in
set_option debug.byAsSorry true in
theorem gcm_init_H_asm_gcm_int_H_equiv (x : BitVec 128) :
  GCMV8.gcm_init_H x = gcm_init_H_asm x := by
  simp only [GCMV8.gcm_init_H, gcm_init_H_asm, hi, lo,
    GCMV8.pmod, GCMV8.refpoly, GCMV8.pmod.pmodTR,
    GCMV8.reduce, GCMV8.degree, GCMV8.degree.degreeTR]
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.reduceEq, ↓reduceIte, Nat.sub_self,
    BitVec.ushiftRight_zero_eq, BitVec.reduceAnd, BitVec.reduceExtracLsb', BitVec.toNat_ofNat,
    Nat.pow_one, Nat.reduceMod, Nat.mul_zero, Nat.add_zero, BitVec.reduceHShiftRight, Nat.zero_mod,
    Nat.zero_add, Nat.sub_zero, Nat.mul_one, Nat.zero_mul, Nat.one_mul, Nat.reduceSub,
    BitVec.and_self, BitVec.zero_and, BitVec.reduceMul, BitVec.xor_zero, BitVec.mul_one,
    BitVec.zero_xor, BitVec.reduceHShiftLeft, Nat.add_one_sub_one, BitVec.one_mul, BitVec.reduceXOr,
    BitVec.ushiftRight_eq, BitVec.shiftLeft_eq, BitVec.reduceAppend]
  bv_decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem gcm_polyval_mul_eq_polynomial_mult (x y : BitVec 128) :
  GCMV8.gcm_polyval_mul x y = DPSFP.polynomial_mult x y := by
  sorry

-- The following represents the assembly version of gcm_polyval
def gcm_polyval_asm (x : BitVec 128) (y : BitVec 128) : BitVec 128 :=
  let v19 := 0xe1e1e1e1e1e1e1e1e1e1e1e1e1e1e1e1#128
  let v19 := BitVec.shiftLeft (hi v19) 57 ++ BitVec.shiftLeft (lo v19) 57
  let v16 := ((lo x) ^^^ (hi x)) ++ ((hi x) ^^^ (lo x))
  let v17 := ((lo y) ^^^ (hi y)) ++ ((hi y) ^^^ (lo y))
  let x := (lo x) ++ (hi x)
  let y := (lo y) ++ (hi y)
  let v0 := DPSFP.polynomial_mult (hi x) (hi y)
  let v2 := DPSFP.polynomial_mult (lo x) (lo y)
  let v1 := DPSFP.polynomial_mult (lo v16) (lo v17)
  let v16 := (lo v2) ++ (hi v0)
  let v18 := v0 ^^^ v2
  let v1 := v1 ^^^ v16
  let v1 := v1 ^^^ v18
  let v18 := DPSFP.polynomial_mult (lo v0) (lo v19)
  let v2 := BitVec.partInstall 0 64 (hi v1) v2
  let v1 := BitVec.partInstall 64 64 (lo v0) v1
  let v0 := v1 ^^^ v18
  let v18 := (lo v0) ++ (hi v0)
  let v0 := DPSFP.polynomial_mult (lo v0) (lo v19)
  let v18 := v18 ^^^ v2
  let v16 := v0 ^^^ v18
  let v23 := v16
  v23

theorem extractLsb'_of_append_hi (x y : BitVec 64) :
  BitVec.extractLsb' 64 64 (x ++ y) = x := by
  bv_decide

theorem extractLsb'_of_append_lo (x y : BitVec 64) :
  BitVec.extractLsb' 0 64 (x ++ y) = y := by
  bv_decide

-- https://kib.kiev.ua/x86docs/Intel/WhitePapers/323640-001.pdf
def karatsuba_multiplication (x : BitVec 128) (y : BitVec 128) : BitVec 256 :=
  let A1 := hi x
  let A0 := lo x
  let B1 := hi y
  let B0 := lo y
  let A1B1 := DPSFP.polynomial_mult A1 B1
  let C1 := hi A1B1
  let C0 := lo A1B1
  let A0B0 := DPSFP.polynomial_mult A0 B0
  let D1 := hi A0B0
  let D0 := lo A0B0
  let A1A0B1B0 := DPSFP.polynomial_mult (A1 ^^^ A0) (B1 ^^^ B0)
  let E1 := hi A1A0B1B0
  let E0 := lo A1A0B1B0
  C1 ++ (C0 ^^^ C1 ^^^ D1 ^^^ E1) ++ (D1 ^^^ C0 ^^^ D0 ^^^ E0) ++ D0

theorem karatsuba_multiplication_equiv (x : BitVec 128) (y : BitVec 128) :
  DPSFP.polynomial_mult x y = karatsuba_multiplication x y := by sorry

-- TODO: look into https://github.com/GaloisInc/saw-script/tree/master/rme for RME
-- https://github.com/GaloisInc/aws-lc-verification/blob/0efc892de9a4d2660067ab02fdcef5993ff5184a/SAW/proof/AES/goal-rewrites.saw#L200-L214
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem gcm_polyval_asm_gcm_polyval_equiv (x : BitVec 128) (y : BitVec 128) :
  GCMV8.gcm_polyval x y = gcm_polyval_asm x y := by
  simp only [GCMV8.gcm_polyval, gcm_polyval_asm, hi, lo,
    extractLsb'_of_append_hi, extractLsb'_of_append_lo, BitVec.partInstall,
    gcm_polyval_mul_eq_polynomial_mult]
  simp only [Nat.reduceAdd, BitVec.reduceAllOnes, BitVec.truncate_eq_setWidth,
    BitVec.reduceSetWidth, BitVec.reduceHShiftLeft, BitVec.reduceNot, BitVec.reduceExtracLsb',
    BitVec.shiftLeft_eq, BitVec.shiftLeft_zero_eq]
  simp only [karatsuba_multiplication_equiv, karatsuba_multiplication, hi, lo]
  generalize h_A1 : BitVec.extractLsb' 64 64 x = A1
  generalize h_A0 : BitVec.extractLsb' 0 64 x = A0
  generalize h_B1 : BitVec.extractLsb' 64 64 y = B1
  generalize h_B0 : BitVec.extractLsb' 0 64 y = B0
  generalize h_A1A0B1B0 : DPSFP.polynomial_mult (A1 ^^^ A0) (B1 ^^^ B0) = A1A0B1B0
  generalize h_A1B1 : DPSFP.polynomial_mult A1 B1 = A1B1
  generalize h_A0B0 : DPSFP.polynomial_mult A0 B0 = A0B0
  sorry

theorem gcm_polyval_asm_associativity (x : BitVec 128) (y : BitVec 128) (z : BitVec 128) :
  gcm_polyval_asm x (gcm_polyval_asm y z) = gcm_polyval_asm (gcm_polyval_asm x y) z := by
  sorry

-- Taken from gcm_gmult_v8
theorem pmull_op_e_0_eize_64_elements_1_size_128_eq (x y : BitVec 64) :
  DPSFP.pmull_op 0 64 1 x y 0#128 =
  DPSFP.polynomial_mult x y := by
  unfold DPSFP.pmull_op
  simp (config := {ground := true}) only [minimal_theory]
  unfold DPSFP.pmull_op
  simp (config := {ground := true}) only [minimal_theory]
  simp only [state_simp_rules, bitvec_rules]
  done

theorem extractLsb'_of_append_mid (x : BitVec 128) (y : BitVec 128):
  BitVec.extractLsb' 64 128 (x ++ y)
  = BitVec.extractLsb' 0 64 x ++ BitVec.extractLsb' 64 64 y := by
  bv_decide

theorem extractLsb'_append4_1 (x : BitVec 32) :
  (BitVec.extractLsb' 0 32 (x ++ x ++ x ++ x)) = x := by bv_decide

theorem extractLsb'_append4_2 (x : BitVec 32) :
  (BitVec.extractLsb' 32 32 (x ++ x ++ x ++ x)) = x := by bv_decide

theorem extractLsb'_append4_3 (x : BitVec 32) :
  (BitVec.extractLsb' 64 32 (x ++ x ++ x ++ x)) = x := by bv_decide

theorem extractLsb'_append4_4 (x : BitVec 32) :
  (BitVec.extractLsb' 96 32 (x ++ x ++ x ++ x)) = x := by bv_decide

theorem setWidth_extractLsb'_equiv_64_128 (x : BitVec 128) :
  (BitVec.setWidth 64 x) = BitVec.extractLsb' 0 64 x := by bv_decide

theorem append_of_extractLsb'_of_append (x : BitVec 64) (y : BitVec 64) :
  (BitVec.extractLsb' 0 64 (x ++ y)) ++ (BitVec.extractLsb' 64 64 (x ++ y))
  = y ++ x := by bv_decide

theorem extractLsb'_of_xor_of_append (x : BitVec 64) (y : BitVec 64) :
  (BitVec.extractLsb' 0 64 ((x ++ y) ^^^ (y ++ x)))
  = (x ^^^ y) := by bv_decide

theorem extractLsb'_of_xor_of_append_hi (x : BitVec 64) (y : BitVec 64) :
  (BitVec.extractLsb' 64 64 ((x ++ y) ^^^ (y ++ x)))
  = (x ^^^ y) := by bv_decide

theorem extractLsb'_of_xor_of_extractLsb'_lo (x : BitVec 128):
  (BitVec.extractLsb' 0 64
      (x ^^^ (BitVec.extractLsb' 0 64 x ++ BitVec.extractLsb' 64 64 x)))
      = BitVec.extractLsb' 64 64 x ^^^ BitVec.extractLsb' 0 64 x := by
      bv_decide

theorem extractLsb'_of_xor_of_extractLsb'_hi (x : BitVec 128):
  (BitVec.extractLsb' 64 64
      (x ^^^ (BitVec.extractLsb' 0 64 x ++ BitVec.extractLsb' 64 64 x)))
      = BitVec.extractLsb' 64 64 x ^^^ BitVec.extractLsb' 0 64 x := by
      bv_decide

syntax "gcm_init_v8_tac" : tactic

macro_rules
  | `(tactic| gcm_init_v8_tac) =>
  `(tactic|
    (sorry))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
set_option sat.timeout 120 in
-- set_option pp.deepTerms true in
-- set_option pp.maxSteps 1000000 in
-- set_option trace.profiler true in
-- set_option linter.unusedVariables false in
-- set_option profiler true in
theorem gcm_init_v8_program_correct (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_init_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_init_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    -- (h_run : sf = run gcm_init_v8_program.length s0)
    (h_run : sf = run 78 s0)
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
    -- ∧ read_pc sf = read_gpr 64 30#5 s0
    -- Htable_addr ptr is moved to the start of the 10th element
    -- ∧ Htable_addr sf = Htable_addr s0 + (9 * 16#64)
    -- H_addr ptr stays the same
    ∧ H_addr sf = H_addr s0
    -- v20 - v31 stores results of Htable
    ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
      read_sfp 128 20#5 sf =
      (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 0
    ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
      read_sfp 128 21#5 sf =
      (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 1
    ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
      read_sfp 128 22#5 sf =
      (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 2
    ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
      read_sfp 128 23#5 sf =
      (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 3
    -- ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
    --   read_sfp 128 24#5 sf =
    --   (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 4
    -- ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
    --   read_sfp 128 25#5 sf =
    --   (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 5
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
  -- Step 1: simulate up to the instruction that saves the value for H0_rev
  -- Verify that v20 stores H0_rev
  sym_n 17
  -- simp only [Htable_addr, state_value] -- TODO: state_value is needed, why
  generalize x1_h: (Memory.read_bytes 16 (r (StateField.GPR 1#5) s0) s0.mem) = x1 at *
  change BitVec 128 at x1
  -- value of q19
  have h_e1 : (r (StateField.SFP 19#5) s17) =
    let tmp := 0xe1e1e1e1e1e1e1e1e1e1e1e1e1e1e1e1#128
    BitVec.shiftLeft (hi tmp) 57 ++ BitVec.shiftLeft (lo tmp) 57 := by
    have q0 : (r (StateField.SFP 19#5) s17) = (r (StateField.SFP 19#5) s3) := by sym_aggregate
    simp only [q0, h_s3_q19, h_s3_non_effects, h_s2_q19, shift_left_common_aux_64_2]
    simp only [Nat.reduceAdd, BitVec.reduceExtracLsb', BitVec.reduceHShiftLeft,
      BitVec.reduceAppend, BitVec.shiftLeft_eq, hi, lo]
  -- value of H0
  have h_H0 : r (StateField.SFP 20#5) s17 =
    let x_rev := (lo x1) ++ (hi x1)
    lo (gcm_init_H_asm x_rev) ++ hi (gcm_init_H_asm x_rev) := by
    sym_aggregate
    have q0: (read_mem_bytes 16 (r (StateField.GPR 1#5) s0) s0) =
      (Memory.read_bytes 16 (r (StateField.GPR 1#5) s0) s0.mem) := by rfl
    simp only [q0, x1_h]
    simp only [shift_left_common_aux_64_2, shift_right_common_aux_64_2_tff,
      shift_right_common_aux_32_4_fff, DPSFP.AdvSIMDExpandImm,
      DPSFP.dup_aux_0_4_32, BitVec.partInstall]
    -- simplifying LHS
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi,
      extractLsb'_of_append_lo, extractLsb'_append4_1, extractLsb'_append4_2,
      extractLsb'_append4_3, extractLsb'_append4_4,
      setWidth_extractLsb'_equiv_64_128, extractLsb'_of_xor_of_append]
    -- simplifying RHS
    simp only [lo, hi, gcm_init_H_asm, BitVec.partInstall,
      extractLsb'_of_append_hi, extractLsb'_of_append_lo]
    simp (config := {ground := true}) only
  -- Step 2: simulate up to H1 and H2_rev and verify
  sym_n 20
  have h_v16_s20_hi : BitVec.extractLsb' 64 64 (r (StateField.SFP 16#5) s20) =
    let x_rev := (lo x1) ++ (hi x1)
    hi (gcm_init_H_asm x_rev) ^^^ lo (gcm_init_H_asm x_rev) := by
    simp (config := {decide := true}) only [
      h_s20_q16, h_s20_non_effects,
      h_s19_non_effects, h_s18_q16, h_s18_non_effects,
      extractLsb'_of_append_mid]
    simp only [h_H0]
    bv_decide
  have h_v16_s20_lo : BitVec.extractLsb' 0 64 (r (StateField.SFP 16#5) s20) =
    let x_rev := (lo x1) ++ (hi x1)
    lo (gcm_init_H_asm x_rev) ^^^ hi (gcm_init_H_asm x_rev):= by
    simp (config := {decide := true}) only [
      h_s20_q16, h_s20_non_effects,
      h_s19_non_effects, h_s18_q16, h_s18_non_effects,
      extractLsb'_of_append_mid]
    simp only [h_H0]
    bv_decide
  have h_v17_s34 : (r (StateField.SFP 17#5) s34) =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    gcm_polyval_asm H0 H0 := by
    simp (config := {decide := true}) only [
      extractLsb'_of_append_mid,
      h_s34_q17, h_s34_non_effects,
      h_s33_q18, h_s33_non_effects,
      h_s32_q0,  h_s32_non_effects,
      h_s31_q18, h_s31_non_effects,
      h_s30_q0, h_s30_non_effects,
      h_s29_q1, h_s29_non_effects,
      h_s28_q2, h_s28_non_effects,
      h_s27_q18, h_s27_non_effects,
      h_s26_q1, h_s26_non_effects,
      h_s25_q1, h_s25_non_effects,
      h_s24_q18, h_s24_non_effects,
      h_s23_q17, h_s23_non_effects,
      h_s22_q1, h_s22_non_effects,
      h_s21_q2, h_s21_non_effects,
      h_s20_q16, h_s20_non_effects,
      h_s19_q0, h_s19_non_effects,
      h_s18_q16, h_s18_non_effects,
      ]
    simp only [h_H0, h_e1]
    generalize (gcm_init_H_asm (lo x1 ++ hi x1)) = H0
    -- simplify LHS
    simp only [pmull_op_e_0_eize_64_elements_1_size_128_eq,
      BitVec.partInstall, lo, hi]
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi,
       extractLsb'_of_append_lo, setWidth_extractLsb'_equiv_64_128,
       extractLsb'_of_xor_of_append, extractLsb'_of_xor_of_append_hi]
    simp only [Nat.reduceAdd, BitVec.reduceAllOnes, BitVec.truncate_eq_setWidth,
      BitVec.reduceSetWidth, BitVec.reduceHShiftLeft, BitVec.reduceNot,
      BitVec.reduceExtracLsb', BitVec.shiftLeft_eq, BitVec.shiftLeft_zero_eq]
    -- simplify RHS
    simp only [gcm_polyval_asm, BitVec.partInstall, hi, lo]
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi,
      extractLsb'_of_append_lo, setWidth_extractLsb'_equiv_64_128,
      extractLsb'_of_xor_of_append]
    simp only [Nat.reduceAdd, BitVec.reduceAllOnes, BitVec.truncate_eq_setWidth,
      BitVec.reduceSetWidth, BitVec.reduceHShiftLeft, BitVec.reduceNot,
      BitVec.reduceExtracLsb', BitVec.shiftLeft_eq, BitVec.shiftLeft_zero_eq]
  have h_v17_s36 : BitVec.extractLsb' 0 64 (r (StateField.SFP 17#5) s36) =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    (hi H2) ^^^ (lo H2) := by
    simp (config := {decide := true}) only [
      extractLsb'_of_append_mid,
      h_s36_q17, h_s36_non_effects,
      h_s35_q22, h_s35_non_effects,
      extractLsb'_of_xor_of_extractLsb'_lo, ]
    simp only [h_v17_s34, h_e1]
  -- value of H1
  have h_H1 : r (StateField.SFP 21#5) s37 =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    ((hi H2) ^^^ (lo H2)) ++ ((hi H0) ^^^ (lo H0)) := by
    simp (config := {decide := true}) only [
      h_s37_q21,
      h_s37_non_effects,
      extractLsb'_of_append_mid, ]
    have q: r (StateField.SFP 16#5) s36 = r (StateField.SFP 16#5) s20 := by sym_aggregate
    simp only [q, h_v17_s36, h_v16_s20_hi]
  have h_H2 : r (StateField.SFP 22#5) s37 =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    (lo H2) ++ (hi H2) := by
    simp (config := {decide := true}) only [
      h_s37_non_effects, h_s36_non_effects,
      h_s35_q22, h_s35_non_effects,
      extractLsb'_of_append_mid, ]
    simp only [h_v17_s34, hi, lo,
      extractLsb'_of_append_hi, extractLsb'_of_append_lo]
  -- Step 3: simulate up to H3_rev, H4 and H5_rev and verify
  sym_n 40
  have h_v16_s68 : r (StateField.SFP 16#5) s68 =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    gcm_polyval_asm H0 H2 := by
    -- TODO: I want to sym_aggregate, but only aggregate to last step,
    -- instead of all the way to the top
    -- sym_aggregate
    simp (config := {decide := true}) only [
      h_s68_q16, h_s68_non_effects,
      h_s67_non_effects, h_s66_q18, h_s66_non_effects,
      h_s65_non_effects, h_s64_q0, h_s64_non_effects,
      h_s63_non_effects, h_s62_q18, h_s62_non_effects,
      h_s61_non_effects, h_s60_q0, h_s60_non_effects,
      h_s59_non_effects, h_s58_q1, h_s58_non_effects,
      h_s57_non_effects, h_s56_q2, h_s56_non_effects,
      h_s55_non_effects, h_s54_non_effects,
      h_s53_q18, h_s53_non_effects,
      h_s52_q1, h_s52_non_effects,
      h_s51_non_effects, h_s50_non_effects,
      h_s49_q1, h_s49_non_effects,
      h_s48_q18, h_s48_non_effects,
      h_s47_non_effects, h_s46_q16, h_s46_non_effects,
      h_s45_non_effects, h_s44_q1, h_s44_non_effects,
      h_s43_non_effects, h_s42_q2, h_s42_non_effects,
      h_s41_non_effects, h_s40_q0, h_s40_non_effects,
      h_s39_non_effects, h_s38_non_effects, h_s37_non_effects]
    have q0 : r (StateField.SFP 20#5) s36 = r (StateField.SFP 20#5) s17 := by sym_aggregate
    have q1 : r (StateField.SFP 22#5) s36 = r (StateField.SFP 22#5) s37 := by sym_aggregate
    have q2_1 : r (StateField.SFP 16#5) s36 = r (StateField.SFP 16#5) s20 := by sym_aggregate
    have q2 : BitVec.extractLsb' 0 64 (r (StateField.SFP 16#5) s36) =
      let x_rev := (lo x1) ++ (hi x1)
      let H0 := gcm_init_H_asm x_rev
      (hi H0) ^^^ (lo H0) := by
      simp [ q2_1, h_v16_s20_lo ]
      simp only [hi, lo]
      bv_decide
    have q4 : (r (StateField.SFP 19#5) s36) = (r (StateField.SFP 19#5) s17) := by sym_aggregate
    simp only [q0, h_H0, q1, h_H2, q2, h_v17_s36, q4, h_e1]
    generalize (gcm_init_H_asm (lo x1 ++ hi x1)) = H0
    -- simplifying LHS
    simp only [pmull_op_e_0_eize_64_elements_1_size_128_eq,
      gcm_polyval_asm_gcm_polyval_equiv,
      hi, lo, BitVec.partInstall]
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi,
      extractLsb'_of_append_lo, setWidth_extractLsb'_equiv_64_128,
      extractLsb'_of_xor_of_append]
    generalize (gcm_polyval_asm H0 H0) = H2
    simp (config := {ground := true}) only
    -- simplifying RHS
    simp only [gcm_polyval_asm, BitVec.partInstall]
    simp only [hi, lo] at *
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi,
      extractLsb'_of_append_lo, setWidth_extractLsb'_equiv_64_128,
      extractLsb'_of_xor_of_append]
    -- simplify all
    simp only [Nat.reduceAdd, BitVec.shiftLeft_zero_eq, BitVec.reduceAllOnes,
      BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth, BitVec.reduceHShiftLeft, BitVec.reduceNot,
      BitVec.reduceExtracLsb', BitVec.shiftLeft_eq]
  have h_v17_s69 : r (StateField.SFP 17#5) s69 =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    gcm_polyval_asm H2 H2 := by
    simp (config := {decide := true}) only [
      h_s69_q17, h_s69_non_effects, h_s68_non_effects,
      h_s67_q4, h_s67_non_effects,
      h_s66_non_effects, h_s65_q5, h_s65_non_effects,
      h_s64_non_effects, h_s63_q4, h_s63_non_effects,
      h_s62_non_effects, h_s61_q5, h_s61_non_effects,
      h_s60_non_effects, h_s59_q6, h_s59_non_effects,
      h_s58_non_effects, h_s57_q7, h_s57_non_effects,
      h_s56_non_effects, h_s55_q4, h_s55_non_effects,
      h_s54_q6, h_s54_non_effects,
      h_s53_non_effects, h_s52_non_effects,
      h_s51_q6, h_s51_non_effects,
      h_s50_q4, h_s50_non_effects,
      h_s49_non_effects, h_s48_non_effects,
      h_s47_q17, h_s47_non_effects,
      h_s46_non_effects, h_s45_q6, h_s45_non_effects,
      h_s44_non_effects, h_s43_q7, h_s43_non_effects,
      h_s42_non_effects, h_s41_q5, h_s41_non_effects,
      h_s40_non_effects, h_s39_non_effects, h_s38_non_effects,
      ]
    have q0 : (r (StateField.SFP 19#5) s37) = (r (StateField.SFP 19#5) s17) := by sym_aggregate
    have q1 : (r (StateField.SFP 17#5) s37) = (r (StateField.SFP 17#5) s36) := by sym_aggregate
    simp only [q0, h_H2, h_e1, q1, h_v17_s36]
    -- simplifying LHS
    simp only [pmull_op_e_0_eize_64_elements_1_size_128_eq,
      gcm_polyval_asm_gcm_polyval_equiv,
      hi, lo, BitVec.partInstall]
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi,
      extractLsb'_of_append_lo, setWidth_extractLsb'_equiv_64_128,
      extractLsb'_of_xor_of_append]
    simp (config := {ground := true}) only
    -- simplifying RHS
    simp only [gcm_polyval_asm, BitVec.partInstall]
    simp only [hi, lo] at *
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi,
      extractLsb'_of_append_lo, setWidth_extractLsb'_equiv_64_128,
      extractLsb'_of_xor_of_append]
    -- simplify all
    simp only [Nat.reduceAdd, BitVec.shiftLeft_zero_eq, BitVec.reduceAllOnes,
      BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth, BitVec.reduceHShiftLeft,
      BitVec.reduceNot, BitVec.reduceExtracLsb', BitVec.shiftLeft_eq]
  have h_H3 : r (StateField.SFP 23#5) s77 =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    let H3 := gcm_polyval_asm H0 H2
    (lo H3) ++ (hi H3) := by
    simp (config := {decide := true}) only [
      h_s77_non_effects, h_s76_non_effects, h_s75_non_effects,
      h_s74_non_effects, h_s73_non_effects, h_s72_non_effects,
      h_s71_non_effects, h_s70_q23, h_s70_non_effects,
      h_s69_non_effects, extractLsb'_of_append_mid ]
    simp only [h_v16_s68]
  have h_H5 : r (StateField.SFP 25#5) s77 =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    let H3 := gcm_polyval_asm H0 H2
    let H5 := gcm_polyval_asm H0 H3
    (lo H5) ++ (hi H5) := by
    simp (config := {decide := true}) only [
      h_s77_non_effects, h_s76_non_effects,
      h_s75_non_effects, h_s74_non_effects,
      h_s73_non_effects, h_s72_non_effects,
      h_s71_q25, h_s71_non_effects,
      extractLsb'_of_append_mid,]
    have q : r (StateField.SFP 17#5) s70 = r (StateField.SFP 17#5) s69 := by sym_aggregate
    simp only [q, h_v17_s69, gcm_polyval_asm_associativity]
  have h_H4 : r (StateField.SFP 24#5) s77 =
    let x_rev := (lo x1) ++ (hi x1)
    let H0 := gcm_init_H_asm x_rev
    let H2 := gcm_polyval_asm H0 H0
    let H3 := gcm_polyval_asm H0 H2
    let H5 := gcm_polyval_asm H0 H3
    ((hi H5) ^^^ (lo H5)) ++ ((hi H3) ^^^ (lo H3)) := by
    simp (config := {decide := true}) only [
      h_s77_non_effects, h_s76_q24, h_s76_non_effects,
      h_s75_non_effects, h_s74_q17, h_s74_non_effects,
      h_s73_q16, h_s73_non_effects,
      h_s72_non_effects,
      extractLsb'_of_append_mid]
    have q0 : r (StateField.SFP 17#5) s71 = r (StateField.SFP 17#5) s69 := by sym_aggregate
    have q1 : r (StateField.SFP 16#5) s71 = r (StateField.SFP 16#5) s68 := by sym_aggregate
    have q2 : r (StateField.SFP 25#5) s71 = r (StateField.SFP 25#5) s77 := by sym_aggregate
    have q3 : r (StateField.SFP 23#5) s71 = r (StateField.SFP 23#5) s77 := by sym_aggregate
    simp only [q0, q1, q2, q3, h_v16_s68, h_v17_s69, h_H3, h_H5]
    simp only [lo, hi, extractLsb'_of_xor_of_extractLsb'_hi,
      extractLsb'_of_xor_of_extractLsb'_lo,
      gcm_polyval_asm_associativity]
  sym_n 1
  sorry
