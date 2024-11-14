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

#eval gcm_init_H_asm 0x66e94bd4ef8a2c3b884cfa59ca342b2e#128

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

-- -- (TODO) Should we simply replace one function by the other here?
-- theorem gcm_polyval_mul_eq_polynomial_mult (x y : BitVec 128) :
--   GCMV8.gcm_polyval_mul x y = DPSFP.polynomial_mult x y := by
--   sorry

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
  let v23 := (hi v16) ++ (lo v16)
  v23

#eval gcm_polyval_asm 0xcdd297a9df1458771099f4b39468565c#128 0x88d320376963120dea0b3a488cb9209b#128

-- TODO: RME look into https://github.com/GaloisInc/saw-script/tree/master/rme
-- https://github.com/GaloisInc/aws-lc-verification/blob/0efc892de9a4d2660067ab02fdcef5993ff5184a/SAW/proof/AES/goal-rewrites.saw#L200-L214
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem gcm_polyval_asm_gcm_polyval_equiv (x : BitVec 128) (y : BitVec 128) :
  GCMV8.gcm_polyval x y = gcm_polyval_asm x y := by
  simp only [GCMV8.gcm_polyval, gcm_polyval_asm]
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

theorem extractLsb'_of_append_hi (x y : BitVec 64) :
  BitVec.extractLsb' 64 64 (x ++ y) = x := by
  bv_decide

theorem extractLsb'_of_append_lo (x y : BitVec 64) :
  BitVec.extractLsb' 0 64 (x ++ y) = y := by
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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
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
    -- ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
    --   read_sfp 128 20#5 sf =
    --   (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 0
    ∧ let Hinit := (read_mem_bytes 16 (H_addr s0) s0)
      read_sfp 128 21#5 sf =
      (GCMV8.GCMInitV8 ((BitVec.extractLsb' 0 64 Hinit) ++ (BitVec.extractLsb' 64 64 Hinit))).get! 1
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
  · simp only
    [shift_left_common_aux_64_2
    , shift_right_common_aux_64_2_tff
    , shift_right_common_aux_32_4_fff
    , DPSFP.AdvSIMDExpandImm
    , DPSFP.dup_aux_0_4_32
    , BitVec.partInstall]
    generalize Memory.read_bytes 16 (r (StateField.GPR 1#5) s0) s0.mem = Hinit
    -- change the type of Hinit to be BitVec 128, assuming that's def-eq
    change BitVec 128 at Hinit
    -- simplifying LHS
    simp only [extractLsb'_of_append_mid, extractLsb'_of_append_hi, extractLsb'_of_append_lo,
      extractLsb'_append4_1, extractLsb'_append4_2, extractLsb'_append4_3, extractLsb'_append4_4,
      setWidth_extractLsb'_equiv_64_128, extractLsb'_of_xor_of_append]
    simp (config := {ground := true}) only
    simp only [pmull_op_e_0_eize_64_elements_1_size_128_eq]
    -- generalize hi and lo of Hinit
    generalize h_Hinit_lo : BitVec.extractLsb' 0 64 Hinit = Hinit_lo
    generalize h_Hinit_hi : BitVec.extractLsb' 64 64 Hinit = Hinit_hi
    -- simplifying RHS
    simp only [GCMV8.GCMInitV8, GCMV8.lo, List.get!, GCMV8.hi]
    simp only [gcm_polyval_asm_gcm_polyval_equiv, gcm_init_H_asm_gcm_int_H_equiv]
    simp only [gcm_polyval_asm, gcm_init_H_asm, hi, lo, BitVec.partInstall]
    simp only [Nat.reduceAdd, BitVec.ushiftRight_eq, BitVec.shiftLeft_zero_eq,
      BitVec.reduceExtracLsb', BitVec.shiftLeft_eq, BitVec.zero_shiftLeft, BitVec.reduceHShiftLeft,
      BitVec.reduceAppend, BitVec.reduceHShiftRight, BitVec.reduceAllOnes,
      BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth, BitVec.reduceNot]
    simp only [append_of_extractLsb'_of_append, extractLsb'_of_append_hi, extractLsb'_of_append_lo]
    -- TODO: a lot of the lemmas here are for reducing the arguments on DPSFP.polynomial_mul to be the same
    -- It should be unnecessary after theory of uninterpreted functions are built into bv_decide
    bv_decide
