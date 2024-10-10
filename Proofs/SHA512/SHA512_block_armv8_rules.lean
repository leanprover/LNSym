/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPSFP.Insts
import Specs.SHA512
import Std.Tactic.BVDecide

set_option sat.timeout 60
set_option bv.ac_nf false

section sha512_block_armv8_rules

open BitVec
open sha512_helpers
open DPSFP
open SHA2

theorem sha512_message_schedule_rule (a b c d : BitVec 128) :
  sha512su1 a b (sha512su0 c d) =
  let a1 := extractLsb' 64 64 a
  let a0 := extractLsb'  0 64 a
  let b1 := extractLsb' 64 64 b
  let b0 := extractLsb'  0 64 b
  let c0 := extractLsb'  0 64 c
  let d1 := extractLsb' 64 64 d
  let d0 := extractLsb'  0 64 d
  message_schedule_word_aux a1 b1 c0 d1 ++
  message_schedule_word_aux a0 b0 d1 d0 := by
  simp only [sha512su1, Nat.reduceAdd, sha512su0, message_schedule_word_aux]
  bv_check "SHA512_block_armv8_rules.lean-sha512_message_schedule_rule-31-2.lrat"

theorem sha512h2_rule (a b c : BitVec 128) :
  sha512h2 a b c =
  let a0 := extractLsb'  0 64 a
  let b1 := extractLsb' 64 64 b
  let b0 := extractLsb'  0 64 b
  let c0 := extractLsb'  0 64 c
  let c1 := extractLsb' 64 64 c
  ((compression_update_t2 b0 a0 b1) + c1) ++
  ((compression_update_t2 ((compression_update_t2 b0 a0 b1) + c1) b0 b1) + c0) := by
  simp only [sha512h2, Nat.reduceAdd, maj, sigma_big_0, ror, compression_update_t2]
  bv_check "SHA512_block_armv8_rules.lean-sha512h2_rule-43-2.lrat"

-- sha512h2 q3, q1, v0.2d: 0xce608423#32
-- theorem sha512h2_instruction_rewrite
--   (h_pc : read_pc s = 0#64)
--   (h_inst : fetch_inst 0#64 s = 0xce608423#32)
--   (h_q3 : q3 = read_sfp 128 3#5 s)
--   (h_q1 : q1 = read_sfp 128 1#5 s)
--   (h_q0 : q0 = read_sfp 128 0#5 s)
--   (h_s' : s' = run 1 s)
--   (h_q3': q3' = read_sfp 128 3#5 s') :
--   q3' = q3 := by
--           simp [*] at *
--           unfold stepi; simp [h_pc, h_inst]
--           unfold exec_inst
--           simp (config := { ground := true }) only [h_inst]
--           unfold exec_crypto_three_reg_sha512
--           simp (config := { ground := true })
--           simp [sha512h2_rule]

private theorem and_nop_lemma (x : BitVec 64) :
  (setWidth 128 x) &&& 0xffffffffffffffff#128 = (setWidth 128 x) := by
  bv_decide

private theorem extractLsb'_low_64_from_setWidth_128_or (x y : BitVec 64) :
  extractLsb' 0 64 ((setWidth 128 x) ||| (setWidth 128 y <<< 64)) = x := by
  bv_decide

private theorem extractLsb'_high_64_from_setWidth_128_or (x y : BitVec 64) :
  extractLsb' 64 64 ((setWidth 128 x) ||| (setWidth 128 y <<< 64)) = y := by
  bv_decide

-- This lemma takes ~5min with bv_decide and the generated LRAT
-- file is ~207MB. It turns out this this theorem is not a good candidate for
-- proof via bit-blasting. As Bruno Dutertre says:
-- "Maybe spending more time simplifying and normalizing terms before
-- bit-blasting would help here .... + is associative and commutative.
-- Proving things like this by bit-blasting + CDCL is hard (in general circuit
-- equivalence can be hard for CDCL solvers), but a normalization procedure
-- would prove it in no time."
theorem sha512h_rule_1 (a b c d e : BitVec 128) :
  let elements := 2
  let esize := 64
  let inner_sum := (binary_vector_op_aux 0 elements esize BitVec.add c d (BitVec.zero 128))
  let outer_sum := (binary_vector_op_aux 0 elements esize BitVec.add inner_sum e (BitVec.zero 128))
  let a0 := extractLsb'  0 64 a
  let a1 := extractLsb' 64 64 a
  let b0 := extractLsb'  0 64 b
  let b1 := extractLsb' 64 64 b
  let c0 := extractLsb'  0 64 c
  let c1 := extractLsb' 64 64 c
  let d0 := extractLsb'  0 64 d
  let d1 := extractLsb' 64 64 d
  let e0 := extractLsb'  0 64 e
  let e1 := extractLsb' 64 64 e
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d1 e1
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d0 e0
  sha512h a b outer_sum = hi64_spec ++ lo64_spec := by
  simp_all! only [Nat.sub_zero];
  repeat (unfold binary_vector_op_aux elem_set elem_get; simp)
  unfold BitVec.partInstall
  unfold sha512h compression_update_t1 sigma_big_1 ch allOnes ror
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_zero, Nat.reducePow, reduceSetWidth,
    reduceHShiftLeft, reduceNot, reduceAnd, BitVec.zero_or, shiftLeft_zero_eq]
  generalize extractLsb'  0 64 a = a_lo
  generalize extractLsb' 64 64 a = a_hi
  generalize extractLsb'  0 64 b = b_lo
  generalize extractLsb' 64 64 b = b_hi
  generalize extractLsb'  0 64 c = c_lo
  generalize extractLsb' 64 64 c = c_hi
  generalize extractLsb'  0 64 d = d_lo
  generalize extractLsb' 64 64 d = d_hi
  generalize extractLsb'  0 64 e = e_lo
  generalize extractLsb' 64 64 e = e_hi
  -- simp at a_lo a_hi b_lo b_hi c_lo c_hi d_lo d_hi e_lo e_hi
  clear a b c d e
  simp only [truncate_eq_setWidth, reduceSetWidth, reduceNot, zero_and, zero_or,
    reduceHShiftLeft, and_nop_lemma, extractLsb'_low_64_from_setWidth_128_or,
    extractLsb'_high_64_from_setWidth_128_or]
  -- simp only [and_nop_lemma, extractLsb'_low_64_from_setWidth_128_or, extractLsb'_high_64_from_setWidth_128_or]
  generalize (b_hi.rotateRight 14 ^^^ b_hi.rotateRight 18 ^^^ b_hi.rotateRight 41) = aux0
  generalize (b_hi &&& a_lo ^^^ ~~~b_hi &&& a_hi) = aux1
  ac_rfl

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rev_elems_of_rev_elems_64_8 (x : BitVec 64) :
  rev_elems 64 8 (rev_elems 64 8 x h₀ h₁) h₀ h₁ = x := by
  repeat (
    unfold rev_elems;
    (simp (config := { ground := true, decide := true }) only [
        ↓reduceDIte, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLeDiff,
        setWidth_setWidth_of_le, BitVec.cast_eq])
  )
  simp_arith at h₀
  simp_arith at h₁
  bv_check "SHA512_block_armv8_rules.lean-rev_elems_of_rev_elems_64_8-135-2.lrat"

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem concat_of_rsh_is_msb_128 (x y : BitVec 64) :
  (x ++ y) >>> 64 = BitVec.setWidth 128 x := by
  bv_check "SHA512_block_armv8_rules.lean-concat_of_rsh_is_msb_128-140-2.lrat"

-- TODO: upstream?
@[simp]
theorem setWidth_append_right (x : BitVec n) (y : BitVec m) :
    BitVec.setWidth m (x ++ y) = y := by
  apply eq_of_toNat_eq
  simp only [toNat_setWidth, toNat_append]
  rw [← Nat.and_pow_two_sub_one_eq_mod, Nat.and_distrib_right]
  suffices x.toNat <<< m &&& 2 ^ m - 1 = 0
    by simp [this]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.and_pow_two_sub_one_eq_mod, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    ge_iff_le, Nat.zero_testBit, Bool.and_eq_false_imp, decide_eq_true_eq]
  omega

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rsh_concat_identity_128 (x : BitVec 128) :
  setWidth 64 (x >>> 64) ++ setWidth 64 x = x := by
  bv_check "SHA512_block_armv8_rules.lean-rsh_concat_identity_128-156-2.lrat"

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rev_vector_of_rev_vector_128_64_8 (x : BitVec 128) :
  rev_vector 128 64 8
    (rev_vector 128 64 8 x h₀ h₁ h₂ h₃ h₄) h₀ h₁ h₂ h₃ h₄ = x := by
  repeat (
    unfold rev_vector;
    simp only [Nat.reduceEqDiff, ↓reduceDIte, Nat.reduceSub, Nat.reduceAdd, truncate_eq_setWidth,
      BitVec.cast_eq]
  )
  rw [concat_of_rsh_is_msb_128,
      setWidth_append_right,
      rev_elems_of_rev_elems_64_8,
      setWidth_setWidth_of_le _ (by decide),
      @setWidth_eq 64,
      rev_elems_of_rev_elems_64_8,
      rsh_concat_identity_128]
  done

private theorem sha512h_rule_2_helper_1 (x y : BitVec 64) :
  extractLsb' 0 64
          (extractLsb' 64 128
            ((setWidth 128 x ||| setWidth 128 y <<< 64) ++
              (setWidth 128 x ||| setWidth 128 y <<< 64)))
  =
  y := by
  bv_decide

private theorem sha512h_rule_2_helper_2 (x y : BitVec 64) :
  extractLsb' 64 64
          (extractLsb' 64 128
            ((setWidth 128 x ||| setWidth 128 y <<< 64) ++
              (setWidth 128 x ||| setWidth 128 y <<< 64)))
  =
  x := by
  bv_decide

theorem BitVec.extractLsb'_append (x : BitVec n) (y : BitVec m) :
    (x ++ y).extractLsb' start len
    = let len' := min len (m - start)
      (x.extractLsb' (start - m) (len - len')
        ++ y.extractLsb' start len'
        ).cast (by omega) := by
  apply eq_of_getLsbD_eq
  intro i
  simp [getLsbD_append]
  by_cases h₁ : m - start ≥ len
  · have len'_eq : min len (m - start) = len := Nat.min_eq_left h₁
    have : start + i.val < m := by omega
    simp [len'_eq, this]
  · have len'_eq : min len (m - start) = m - start :=
      Nat.min_eq_right (by omega)
    simp only [len'_eq]
    by_cases h₂ : start + i.val < m
    · have h₃ : ↑i < m - start := by omega
      simp [h₂, h₃]
    · have h₃ : ¬(↑i < m - start) := by omega
      have h₄ : ↑i - (m - start) < len - (m - start) := by omega
      have h₅ : start - m + (↑i - (m - start)) = start + ↑i - m := by omega
      simp [h₂, h₃, h₄, h₅]

theorem BitVec.cast_eq_of_heq (x : BitVec n) (y : BitVec m) (h : n = m) :
    HEq x y → x.cast h = y := by
  cases h; simp

@[simp]
theorem BitVec.cast_heq_iff (x : BitVec n) (y : BitVec m) (h : n = n') :
    HEq (x.cast h) y ↔ HEq x y := by
  cases h; simp

theorem BitVec.extractLsb'_append_right (x : BitVec n) (y : BitVec m)
    (h : start + len ≤ m) :
    (x ++ y).extractLsb' start len = y.extractLsb' start len := by
  have len'_eq : min len (m - start) = len := Nat.min_eq_left (by omega)
  simp only [extractLsb'_append]
  apply cast_eq_of_heq
  rw [len'_eq, Nat.sub_self]
  simp only [zero_width_append, heq_eq_eq, cast_heq_iff]

@[simp]
theorem BitVec.extractLsb'_extractLsb'_of_le {w : Nat} (start₁ len₁ start₂ len₂)
    (h : start₂ + len₂ ≤ len₁)
    (x : BitVec w) :
    (x.extractLsb' start₁ len₁).extractLsb' start₂ len₂
    = x.extractLsb' (start₁ + start₂) len₂ := by
  apply eq_of_getLsbD_eq
  intro i
  simp only [getLsbD_extractLsb', Fin.is_lt, decide_True, Bool.true_and,
    Bool.and_iff_right_iff_imp, decide_eq_true_eq,
    show start₁ + (start₂ + i.val) = start₁ + start₂ + i.val by ac_rfl]
  omega

  -- apply eq_of_toNat_eq
  -- simp only [extractLsb', toNat_ofNat, setWidth, setWidth']


-- This lemma takes 2min with bv_decide and the generated LRAT
-- file is ~120MB. As with sha512h_rule_1 above, we prefer to just simplify and
-- normalize here instead of doing bit-blasting.
theorem sha512h_rule_2 (a b c d e : BitVec 128) :
  let a0 := extractLsb'  0 64 a
  let a1 := extractLsb' 64 64 a
  let b0 := extractLsb'  0 64 b
  let b1 := extractLsb' 64 64 b
  let c0 := extractLsb'  0 64 c
  let c1 := extractLsb' 64 64 c
  let d0 := extractLsb'  0 64 d
  let d1 := extractLsb' 64 64 d
  let e0 := extractLsb'  0 64 e
  let e1 := extractLsb' 64 64 e
  let inner_sum := binary_vector_op_aux 0 2 64 BitVec.add d e (BitVec.zero 128)
  let concat := inner_sum ++ inner_sum
  let operand := extractLsb' 64 128 concat
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d0 e0
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d1 e1
  sha512h a b (binary_vector_op_aux 0 2 64 BitVec.add c operand (BitVec.zero 128)) =
  hi64_spec ++ lo64_spec := by
  repeat (
    unfold binary_vector_op_aux;
    simp only [Nat.reduceLeDiff, ↓reduceDIte, Nat.reduceAdd, add_eq, zero_eq]
  )
  unfold sha512h compression_update_t1 elem_set elem_get partInstall sigma_big_1 ch ror
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.sub_zero, reduceAllOnes,
    reduceSetWidth, Nat.zero_mul, reduceHShiftLeft, reduceNot, reduceAnd, Nat.one_mul,
    BitVec.cast_eq]
  simp only [shiftLeft_zero_eq, BitVec.zero_or, and_nop_lemma]
  generalize extractLsb'  0 64 a = a_lo
  generalize extractLsb' 64 64 a = a_hi
  generalize extractLsb'  0 64 b = b_lo
  generalize extractLsb' 64 64 b = b_hi
  generalize extractLsb'  0 64 c = c_lo
  generalize extractLsb' 64 64 c = c_hi
  generalize extractLsb'  0 64 d = d_lo
  generalize extractLsb' 64 64 d = d_hi
  generalize extractLsb'  0 64 e = e_lo
  generalize extractLsb' 64 64 e = e_hi
  clear a b c d e
  simp only [truncate_eq_setWidth, reduceSetWidth, reduceNot, zero_and, zero_or,
    reduceHShiftLeft]

  simp only [
    show 18446744073709551615#128 = (18446744073709551615#64).setWidth 128 by rfl,
    ← BitVec.setWidth_and]
  simp only [extractLsb'_high_64_from_setWidth_128_or, extractLsb'_low_64_from_setWidth_128_or]
  simp only [sha512h_rule_2_helper_1, sha512h_rule_2_helper_2]
  generalize (b_hi.rotateRight 14 ^^^ b_hi.rotateRight 18 ^^^ b_hi.rotateRight 41) = aux1
  ac_rfl

end sha512_block_armv8_rules
