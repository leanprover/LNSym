/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPSFP.Insts
import Specs.SHA512
import Std.Tactic.BVDecide

set_option sat.timeout 60
-- See https://github.com/leanprover/lean4/issues/5664
-- for context on why `ac_nf` is off for these proofs.
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
  bv_check "lrat_files/SHA512_block_armv8_rules.lean-sha512_message_schedule_rule-31-2.lrat"

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
  bv_check "lrat_files/SHA512_block_armv8_rules.lean-sha512h2_rule-43-2.lrat"


private theorem and_nop_lemma (x : BitVec 64) :
  (setWidth 128 x) &&& 0xffffffffffffffff#128 = (setWidth 128 x) := by
  bv_decide

private theorem extractLsb'_low_64_from_setWidth_128_or (x y : BitVec 64) :
  extractLsb' 0 64 ((setWidth 128 x) ||| (setWidth 128 y <<< 64)) = x := by
  bv_decide

private theorem extractLsb'_high_64_from_setWidth_128_or (x y : BitVec 64) :
  extractLsb' 64 64 ((setWidth 128 x) ||| (setWidth 128 y <<< 64)) = y := by
  bv_decide

theorem sha512h_rule (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 : BitVec 64) :
  (DPSFP.sha512h (a1 ++ a0) (b1 ++ b0) (c1 + (d1 + e1) ++ (c0 + (d0 + e0)))) =
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d1 e1
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d0 e0
  hi64_spec ++ lo64_spec
  := by
  simp [DPSFP.sha512h, compression_update_t1]
  repeat rw [extractLsb'_append_left, extractLsb'_append_right]
  ac_rfl
  done

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
  let inner_sum := (binary_vector_op_aux 0 elements esize BitVec.add c d 0#128)
  let outer_sum := (binary_vector_op_aux 0 elements esize BitVec.add inner_sum e 0#128)
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

theorem binary_vector_op_aux_add_128_simp (x y result : BitVec 128) :
  DPSFP.binary_vector_op_aux 0 2 64 BitVec.add x y result =
  (BitVec.extractLsb' 64 64 x + BitVec.extractLsb' 64 64 y) ++
  (BitVec.extractLsb' 0 64 x + BitVec.extractLsb' 0 64 y) := by
  repeat simp [DPSFP.binary_vector_op_aux, state_simp_rules, bitvec_rules, partInstall]
  bv_decide
  done

theorem sha512h_and_sha512h2_rule :
  let x0 := extractLsb'  0 64 x
  let y0 := extractLsb'  0 64 y
  let y1 := extractLsb' 64 64 y
  let hi64_spec_1 := compression_update_t1 b1 a0 a1 c1 d1 e1
  let hi64_spec_2 := compression_update_t2 y0 x0 y1
  let lo64_spec_1 := compression_update_t1 (b0 + hi64_spec_1) b1 a0 c0 d0 e0
  let lo64_spec_2 := compression_update_t2 (hi64_spec_2 + hi64_spec_1) y0 y1
  (DPSFP.sha512h2 x y
      (DPSFP.sha512h (a1 ++ a0) (b1 ++ b0)
                     (c1 + (d1 + e1) ++ (c0 + (d0 + e0))))) =
  (hi64_spec_1 + hi64_spec_2) ++ (lo64_spec_1 + lo64_spec_2) := by
  simp [sha512h2_rule, sha512h]
  generalize extractLsb'  0 64 x = x0
  -- generalize extractLsb' 64 64 x = x1
  generalize extractLsb'  0 64 y = y0
  generalize extractLsb' 64 64 y = y1
  repeat rw [BitVec.extractLsb'_append_left, BitVec.extractLsb'_append_right]
  simp [compression_update_t1]
  generalize compression_update_t2 y0 x0 y1 = p0
  generalize ch b1 a0 a1 = p1
  generalize sigma_big_1 b1 = p2
  ac_rfl
  done

/-
theorem sha512h_and_sha512h2_rule_1 :
  let elements := 2
  let esize := 64
  let inner_sum := (binary_vector_op_aux 0 elements esize BitVec.add c d 0#128)
  let outer_sum := (binary_vector_op_aux 0 elements esize BitVec.add inner_sum e 0#128)
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
  let x0 := extractLsb'  0 64 x
  let y0 := extractLsb'  0 64 y
  let y1 := extractLsb' 64 64 y
  let hi64_spec_1 := compression_update_t1 b1 a0 a1 c1 d1 e1
  let hi64_spec_2 := compression_update_t2 y0 x0 y1
  let lo64_spec_1 := compression_update_t1 (b0 + hi64_spec_1) b1 a0 c0 d0 e0
  let lo64_spec_2 := compression_update_t2 (hi64_spec_2 + hi64_spec_1) y0 y1
  DPSFP.sha512h2 x y (DPSFP.sha512h a b outer_sum) =
  (hi64_spec_1 + hi64_spec_2) ++ (lo64_spec_1 + lo64_spec_2) := by
  simp [sha512h2_rule, sha512h_rule_1]
  generalize extractLsb'  0 64 a = a0
  generalize extractLsb' 64 64 a = a1
  generalize extractLsb'  0 64 b = b0
  generalize extractLsb' 64 64 b = b1i
  generalize extractLsb'  0 64 c = c0
  generalize extractLsb' 64 64 c = c1
  generalize extractLsb'  0 64 d = d0
  generalize extractLsb' 64 64 d = d1
  generalize extractLsb'  0 64 e = e0
  generalize extractLsb' 64 64 e = e1
  generalize extractLsb'  0 64 x = x0
  -- generalize extractLsb' 64 64 x = x1
  generalize extractLsb'  0 64 y = y0
  generalize extractLsb' 64 64 y = y1
  rw [BitVec.extractLsb'_append_left, BitVec.extractLsb'_append_right]
  ac_rfl
-/

-- set_option maxHeartbeats 0 in
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
    let inner_sum := binary_vector_op_aux 0 2 64 BitVec.add d e 0#128
    let concat := inner_sum ++ inner_sum
    let operand := extractLsb' 64 128 concat
    let hi64_spec := compression_update_t1 b1 a0 a1 c1 d0 e0
    let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d1 e1
    sha512h a b (binary_vector_op_aux 0 2 64 BitVec.add c operand 0#128)
    = hi64_spec ++ lo64_spec := by
  simp only
  repeat (
    repeat rw [binary_vector_op_aux_of_lt (by omega)]
    rw [binary_vector_op_aux_of_not_lt (by omega)]
  )
  simp only [zero_eq, Nat.reduceAdd, add_eq, Nat.zero_add]
  simp only [elem_set, Nat.one_mul, elem_get, Nat.zero_mul, Nat.reduceAdd,
    Nat.le_refl, BitVec.extractLsb'_extractLsb'_of_le, Nat.zero_add, Nat.reduceLeDiff,
    Nat.add_zero]
  rw [BitVec.extractLsb'_append_left_of_le (by omega), Nat.sub_self,
    partInstall_partInstall, partInstall_partInstall]
  simp only [Nat.reduceAdd, BitVec.cast_eq, partInstall_eq]

  simp only [sha512h, compression_update_t1, elem_set, elem_get, partInstall, sigma_big_1, ch, ror]
  simp only [Nat.reduceAdd, Nat.zero_add, zero_eq, reduceAllOnes, truncate_eq_setWidth,
    reduceSetWidth, Nat.zero_mul, shiftLeft_zero_eq, reduceNot, zero_and, Nat.reduceLeDiff,
    BitVec.extractLsb'_extractLsb'_of_le, Nat.add_zero, add_eq, zero_or, Nat.one_mul, reduceHShiftLeft,
    Nat.le_refl]

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
  generalize (b_hi.rotateRight 14 ^^^ b_hi.rotateRight 18 ^^^ b_hi.rotateRight 41) = aux1
  clear a b c d e

  rw [BitVec.extractLsb'_append_left]
  rw [BitVec.extractLsb'_append_right]
  rw [BitVec.extractLsb'_append_right]
  rw [BitVec.extractLsb'_append_right_of_le (by omega)]
  rw [BitVec.extractLsb'_append_left]

  ac_rfl

end sha512_block_armv8_rules
