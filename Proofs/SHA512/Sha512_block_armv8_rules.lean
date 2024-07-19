/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPSFP.Insts
import Specs.SHA512
import LeanSAT

set_option sat.timeout 60

section sha512_block_armv8_rules

open BitVec
open sha512_helpers
open DPSFP
open SHA2

theorem sha512_message_schedule_rule (a b c d : BitVec 128) :
  sha512su1 a b (sha512su0 c d) =
  let a1 := extractLsb 127 64 a
  let a0 := extractLsb  63  0 a
  let b1 := extractLsb 127 64 b
  let b0 := extractLsb  63  0 b
  let c0 := extractLsb  63  0 c
  let d1 := extractLsb 127 64 d
  let d0 := extractLsb  63  0 d
  message_schedule_word_aux a1 b1 c0 d1 ++
  message_schedule_word_aux a0 b0 d1 d0 := by
  simp [sha512su1, sha512su0,  message_schedule_word_aux]
  bv_decide

theorem sha512h2_rule (a b c : BitVec 128) :
  sha512h2 a b c =
  let a0 := extractLsb  63  0  a
  let b1 := extractLsb 127 64  b
  let b0 := extractLsb  63  0  b
  let c0 := extractLsb  63  0  c
  let c1 := extractLsb 127 64  c
  ((compression_update_t2 b0 a0 b1) + c1) ++
  ((compression_update_t2 ((compression_update_t2 b0 a0 b1) + c1) b0 b1) + c0) := by
  simp [maj, compression_update_t2, sha512h2, sigma_big_0, ror]
  bv_decide

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

set_option sat.timeout 350 in
theorem sha512h_rule_1 (a b c d e : BitVec 128) :
  let elements := 2
  let esize := 64
  let inner_sum := (binary_vector_op_aux 0 elements esize BitVec.add c d (BitVec.zero 128) H)
  let outer_sum := (binary_vector_op_aux 0 elements esize BitVec.add inner_sum e (BitVec.zero 128) H)
  let a0 := extractLsb 63 0   a
  let a1 := extractLsb 127 64 a
  let b0 := extractLsb 63 0   b
  let b1 := extractLsb 127 64 b
  let c0 := extractLsb 63 0   c
  let c1 := extractLsb 127 64 c
  let d0 := extractLsb 63 0   d
  let d1 := extractLsb 127 64 d
  let e0 := extractLsb 63 0   e
  let e1 := extractLsb 127 64 e
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d1 e1
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d0 e0
  sha512h a b outer_sum = hi64_spec ++ lo64_spec := by
  simp_all! only [Nat.sub_zero];
  repeat (unfold binary_vector_op_aux elem_set elem_get; simp)
  unfold BitVec.partInstall
  unfold sha512h compression_update_t1 sigma_big_1 ch allOnes ror
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_zero, Nat.reducePow, reduceZeroExtend,
    reduceHShiftLeft, reduceNot, reduceAnd, BitVec.zero_or]
  bv_decide

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rev_elems_of_rev_elems_64_8 (x : BitVec 64) :
  rev_elems 64 8 (rev_elems 64 8 x h₀ h₁) h₀ h₁ = x := by
  repeat (unfold rev_elems; (simp (config := {ground := true, decide := true})))
  simp_arith at h₀
  simp_arith at h₁
  bv_decide

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem concat_of_rsh_is_msb_128 (x y : BitVec 64) :
  (x ++ y) >>> 64 = BitVec.zeroExtend 128 x := by
  bv_decide

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem truncate_of_concat_is_lsb_64 (x y : BitVec 64) :
  BitVec.zeroExtend 64 (x ++ y) = y := by
  bv_decide

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem zeroextend_bigger_smaller_64 (x : BitVec 64) :
  BitVec.zeroExtend 64 (BitVec.zeroExtend 128 x) =
  BitVec.zeroExtend 64 x := by
  bv_decide

theorem zeroextend_id_64 (x : BitVec 64) :
  BitVec.zeroExtend 64 x = x := by
  simp only [zeroExtend_eq]

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rsh_concat_identity_128 (x : BitVec 128) :
  zeroExtend 64 (x >>> 64) ++ zeroExtend 64 x = x := by
  bv_decide

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rev_vector_of_rev_vector_128_64_8 (x : BitVec 128) :
  rev_vector 128 64 8
    (rev_vector 128 64 8 x h₀ h₁ h₂ h₃ h₄) h₀ h₁ h₂ h₃ h₄ = x := by
  repeat (unfold rev_vector; simp)
  rw [concat_of_rsh_is_msb_128,
      truncate_of_concat_is_lsb_64,
      rev_elems_of_rev_elems_64_8,
      zeroextend_bigger_smaller_64,
      zeroextend_id_64,
      rev_elems_of_rev_elems_64_8,
      rsh_concat_identity_128]
  done

set_option sat.timeout 180 in
theorem sha512h_rule_2 (a b c d e : BitVec 128) :
  let a0 := extractLsb 63 0   a
  let a1 := extractLsb 127 64 a
  let b0 := extractLsb 63 0   b
  let b1 := extractLsb 127 64 b
  let c0 := extractLsb 63 0   c
  let c1 := extractLsb 127 64 c
  let d0 := extractLsb 63 0   d
  let d1 := extractLsb 127 64 d
  let e0 := extractLsb 63 0   e
  let e1 := extractLsb 127 64 e
  let inner_sum := binary_vector_op_aux 0 2 64 BitVec.add d e (BitVec.zero 128) h1
  let concat := inner_sum ++ inner_sum
  let operand := extractLsb 191 64 concat
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d0 e0
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d1 e1
  sha512h a b (binary_vector_op_aux 0 2 64 BitVec.add c operand (BitVec.zero 128) h2) =
  hi64_spec ++ lo64_spec := by
  repeat (unfold binary_vector_op_aux; simp)
  repeat (unfold BitVec.partInstall; simp)
  unfold sha512h compression_update_t1 elem_set elem_get partInstall sigma_big_1 ch ror
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.sub_zero, reduceAllOnes,
    reduceZeroExtend, Nat.zero_mul, reduceHShiftLeft, reduceNot, reduceAnd, Nat.one_mul,
    BitVec.cast_eq]
  bv_decide

end sha512_block_armv8_rules
