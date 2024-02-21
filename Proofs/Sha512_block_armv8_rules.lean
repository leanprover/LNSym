/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPSFP.Insts
import Specs.SHA512
-- import Auto

section sha512_block_armv8_rules

open Std.BitVec
open sha512_helpers
open DPSFP
open SHA2

-- set_option auto.smt true
-- set_option auto.smt.trust true
-- set_option auto.smt.timeout 20 -- seconds
-- set_option auto.smt.save true
-- -- set_option trace.auto.smt.printCommands true
-- set_option trace.auto.smt.result true -- Print the SMT solver's output
-- set_option trace.auto.smt.model true  -- Print the counterexample, if any
-- set_option trace.auto.smt.proof false -- Do not print the proof.

-- set_option auto.smt.savepath "/tmp/sha512_message_schedule_rule.smt2" in
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
  sorry -- auto d[sha512su1, sha512su0,  message_schedule_word_aux]

-- set_option auto.smt.savepath "/tmp/sha512h2_rule.smt2" in
theorem sha512h2_rule (a b c : BitVec 128) :
  sha512h2 a b c =
  let a0 := extractLsb  63  0  a
  let b1 := extractLsb 127 64  b
  let b0 := extractLsb  63  0  b
  let c0 := extractLsb  63  0  c
  let c1 := extractLsb 127 64  c
  ((compression_update_t2 b0 a0 b1) + c1) ++
  ((compression_update_t2 ((compression_update_t2 b0 a0 b1) + c1) b0 b1) + c0) := by
  sorry -- auto u[maj, compression_update_t2, sha512h2]

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

-- set_option auto.smt.savepath "/tmp/sha512h_rule_1.smt2" in
theorem sha512h_rule_1 (a b c d e : BitVec 128) :
  let elements := 2
  let esize := 64
  let inner_sum := (binary_vector_op_aux 0 elements esize Std.BitVec.add c d (Std.BitVec.zero 128) H)
  let outer_sum := (binary_vector_op_aux 0 elements esize Std.BitVec.add inner_sum e (Std.BitVec.zero 128) H)
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
  sorry
/-
  simp_all! only [Nat.sub_zero];
  repeat (unfold binary_vector_op_aux; simp)
  unfold BitVec.partInstall
  unfold sha512h compression_update_t1 sigma_big_1 ch allOnes
  auto
-/

-- (FIXME) Prove without auto.
-- set_option auto.smt.savepath "/tmp/rev_elems_of_rev_elems_64_8.smt2" in
theorem rev_elems_of_rev_elems_64_8 (x : Std.BitVec 64) :
  rev_elems 64 8 (rev_elems 64 8 x h₀ h₁) h₀ h₁ = x := by
  repeat (unfold rev_elems; (simp (config := {ground := true, decide := true})))
  simp_arith at h₀
  simp_arith at h₁
  sorry -- auto

-- (FIXME) Prove without auto.
-- set_option auto.smt.savepath "/tmp/concat_of_rsh_is_msb_128.smt2" in
theorem concat_of_rsh_is_msb_128 (x y : Std.BitVec 64) :
  (x ++ y) >>> 64 = Std.BitVec.zeroExtend 128 x := by
  sorry -- auto

-- (FIXME) Prove without auto.
-- set_option auto.smt.savepath "/tmp/truncate_of_concat_is_lsb_64.smt2" in
theorem truncate_of_concat_is_lsb_64 (x y : Std.BitVec 64) :
  Std.BitVec.zeroExtend 64 (x ++ y) = y := by
  sorry -- auto

-- (FIXME) Prove without auto.
-- set_option auto.smt.savepath "/tmp/zeroextend_bigger_smaller_64.smt2" in
theorem zeroextend_bigger_smaller_64 (x : Std.BitVec 64) :
  Std.BitVec.zeroExtend 64 (Std.BitVec.zeroExtend 128 x) =
  Std.BitVec.zeroExtend 64 x := by
  sorry -- auto

theorem zeroextend_id_64 (x : Std.BitVec 64) :
  Std.BitVec.zeroExtend 64 x = x := by
  simp

-- (FIXME) Prove without auto.
-- set_option auto.smt.savepath "/tmp/rsh_concat_identity_128.smt2" in
theorem rsh_concat_identity_128 (x : Std.BitVec 128) :
  zeroExtend 64 (x >>> 64) ++ zeroExtend 64 x = x := by
  sorry

-- (FIXME) Prove without auto.
theorem rev_vector_of_rev_vector_128_64_8 (x : Std.BitVec 128) :
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

-- set_option auto.smt.savepath "/tmp/sha512h_rule_2.smt2" in
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
  let inner_sum := binary_vector_op_aux 0 2 64 Std.BitVec.add d e (Std.BitVec.zero 128) h1
  let concat := inner_sum ++ inner_sum
  let operand := extractLsb 191 64 concat
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d0 e0
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d1 e1
  sha512h a b (binary_vector_op_aux 0 2 64 Std.BitVec.add c operand (Std.BitVec.zero 128) h2) =
  hi64_spec ++ lo64_spec := by
  repeat (unfold binary_vector_op_aux; simp)
  repeat (unfold BitVec.partInstall; simp)
  unfold sha512h compression_update_t1 sigma_big_1 ch
  sorry -- auto

end sha512_block_armv8_rules
