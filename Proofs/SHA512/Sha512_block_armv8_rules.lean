/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPSFP.Insts
import Specs.SHA512
import LeanSAT
import Tactics.CSE
import Tactics.Attr

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
  bv_check "lrat_files/Sha512_block_armv8_rules.lean-sha512_message_schedule_rule-31-2.lrat"

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
  bv_check "lrat_files/Sha512_block_armv8_rules.lean-sha512h2_rule-43-2.lrat"

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
  (zeroExtend 128 x) &&& 0xffffffffffffffff#128 = (zeroExtend 128 x) := by
  bv_decide

private theorem extractLsb_low_64_from_zeroExtend_128_or (x y : BitVec 64) :
  extractLsb 63 0 ((zeroExtend 128 x) ||| (zeroExtend 128 y <<< 64)) = x := by
  bv_decide

private theorem extractLsb_high_64_from_zeroExtend_128_or (x y : BitVec 64) :
  extractLsb 127 64 ((zeroExtend 128 x) ||| (zeroExtend 128 y <<< 64)) = y := by
  bv_decide

-- This lemma takes ~5min with bv_decide and the generated LRAT
-- file is ~207MB. It turns out this this theorem is not a good candidate for
-- proof via bit-blasting. As Bruno Dutertre says:
-- "Maybe spending more time simplifying and normalizing terms before
-- bit-blasting would help here .... + is associative and commutative.
-- Proving things like this by bit-blasting + CDCL is hard (in general circuit
-- equivalence can be hard for CDCL solvers), but a normalization procedure
-- would prove it in no time."
set_option trace.Tactic.cse.summary true in
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
    reduceHShiftLeft, reduceNot, reduceAnd, BitVec.zero_or, shiftLeft_zero_eq]
  cse (config := {minRefsToCSE := 2})
  /-
  H : 64 > 0
a b c d e : BitVec 128
x1 : BitVec 64
hx1 : extractLsb 63 0 b +
    (extractLsb 127 64 c +
            ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
              (extractLsb 127 64 b).rotateRight 41) +
          (extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a) +
        extractLsb 127 64 d +
      extractLsb 127 64 e) =
  x1
x2 : BitVec 64
hx2 : extractLsb 127 64 c +
          ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
            (extractLsb 127 64 b).rotateRight 41) +
        (extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a) +
      extractLsb 127 64 d +
    extractLsb 127 64 e =
  x2
x3 : BitVec 64
hx3 : extractLsb 127 64 c +
        ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
          (extractLsb 127 64 b).rotateRight 41) +
      (extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a) +
    extractLsb 127 64 d =
  x3
x4 : BitVec 64
hx4 : extractLsb 127 64 c +
      ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
        (extractLsb 127 64 b).rotateRight 41) +
    (extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a) =
  x4
x5 : BitVec 64
hx5 : extractLsb 127 64 c +
    ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
      (extractLsb 127 64 b).rotateRight 41) =
  x5
x6 : BitVec 64
hx6 : (extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a) +
        ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
          (extractLsb 127 64 b).rotateRight 41) +
      extractLsb 127 64
        (zeroExtend 128
              (extractLsb 63 0
                  (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
                    zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
                extractLsb 63 0 e) &&&
            18446744073709551615#128 |||
          zeroExtend 128
              (extractLsb 127 64
                  (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
                    zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
                extractLsb 127 64 e) <<<
            64) +
    extractLsb 63 0 b =
  x6
x7 : BitVec (63 - 0 + 1)
hx7 : extractLsb 63 0 b = x7
x8 : BitVec 64
hx8 : (extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a) +
      ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
        (extractLsb 127 64 b).rotateRight 41) +
    extractLsb 127 64
      (zeroExtend 128
            (extractLsb 63 0
                (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
                  zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
              extractLsb 63 0 e) &&&
          18446744073709551615#128 |||
        zeroExtend 128
            (extractLsb 127 64
                (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
                  zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
              extractLsb 127 64 e) <<<
          64) =
  x8
x9 : BitVec (127 - 64 + 1)
hx9 : extractLsb 127 64
    (zeroExtend 128
          (extractLsb 63 0
              (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
                zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
            extractLsb 63 0 e) &&&
        18446744073709551615#128 |||
      zeroExtend 128
          (extractLsb 127 64
              (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
                zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
            extractLsb 127 64 e) <<<
        64) =
  x9
x10 : BitVec 128
hx10 : zeroExtend 128
        (extractLsb 63 0
            (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
              zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
          extractLsb 63 0 e) &&&
      18446744073709551615#128 |||
    zeroExtend 128
        (extractLsb 127 64
            (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
              zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
          extractLsb 127 64 e) <<<
      64 =
  x10
x11 : BitVec 128
hx11 : zeroExtend 128
      (extractLsb 127 64
          (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
            zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
        extractLsb 127 64 e) <<<
    64 =
  x11
x12 : BitVec 128
hx12 : zeroExtend 128
    (extractLsb 127 64
        (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
          zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
      extractLsb 127 64 e) =
  x12
x13 : BitVec 64
hx13 : extractLsb 127 64
      (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
        zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
    extractLsb 127 64 e =
  x13
x14 : BitVec (127 - 64 + 1)
hx14 : extractLsb 127 64 e = x14
x15 : BitVec (127 - 64 + 1)
hx15 : extractLsb 127 64
    (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
      zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) =
  x15
x16 : BitVec 128
hx16 : zeroExtend 128
      (extractLsb 63 0
          (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
            zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
        extractLsb 63 0 e) &&&
    18446744073709551615#128 =
  x16
x17 : BitVec 128
hx17 : zeroExtend 128
    (extractLsb 63 0
        (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
          zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
      extractLsb 63 0 e) =
  x17
x18 : BitVec 64
hx18 : extractLsb 63 0
      (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
        zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) +
    extractLsb 63 0 e =
  x18
x19 : BitVec (63 - 0 + 1)
hx19 : extractLsb 63 0 e = x19
x20 : BitVec (63 - 0 + 1)
hx20 : extractLsb 63 0
    (zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
      zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64) =
  x20
x21 : BitVec 128
hx21 : zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 |||
    zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64 =
  x21
x22 : BitVec 128
hx22 : zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) <<< 64 = x22
x23 : BitVec 128
hx23 : zeroExtend 128 (extractLsb 127 64 c + extractLsb 127 64 d) = x23
x24 : BitVec 64
hx24 : extractLsb 127 64 c + extractLsb 127 64 d = x24
x25 : BitVec (127 - 64 + 1)
hx25 : extractLsb 127 64 d = x25
x26 : BitVec (127 - 64 + 1)
hx26 : extractLsb 127 64 c = x26
x27 : BitVec 128
hx27 : zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) &&& 18446744073709551615#128 = x27
x28 : BitVec 128
hx28 : 18446744073709551615#128 = x28
x29 : BitVec 128
hx29 : zeroExtend 128 (extractLsb 63 0 c + extractLsb 63 0 d) = x29
x30 : BitVec 64
hx30 : extractLsb 63 0 c + extractLsb 63 0 d = x30
x31 : BitVec (63 - 0 + 1)
hx31 : extractLsb 63 0 d = x31
x32 : BitVec (63 - 0 + 1)
hx32 : extractLsb 63 0 c = x32
x33 : BitVec 64
hx33 : (extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a) +
    ((extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^
      (extractLsb 127 64 b).rotateRight 41) =
  x33
x34 : BitVec 64
hx34 : (extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 ^^^ (extractLsb 127 64 b).rotateRight 41 =
  x34
x35 : BitVec 64
hx35 : (extractLsb 127 64 b).rotateRight 41 = x35
x36 : BitVec 64
hx36 : (extractLsb 127 64 b).rotateRight 14 ^^^ (extractLsb 127 64 b).rotateRight 18 = x36
x37 : BitVec 64
hx37 : (extractLsb 127 64 b).rotateRight 18 = x37
x38 : BitVec 64
hx38 : (extractLsb 127 64 b).rotateRight 14 = x38
x39 : BitVec 64
hx39 : extractLsb 127 64 b &&& extractLsb 63 0 a ^^^ ~~~extractLsb 127 64 b &&& extractLsb 127 64 a = x39
x40 : BitVec 64
hx40 : ~~~extractLsb 127 64 b &&& extractLsb 127 64 a = x40
x41 : BitVec (127 - 64 + 1)
hx41 : extractLsb 127 64 a = x41
x42 : BitVec 64
hx42 : ~~~extractLsb 127 64 b = x42
x43 : BitVec 64
hx43 : extractLsb 127 64 b &&& extractLsb 63 0 a = x43
x44 : BitVec (63 - 0 + 1)
hx44 : extractLsb 63 0 a = x44
x45 : BitVec (127 - 64 + 1)
hx45 : extractLsb 127 64 b = x45
⊢ x8 ++
    ((x6 &&& x45 ^^^ ~~~x6 &&& x44) + (x6.rotateRight 14 ^^^ x6.rotateRight 18 ^^^ x6.rotateRight 41) +
      extractLsb 63 0 x10) =
  x2 ++
    (x32 + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) + (x1 &&& x45 ^^^ ~~~x1 &&& x44) + x31 + x19)
  -/
  generalize extractLsb 63   0 a = a_lo
  generalize extractLsb 127 64 a = a_hi
  generalize extractLsb 63   0 b = b_lo
  generalize extractLsb 127 64 b = b_hi
  generalize extractLsb 63   0 c = c_lo
  generalize extractLsb 127 64 c = c_hi
  generalize extractLsb 63   0 d = d_lo
  generalize extractLsb 127 64 d = d_hi
  generalize extractLsb 63   0 e = e_lo
  generalize extractLsb 127 64 e = e_hi
  simp at a_lo a_hi b_lo b_hi c_lo c_hi d_lo d_hi e_lo e_hi
  clear a b c d e
  simp only [and_nop_lemma, extractLsb_low_64_from_zeroExtend_128_or, extractLsb_high_64_from_zeroExtend_128_or]
  generalize (b_hi.rotateRight 14 ^^^ b_hi.rotateRight 18 ^^^ b_hi.rotateRight 41) = aux0
  generalize (b_hi &&& a_lo ^^^ ~~~b_hi &&& a_hi) = aux1
  ac_rfl

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rev_elems_of_rev_elems_64_8 (x : BitVec 64) :
  rev_elems 64 8 (rev_elems 64 8 x h₀ h₁) h₀ h₁ = x := by
  repeat (unfold rev_elems; (simp (config := {ground := true, decide := true})))
  simp_arith at h₀
  simp_arith at h₁
  bv_check "lrat_files/Sha512_block_armv8_rules.lean-rev_elems_of_rev_elems_64_8-96-2.lrat"

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem concat_of_rsh_is_msb_128 (x y : BitVec 64) :
  (x ++ y) >>> 64 = BitVec.zeroExtend 128 x := by
  bv_check "lrat_files/Sha512_block_armv8_rules.lean-concat_of_rsh_is_msb_128-101-2.lrat"

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem truncate_of_concat_is_lsb_64 (x y : BitVec 64) :
  BitVec.zeroExtend 64 (x ++ y) = y := by
  bv_check "lrat_files/Sha512_block_armv8_rules.lean-truncate_of_concat_is_lsb_64-106-2.lrat"

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem zeroextend_bigger_smaller_64 (x : BitVec 64) :
  BitVec.zeroExtend 64 (BitVec.zeroExtend 128 x) =
  BitVec.zeroExtend 64 x := by
  bv_omega

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rsh_concat_identity_128 (x : BitVec 128) :
  zeroExtend 64 (x >>> 64) ++ zeroExtend 64 x = x := by
  bv_check "lrat_files/Sha512_block_armv8_rules.lean-rsh_concat_identity_128-117-2.lrat"

-- (FIXME) Generalize to arbitrary-length bitvecs.
theorem rev_vector_of_rev_vector_128_64_8 (x : BitVec 128) :
  rev_vector 128 64 8
    (rev_vector 128 64 8 x h₀ h₁ h₂ h₃ h₄) h₀ h₁ h₂ h₃ h₄ = x := by
  repeat (unfold rev_vector; simp)
  rw [concat_of_rsh_is_msb_128,
      truncate_of_concat_is_lsb_64,
      rev_elems_of_rev_elems_64_8,
      zeroextend_bigger_smaller_64,
      @zeroExtend_eq 64,
      rev_elems_of_rev_elems_64_8,
      rsh_concat_identity_128]
  done

private theorem sha512h_rule_2_helper_1 (x y : BitVec 64) :
  extractLsb 63 0
          (extractLsb 191 64
            ((zeroExtend 128 x ||| zeroExtend 128 y <<< 64) ++
              (zeroExtend 128 x ||| zeroExtend 128 y <<< 64)))
  =
  y := by
  bv_decide

private theorem sha512h_rule_2_helper_2 (x y : BitVec 64) :
  extractLsb 127 64
          (extractLsb 191 64
            ((zeroExtend 128 x ||| zeroExtend 128 y <<< 64) ++
              (zeroExtend 128 x ||| zeroExtend 128 y <<< 64)))
  =
  x := by
  bv_decide

-- This lemma takes 2min with bv_decide and the generated LRAT
-- file is ~120MB. As with sha512h_rule_1 above, we prefer to just simplify and
-- normalize here instead of doing bit-blasting.
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
  simp only [shiftLeft_zero_eq, BitVec.zero_or, and_nop_lemma]
  generalize extractLsb 63   0 a = a_lo
  generalize extractLsb 127 64 a = a_hi
  generalize extractLsb 63   0 b = b_lo
  generalize extractLsb 127 64 b = b_hi
  generalize extractLsb 63   0 c = c_lo
  generalize extractLsb 127 64 c = c_hi
  generalize extractLsb 63   0 d = d_lo
  generalize extractLsb 127 64 d = d_hi
  generalize extractLsb 63   0 e = e_lo
  generalize extractLsb 127 64 e = e_hi
  simp at a_lo a_hi b_lo b_hi c_lo c_hi d_lo d_hi e_lo e_hi
  clear a b c d e
  simp only [extractLsb_high_64_from_zeroExtend_128_or, extractLsb_low_64_from_zeroExtend_128_or]
  simp only [sha512h_rule_2_helper_1, sha512h_rule_2_helper_2]
  generalize (b_hi.rotateRight 14 ^^^ b_hi.rotateRight 18 ^^^ b_hi.rotateRight 41) = aux1
  ac_rfl

end sha512_block_armv8_rules
