/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.SHA512.SHA512_block_armv8_rules

/-!
# SHA512 rounds as computed by `sha512_block_armv8`

The word-level facts behind the `vcgen` proof of SHA512 (`SHA512Groups.lean`,
`SHA512VCGen.lean`):

- `two_rounds`: the hash instructions of one group of the loop body (`add`,
  three `ext`, `add`, `sha512h`, `add`, `sha512h2` on the registers holding the
  working state) compute two rounds of the specification's `compression_update`.
- `sched_step`: a group's `sha512su0`/`sha512su1` compute the next two words of
  the message schedule from the 16-word window.

Both rest on the instruction rules in `SHA512_block_armv8_rules.lean`.
-/

namespace SHA512VCGen
open BitVec SHA2 sha512_helpers DPSFP

theorem maj_comm_23 (x y z : BitVec 64) : maj x y z = maj x z y := by
  simp only [maj]; ac_rfl

theorem ext_hi (a b c d : BitVec 64) :
    extractLsb' 64 64 (extractLsb' 64 128 (a ++ b ++ (c ++ d))) = b := by bv_decide
theorem ext_lo (a b c d : BitVec 64) :
    extractLsb' 0 64 (extractLsb' 64 128 (a ++ b ++ (c ++ d))) = c := by bv_decide
theorem hi_of_append (a b : BitVec 64) : extractLsb' 64 64 (a ++ b) = a :=
  BitVec.extractLsb'_append_eq_left
theorem lo_of_append (a b : BitVec 64) : extractLsb' 0 64 (a ++ b) = b :=
  BitVec.extractLsb'_append_eq_right

/-- One two-round group of `sha512_block_armv8`, as computed from the registers
holding the working state `S` (`A = b:a`, `B = d:c`, `C = f:e`, `D = h:g`), the
round constants `k1:k0` and the message words `w1:w0`. -/
theorem two_rounds (S : Hash) (k0 k1 w0 w1 : BitVec 64) :
    let A := S.b ++ S.a
    let B := S.d ++ S.c
    let C := S.f ++ S.e
    let D := S.h ++ S.g
    let Kw := binary_vector_op_aux 0 2 64 BitVec.add (k1 ++ k0) (w1 ++ w0) 0#128
    let D1 := binary_vector_op_aux 0 2 64 BitVec.add D (extractLsb' 64 128 (Kw ++ Kw)) 0#128
    let D2 := sha512h (extractLsb' 64 128 (D ++ C)) (extractLsb' 64 128 (C ++ B)) D1
    let S2 := compression_update (compression_update S k0 w0) k1 w1
    sha512h2 B A D2 = S2.b ++ S2.a ∧
    binary_vector_op_aux 0 2 64 BitVec.add B D2 0#128 = S2.f ++ S2.e := by
  intro A B C D Kw D1 D2 S2
  have hD2 : D2 =
      compression_update_t1 S.e S.f S.g S.h k0 w0 ++
      compression_update_t1 (S.d + compression_update_t1 S.e S.f S.g S.h k0 w0) S.e S.f S.g k1 w1 := by
    have := sha512h_rule_2 (extractLsb' 64 128 (D ++ C)) (extractLsb' 64 128 (C ++ B)) D (k1 ++ k0) (w1 ++ w0)
    simp only [D2, D1, Kw, B, C, D] at this ⊢
    rw [this]
    simp only [ext_hi, ext_lo, hi_of_append, lo_of_append]
  refine ⟨?_, ?_⟩
  · rw [sha512h2_rule, hD2]
    simp only [A, B, S2, compression_update, hi_of_append, lo_of_append]
    simp only [compression_update_t2, maj_comm_23 S.a S.c S.b]
    ac_rfl
  · rw [hD2, binary_vector_op_aux_add_128_simp]
    simp only [B, S2, compression_update, hi_of_append, lo_of_append]


/-- The spec's message schedule recurrence. -/
theorem message_schedule_word_rec (m : List (BitVec 64)) {t : Nat} (h : 16 ≤ t) :
    message_schedule_word t m =
      message_schedule_word_aux (message_schedule_word (t - 2) m) (message_schedule_word (t - 7) m)
        (message_schedule_word (t - 15) m) (message_schedule_word (t - 16) m) := by
  rw [message_schedule_word]
  simp [show ¬ t ≤ 15 by omega]

/-- One message-schedule step of a group: from the window `W[t-16 .. t-1]` (as
lane pairs in eight registers) to `W[t+1] : W[t]`. -/
theorem sched_step (w : Nat → BitVec 64) (t : Nat) (ht : 16 ≤ t)
    (hrec : ∀ u, 16 ≤ u → w u = message_schedule_word_aux (w (u - 2)) (w (u - 7)) (w (u - 15)) (w (u - 16))) :
    sha512su1 (w (t - 1) ++ w (t - 2))
      (extractLsb' 64 128 ((w (t - 5) ++ w (t - 6)) ++ (w (t - 7) ++ w (t - 8))))
      (sha512su0 (w (t - 13) ++ w (t - 14)) (w (t - 15) ++ w (t - 16))) =
    w (t + 1) ++ w t := by
  rw [sha512_message_schedule_rule]
  simp only [hi_of_append, lo_of_append, ext_hi, ext_lo]
  rw [hrec (t + 1) (by omega), hrec t ht]
  simp only [show t + 1 - 2 = t - 1 by omega, show t + 1 - 7 = t - 6 by omega,
    show t + 1 - 15 = t - 14 by omega, show t + 1 - 16 = t - 15 by omega]

end SHA512VCGen
