/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

This file contains bitvector theorems that stress Isabelle automation.
We port the file to Lean for comparison.
-/

import LeanSAT
open BitVec

/--
`mask w n` is an w-bit word where the low `n`
bits are `1`s and the upper bits are `0`s.
 -/
def mask (w : Nat) (i : Nat) : BitVec w :=
  match i with
  | 0 => 0#w
  | i' + 1 => 1#w <<< i' ||| mask w i'

@[simp]
theorem getLsb_mask : (mask w₁ i).getLsb j =
  (decide (j < i) && (j < w₁)) := by
  induction i generalizing w₁ j
  case zero => simp [mask]
  case succ i ih =>
    simp only [mask, getLsb_or, getLsb_shiftLeft, getLsb_one]
    rw [ih]
    by_cases h : j < i
    · simp [h]; omega
    · simp [h]
      by_cases h' : j < w₁
      · simp [h', show 0 < w₁ by omega]; omega
      · simp [h']

@[simp]
def mask64 (i : Nat) : BitVec 64 := mask 64 i

/--
This is challenging: the number `n`, `m` are used both as:
- bitvectors (for the shifts).
- `nat`s for the mask.
-/
theorem mask_split (x : BitVec 64) (n m : Nat) :
    (x &&& mask64 (n + m)) = (x &&& (mask64 m <<< n) ||| x &&& mask64 n) := by
  simp only [mask64]
  apply BitVec.eq_of_getLsb_eq
  simp only [getLsb_and, getLsb_mask, Fin.is_lt, decide_True, Bool.and_true, getLsb_or,
    getLsb_shiftLeft, Bool.true_and]
  intros i
  by_cases h : (i : Nat) < n
  · simp [h]
    omega
  · simp [h]
    by_cases h' : (i : Nat) < n + m
    · simp [h']
      omega
    · simp [h']
      omega

/-- info: 'mask_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mask_split

-- ∀x, y: word64. ∀m, k: ℕ. (x & mask64 (m + k) = y) ⟹ ((x & mask64 m) = (y & mask64 m))
theorem smaller_mask_same (x y : BitVec 64) (m k : Nat)
    (h : x &&& mask64 (m + k) = y) :
    x &&& mask64 m = y &&& mask64 m := by
  apply BitVec.eq_of_getLsb_eq
  simp
  intros i
  have : (x &&& mask64 (m + k)).getLsb i = (y).getLsb i := by rw [h]
  simp only [mask64, getLsb_and, getLsb_mask, Fin.is_lt, decide_True, Bool.and_true] at this
  by_cases h : (i : Nat) < m
  · simpa [h, show (i : Nat) < m + k by omega] using this
  · simp [h]

/-- info: 'smaller_mask_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms smaller_mask_same

/-
mask_split_left
∀x, y: word64. ∀n: ℕ.
    ((x & (mask64 m << n) | x & mask64 n) = y)
    ⟹
    (x & (mask m64 << n) = (y & (mask64 m << n)))
-/
theorem mask_split_left (x y : BitVec 64) (n m : Nat)
    (h : (x &&& (mask64 m <<< n) ||| x &&& mask64 n) = y) :
    x &&& (mask64 m <<< n) = (y &&& (mask64 m <<< n)) := by
  bv_decide

/--
It's highly suspect that LeanSAT can prove `mask_split_left` without
unfolding the definition of `mask64`.
For sanity, we prove the same theorem with:
- `mask64 m` as an uninterpreted symbol called `mask64m`,
- `mask64 n` as an uninterpreted symbol `mask64n`.
-/
theorem mask_split_left' (x y mask64m mask64n : BitVec 64) (n : Nat)
    (h : (x &&& (mask64m <<< n) ||| x &&& mask64n) = y) :
    x &&& (mask64m <<< n) = (y &&& (mask64m <<< n)) := by
  rw [← h]
  apply BitVec.eq_of_getLsb_eq
  intros i
  simp only [getLsb_and, getLsb_shiftLeft, Fin.is_lt, decide_True, Bool.true_and, getLsb_or]
  rcases (x.getLsb i) with rfl | rfl
  · simp
  · simp
    intros hi hk
    simp [hi, hk]

/--
info: 'mask_split_left' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms mask_split_left

/-
mask_split_right
∀x, y: word64. ∀n: ℕ.
    ((x & (mask64 m << n)) | (x & mask64 n)) = y)
    ⟹
    ((x & mask64 n) = (y & mask64 n))
-/
theorem mask_split_right (x y : BitVec 64) (n m : Nat)
    (h : ((x &&& (mask64 m <<< n)) ||| (x &&& mask64 n)) = y) :
    x &&& mask64 n = y &&& mask64 n := by
  bv_decide

/--
See `mask_split_left'`.
We prove `mask_split_right` with
- `mask64 m` as an uninterpreted symbol called `mask64m`,
- `mask64 n` as an uninterpreted symbol `mask64n`.
-/
theorem mask_split_right' (x y mask64m mask64n : BitVec 64) (n : Nat)
    (h : ((x &&& (mask64m <<< n)) ||| (x &&& mask64n)) = y) :
    x &&& mask64n = y &&& mask64n := by
  rw [← h]
  apply BitVec.eq_of_getLsb_eq
  intros i
  simp only [getLsb_and, getLsb_shiftLeft, Fin.is_lt, decide_True, Bool.true_and, getLsb_or]
  rcases (x.getLsb i) with rfl | rfl
  · simp
  · simp
    intros hi
    simp [hi]

/--
info: 'mask_split_right' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms mask_split_right

/-
address_size_fault_lemma
∀x: word64. (x & (mask64 4 << 2) = 0)
            ⇔
            ((x & mask64 6) = 0x0000_0000) ⋁
             (x & mask64 6) = 0x0000_0001) ⋁
             (x & mask64 6) = 0x0000_0002) ⋁
             (x & mask64 6) = 0x0000_0003)  )
-/
theorem address_size_fault_lemma
    (x : BitVec 64) :
    x &&& (mask64 4 <<< 2) = 0
    ↔
    (x &&& mask64 6 = 0x00000000) ∨
    (x &&& mask64 6 = 0x00000001) ∨
    (x &&& mask64 6 = 0x00000002) ∨
    (x &&& mask64 6 = 0x00000003) := by
  simp [mask64, mask]
  bv_decide

/-
∀m, n: ℕ. (m < 4096 ∧ n ≤ 511) ⟹ ((n * 0x0000_1000) + word_of64 m) ≤ 0x01FF_FFFF)
-/
theorem some_lemma (m n : Nat) (h : m < 4096 ∧ n ≤ 511) :
    (n * 0x00001000) + m ≤ 0x01FFFFFF := by
  omega

/-- info: 'some_lemma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms some_lemma

/-
∀x: word64. (x & 0x3c  ==  0x0000_0000)
           ⇔
           ((x & 0x0000_003f == 0x0000_0000) ⋁
            (x & 0x0000_003f == 0x0000_0001) ⋁
            (x & 0x0000_003f == 0x0000_0002) ⋁
            (x & 0x0000_003f == 0x0000_0003)  )
-/
theorem bitmask_lemma (x : BitVec 64) :
    x &&& 0x3c = 0x00000000
    ↔
    (x &&& 0x0000003f = 0x00000000) ∨
    (x &&& 0x0000003f = 0x00000001) ∨
    (x &&& 0x0000003f = 0x00000002) ∨
    (x &&& 0x0000003f = 0x00000003) := by
  bv_decide

/--
info: 'bitmask_lemma' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms bitmask_lemma

/-
∀m: word64. ∀P: word64 ➝ 𝔹.
  (m ≤ 0x0000_0006 ∧
   P 0x0000_0000   ∧
   P 0x0000_0001   ∧
   P 0x0000_0002   ∧
   P 0x0000_0003   ∧
   P 0x0000_0004   ∧
   P 0x0000_0005   ∧
   P 0x0000_0006)
  ⟹
  P m
-/
theorem less_6E (m : BitVec 64) (P : BitVec 64 → Bool)
    (h : m ≤ 0x00000006 ∧
         P 0x00000000 ∧
         P 0x00000001 ∧
         P 0x00000002 ∧
         P 0x00000003 ∧
         P 0x00000004 ∧
         P 0x00000005 ∧
         P 0x00000006) :
    P m := by
  obtain ⟨m, hm⟩ := m
  simp_all [BitVec.le_def]
  -- this proof is unfortunate, it's surely golfable,
  -- and one would hope that the automation would do better.
  obtain hm | hm | hm | hm | hm | hm | hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨
    m = 4 ∨ m = 5 ∨ m = 6 := by omega
  repeat (simp [hm] at h ⊢; simp [h])

/-- info: 'less_6E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms less_6E
