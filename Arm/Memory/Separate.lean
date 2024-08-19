/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat
-/
import Arm.State
import Arm.BitVec

section Separate

open BitVec

----------------------------------------------------------------------

-- [x1, x2] denotes a memory region X whose first address is x1 and
-- last address is x2. Note that empty memory regions are ruled out by
-- this formalization.

-- All addresses are 64-bit bitvectors.

-- Note that the `-` operation in the definitions in this file is
-- bitvector subtraction, i.e.,
-- let x and y be n-bit bitvectors:
-- BV2Nat (x - y) =
-- (Nat.mod (Nat.add (BV2Nat x) (Nat.sub 2^n (BV2Nat y))) 2^n).

----------------------------------------------------------------------
-- `mem_overlap`: returns true when memory regions A and B overlap.
--
-- Here is some intuition for this definition: in the first two
-- disjuncts, the frame of reference on the number line (which is
-- really a circle for modular arithmetic) is a1, and in the last two
-- disjuncts, the frame is b1.
--
-- Here are some examples:
--
-- Example 1: The first part of B overlaps with the second part of A;
-- no region wraps around.
--
-- Original number line:
--
--   0     a1    b1    a2    b2
--   |-----|-----|-----|-----|-----...
--
-- Number line with a1 as the frame of reference: b1 <= a2 is true.
--
--   a1     b1    a2    b2
--   |-----|-----|-----|--------...
--
-- Example 2: A and B overlap, and B wraps around (note b2 appears
-- before b1 on the number line).
--
-- Original number line:
--
--   0     a1    b2    a2    b1
--   |-----|-----|-----|-----|-----...
--
-- Number line with a1 as the frame of reference: b2 <= a2 is true.
--
--   a1     b2    a2    b1
--   |-----|-----|-----|--------...
--
-- Example 3: A and B overlap, and B wraps around again.
--
-- Original number line:
--
--   0     a1    a2    b2    b1
--   |-----|-----|-----|-----|-----...
--
-- Number line with b1 as the frame of reference: a1 <= b2 is true (as
-- is a2 <= b2 for this example).
--
--   b1     a1    a2    b2
--   |-----|-----|-----|--------...
--
--
def mem_overlap (a1 a2 b1 b2 : BitVec 64) : Bool :=
  b1 - a1 <= a2 - a1 ||
  b2 - a1 <= a2 - a1 ||
  a1 - b1 <= b2 - b1 ||
  a2 - b1 <= b2 - b1

----------------------------------------------------------------------
-- `mem_separate`: returns true when memory regions A and B are
-- separate from each other.

def mem_separate (a1 a2 b1 b2 : BitVec 64) : Bool :=
  not (mem_overlap a1 a2 b1 b2)

----------------------------------------------------------------------
-- `mem_subset`: returns true when A is a subset of B.
def mem_subset (a1 a2 b1 b2 : BitVec 64) : Bool :=
  (b2 - b1 = BitVec.ofNat 64 (2^64 - 1)) ||
  ((a2 - b1 <= b2 - b1 && a1 - b1 <= a2 - b1))

example : mem_subset 0#64 2#64 0#64 10#64 = true := rfl

example : mem_subset 8#64 10#64 8#64 2#64 = true := rfl

example : mem_subset 10#64 1#64 8#64 2#64 = true := rfl

example : mem_subset 0#64 1#64 8#64 2#64 = true := rfl

example : mem_subset 0#64 2#64 (BitVec.ofNat 64 (2^64 - 1)) 10#64 = true := rfl

-- The second region is just 2 bytes long, but the first one spans the
-- whole memory.
example : mem_subset 0#64 (BitVec.ofNat 64 (2^64 - 1)) (BitVec.ofNat 64 (2^64 - 1)) 0#64 = false := rfl

-- Every region is a subset of the whole memory.
example : mem_subset (BitVec.ofNat 64 (2^64 - 1)) 0#64 0#64 (BitVec.ofNat 64 (2^64 - 1)) = true := rfl

----------------------------------------------------------------------
-- `mem_legal`: returns true when the specified region does not wrap
-- around.
def mem_legal (a1 a2 : BitVec 64) : Bool :=
  a1 <= a2

/-
Given two legal memory regions `[a1, a2]` and `[b1, b2]` that are separated,
it must be the case either:
  - the first one ends before the second one starts (`a2 < b1`),
  - or, the first one starts after the second one ends `(a1 > b2)`,
-/
theorem lt_or_gt_of_mem_separate_of_mem_legal_of_mem_legal (h : mem_separate a1 a2 b1 b2)
    (ha : mem_legal a1 a2) (hb : mem_legal b1 b2) :
    a2 < b1 ∨ a1 > b2 := by
  unfold mem_separate mem_overlap at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := by simpa only [Bool.not_or, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] using h
  simp only [mem_legal, decide_eq_true_eq] at ha hb
  rw [BitVec.le_def] at ha hb
  rw [BitVec.le_def] at h₁ h₂ h₃ h₄
  rw [BitVec.lt_def, BitVec.gt_def]
  by_cases h₅ : a2.toNat < b1.toNat
  · simp only [h₅, gt_iff_lt, BitVec.val_bitvec_lt, true_or]
  · by_cases h₆ : a1.toNat > b2.toNat
    · simp only  [BitVec.val_bitvec_lt, gt_iff_lt, h₆, or_true]
    · exfalso
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le ha] at h₁ h₂
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le hb] at h₃ h₄
      have h₅' : b1.toNat ≤ a2.toNat := by omega
      have h₆' : a1.toNat ≤ b2.toNat := by omega
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le h₅'] at h₄
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le h₆'] at h₂
      omega

/--
Given two legal memory regions `[a1, a2]` and `[b1, b2]`,
such that either the first one ends before the second one starts (`a2 < b1`),
or the first one starts after the second one ends `(a1 > b2)`,
the memory regions are separate.
-/
theorem mem_separate_of_lt_or_gt_of_mem_legal_of_mem_legal (h : a2 < b1 ∨ a1 > b2)
    (ha : mem_legal a1 a2) (hb : mem_legal b1 b2) :
    mem_separate a1 a2 b1 b2 := by
  unfold mem_separate mem_overlap
  simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  unfold mem_legal at ha hb
  simp only [decide_eq_true_eq] at ha hb
  rw [BitVec.le_def] at ha hb
  simp only[BitVec.le_def]
  rw [BitVec.lt_def, BitVec.gt_def] at h
  rcases h with h | h
  · rw [toNat_sub_eq_toNat_sub_toNat_of_le ha]
    have ha1b1 : a1.toNat ≤ b1.toNat := by omega
    rw [toNat_sub_eq_toNat_sub_toNat_of_le ha1b1]
    have ha1b2 : a1.toNat ≤ b2.toNat := by omega
    rw [toNat_sub_eq_toNat_sub_toNat_of_le ha1b2]
    rw [toNat_sub_eq_toNat_sub_toNat_of_le hb]
    have ha1b1' : a1.toNat < b1.toNat := by omega
    rw [toNat_sub_eq_two_pow_sub_add_of_lt ha1b1']
    rw [toNat_sub_eq_two_pow_sub_add_of_lt h]
    omega
  · rw [toNat_sub_eq_toNat_sub_toNat_of_le ha]
    rw [toNat_sub_eq_toNat_sub_toNat_of_le hb]
    have ha2b1 : b1.toNat ≤ a2.toNat := by omega
    rw [toNat_sub_eq_toNat_sub_toNat_of_le ha2b1]
    have ha1b1 : b1.toNat ≤ a1.toNat := by omega
    rw [toNat_sub_eq_toNat_sub_toNat_of_le ha1b1]
    have hb1a1 : b1.toNat < a1.toNat := by omega
    rw [toNat_sub_eq_two_pow_sub_add_of_lt hb1a1]
    have hb2a1 : b2.toNat < a1.toNat := by omega
    rw [toNat_sub_eq_two_pow_sub_add_of_lt hb2a1]
    omega

/--
Given two legal memory regions `[a1, a2]` and `[b1, b2]`,
being separate is *equivalent* to:
- either the first one ends before the second one starts (`a2 < b1`),
- or the first one starts after the second one ends `(a1 > b2)`,
-/
theorem mem_separate_iff_lt_or_gt_of_mem_legal_of_mem_legal
    (ha : mem_legal a1 a2) (hb : mem_legal b1 b2) :
   a2 < b1 ∨ a1 > b2 ↔ mem_separate a1 a2 b1 b2 := by
  constructor
  · intros h
    apply mem_separate_of_lt_or_gt_of_mem_legal_of_mem_legal <;> assumption
  · intros h
    apply lt_or_gt_of_mem_separate_of_mem_legal_of_mem_legal <;> assumption

/--
If we express a memory region as `[a..(a+n)]` for `(n : Nat)`,
and this memory region is legal, then we could not have had any wraparound.
Thus, it must be the case that (a + n).toNat = a.toNat + n
-/
theorem add_lt_of_mem_legal_of_lt
    (h : mem_legal a (a + n)) :
    a.toNat + n.toNat < 2^64 := by
  simp only [mem_legal, decide_eq_true_eq,
    le_def, toNat_add, Nat.reducePow] at h
  by_cases hadd : a.toNat + n.toNat < 2^64
  · assumption
  · exfalso
    have ha : a.toNat < 2^64 := a.isLt;
    have h₂ : a.toNat + n.toNat - 2^64 < 2^64 := by omega
    have hmod : (a.toNat + n.toNat) % 18446744073709551616 = a.toNat + n.toNat - 2^64 := by
      rw [Nat.mod_eq_sub_mod]
      rw [Nat.mod_eq_of_lt h₂]
      omega
    rw [hmod] at h
    omega

/--
If we express a memory region as `[a..(a+n)]` for `(n : Nat)`,
and this memory region is legal, then we could not have had any wraparound.
Thus, it must be the case that (a + n).toNat = a.toNat + n
-/
theorem toNat_add_distrib_of_mem_legal_of_lt
    (h : mem_legal a (a + n)) :
    (a + n).toNat = a.toNat + n.toNat := by
  simp only [add_def, toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt]
  apply add_lt_of_mem_legal_of_lt h

end Separate

/-#

### New Memory Model

The new memory model is different from the old one in two ways:

1. It uses (base pointer, length) to keep track of memory regions instead of closed intervals of [pointer 1, pointer 2].
2. To facilitate the new representation, it bakes in the assumption that the memory region is legal
   (i.e. no wraparound).
3. More softly, it tries to keep reasoning in terms of `Nat` rather than `BitVec` in order to allow easier
   automation via `omega` for proving disjointedness / subset assumptions.

All of the new definitions are named after the old definitions with a prime (') after their name.
For robustness (and confidence), we plan to prove theorems that establish the equivalence of the old and new memory models.
-/
section NewDefinitions

/--
`mem_legal' a n` witnessses that `(a + n)` does not overflow, and thus `[a..a+n)` is a valid range
of memory. Note that the interval is left closed, right open, and thus `n` is the number of bytes in the memory range.
-/
def mem_legal' (a : BitVec 64) (n : Nat) : Prop :=
  a.toNat + n ≤ 2^64

/-- Build a `mem_legal'` from a proof obligation that can be closed by `omega`. -/
def mem_legal'.of_omega (h : a.toNat + n ≤ 2^64) : mem_legal' a n := h

theorem mem_legal'.def (h : mem_legal' a n) : a.toNat + n ≤ 2^64 := h

/--
@bollu: have proof automation exploit this.
Equation lemma for `mem_legal'`.
-/
theorem mem_legal'_def (h : mem_legal' a n) : a.toNat + n ≤ 2^64 := h

/--
The maximum size of the range we can choose to allocate is 2^64.
@bollu: have proof automation exploit this.
-/
theorem mem_legal'.size_le_two_pow (h : mem_legal' a n) : n ≤ 2 ^ 64 := by
  rw [mem_legal'] at h
  omega


/--
If we know that `[a..a+n)` is legal and `a'.toNat + n' < a.toNat + n`,
then `[a'..a'+n')` is also legal. -/
theorem mem_legal'.of_mem_legal'_of_lt
    (h : mem_legal' a n) (hn : a'.toNat + n' ≤ a.toNat + n) :
    mem_legal' a' n' := by
  unfold mem_legal' at h ⊢
  omega

/--
If we know that `[a..a+n)` is legal, -/
theorem mem_legal'.of_mem_legal'_self_of_lt
    (h : mem_legal' a n) (hn : a.toNat + offset + n' ≤ a.toNat + n) :
    mem_legal' (a + (BitVec.ofNat 64 offset)) n' := by
  unfold mem_legal' at h ⊢
  bv_omega

/-- If we know that `[a..a+n)` is legal, then `a+m` does not overflow for `m < n`. -/
theorem mem_legal'.toNat_add_eq_toNat_add_toNat_of_le
    (h : mem_legal' a n) (hm : m < n) :
    (a + (BitVec.ofNat 64 m)).toNat = a.toNat + m := by
  have := h.size_le_two_pow
  have := h.def
  bv_omega

/--
Legal in the new sense implies legal in the old sense.
-/
theorem mem_legal_of_mem_legal' (h : mem_legal' a n) :
    mem_legal a (a + (BitVec.ofNat 64 (n - 1))) := by
  simp only [mem_legal', mem_legal, BitVec.le_def] at h ⊢
  rw [BitVec.toNat_add_eq_toNat_add_toNat]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.le_add_right, decide_True]
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega


/--
Legal in the new sense implies legal in the old sense.
Note that the subtraction could also have been written as `(b - a).toNat + 1`
-/
theorem mem_legal'_of_mem_legal (h: mem_legal a b) : mem_legal' a (b.toNat - a.toNat + 1) := by
  simp only [mem_legal, decide_eq_true_eq] at h
  rw [mem_legal']
  rw [BitVec.le_def] at h
  omega


def mem_legal'_of_mem_legal'_of_lt (h : mem_legal' a n) (m : Nat) (hm : m ≤ n) :
    mem_legal' a m := by
  simp only [mem_legal', Nat.reducePow] at h ⊢
  omega

/--
`mem_legal` is equivalent to `mem_legal'`.
-/
theorem mem_legal_iff_mem_legal' : mem_legal a b ↔
    mem_legal' a ((b - a).toNat + 1) := by
  constructor
  · intros h
    simp only [mem_legal, decide_eq_true_eq] at h
    rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le h]
    · simp only [mem_legal']
      omega
  · intros h
    simp only [mem_legal'] at h
    simp only [mem_legal, BitVec.le_def, decide_eq_true_eq]
    apply Classical.byContradiction
    intros h₂
    rw [BitVec.toNat_sub_eq_two_pow_sub_add_of_lt (by omega)] at h
    omega

/--
`mem_separate' a an b bn` asserts that two memory regions [a..an) and [b..bn) are separate.
Note that we use *half open* intervals.
In prose, we may notate this as `[a..an) ⟂ [b..bn)`.
See also: Why numbering should start at zero (https://www.cs.utexas.edu/~EWD/ewd08xx/EWD831.PDF)
-/
structure mem_separate' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  h : a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn

/--
Unfold the definition of `mem_subset'` to write definitions that `omega` can process.
-/
theorem mem_separate'.omega_def (h : mem_separate' a an b bn) :
  a.toNat + an ≤ 2^64 ∧
  b.toNat + bn ≤ 2^64 ∧
  (a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn) := by
  obtain ⟨ha, hb, hsplit⟩ := h
  unfold mem_legal' at ha hb
  omega

/-- Build a mem_subset' from a goal that `h` that can be closed by `omega`. -/
theorem mem_separate'.of_omega
  (h :a.toNat + an ≤ 2^64 ∧
  b.toNat + bn ≤ 2^64 ∧
  (a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn) := by omega) :
  mem_separate' a an b bn :=  by
constructor
· unfold mem_legal'; omega
· unfold mem_legal'; omega
· omega

theorem BitVec.not_le_eq_lt {a b : BitVec w₁} : (¬ (a ≤ b)) ↔ b < a := by
  rw [BitVec.le_def, BitVec.lt_def]
  omega

/-#
This is a theorem we ought to prove, which establishes the equivalence
between the old and new defintions of 'mem_separate'.
However, the proof is finicky, and so we leave it commented for now.
-/
/-
theorem mem_separate_of_mem_separate' (h : mem_separate' a an b bn)
    (ha' : a' = a + (BitVec.ofNat w₁ (an - 1) ) (hb' : b' = b + (BitVec.ofNat w₁ (bn - 1)))
    (hlegala : mem_legal a an) (hlegalb: mem_legal b bn) :
    mem_separate a a' b b' := by
  simp [mem_separate]
  simp [mem_overlap]
  obtain ⟨ha, hb, hsep⟩ := h
  simp [mem_legal'] at ha hb
  subst ha'
  subst hb'
  apply Classical.byContradiction
  intro hcontra
  · sorry
  · sorry
-/

/-- `mem_subset' a an b bn` witnesses that `[a..a+an)` is a subset of `[b..b+bn)`.
In prose, we may notate this as `[a..an) ≤ [b..bn)`.
-/
structure mem_subset' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  hstart : b ≤ a
  hend : a.toNat + an ≤ b.toNat + bn

/--
Unfold the definition of `mem_subset'` to write definitions that `omega` can process.
-/
theorem mem_subset'.omega_def (h : mem_subset' a an b bn) :
  a.toNat + an ≤ 2^64 ∧
  b.toNat + bn ≤ 2^64 ∧
  b.toNat ≤ a.toNat ∧
  a.toNat + an ≤ b.toNat + bn := by
  obtain ⟨ha, hb, hstart, hend⟩ := h
  rw [BitVec.le_def] at hstart
  unfold mem_legal' at ha hb
  omega

/-- Build a mem_subset' from a goal that `h` that can be closed by `omega`. -/
theorem mem_subset'.of_omega
  (h : a.toNat + an ≤ 2^64 ∧
  b.toNat + bn ≤ 2^64 ∧
  b.toNat ≤ a.toNat ∧
  a.toNat + an ≤ b.toNat + bn) : mem_subset' a an b bn :=  by
constructor
· unfold mem_legal'; omega
· unfold mem_legal'; omega
· rw [BitVec.le_def]; omega
· omega

theorem mem_subset'_refl (h : mem_legal' a an) : mem_subset' a an a an where
  ha := h
  hb := h
  hstart := by simp only [BitVec.le_def, Nat.le_refl]
  hend := by simp only [Nat.le_refl]

/--
If `[a'..a'+an')` begins at least where `[a..an)` begins,
and ends before `[a..an)` ends, and if `[a..an)` is a subset of `[b..bn)`,
then `[a'..a'+an')` is a subset of `[b..bn)`.
-/
theorem mem_subset'_of_le_of_le {a' : BitVec 64} (h : mem_subset' a an b bn)
  (ha' : a.toNat ≤ a'.toNat) (han' : a'.toNat + an' ≤ a.toNat + an) :
  mem_subset' a' an' b bn where
  ha := by
    obtain ⟨ha, hb, hstart, hend⟩ := h
    simp only [mem_legal', Nat.reducePow] at ha hb ⊢
    simp_all only [BitVec.le_def]
    omega
  hb := h.hb
  hstart := by
    obtain ⟨ha, hb, hstart, hend⟩ := h
    simp only [mem_legal', Nat.reducePow] at ha hb
    simp_all only [BitVec.le_def]
    omega
  hend := by
    obtain ⟨ha, hb, hstart, hend⟩ := h
    simp only [mem_legal', Nat.reducePow] at ha hb
    simp_all only [BitVec.le_def]
    omega

/--
If `[a..an)` is a subset of `[b..bn)`,
then `[a..an')` is a subset of `[b..bn)` if `an' ≤ an`.
-/
theorem mem_subset'_of_length_le (h : mem_subset' a an b bn)
  (han' : an' ≤ an) : mem_subset' a an' b bn := by
  apply mem_subset'_of_le_of_le h
  · simp only [Nat.le_refl]
  · omega

/-- if `[a..an) ≤ [b..bn)` and `[b..bn) ⟂ [c..cn)`,
then `[a..an) ⟂ [c..cn)`.
(Recall that `⟂` stands for `mem_separate'`.)
-/
theorem mem_separate'_of_mem_separate'_of_mem_subset'
    (hsep : mem_separate' b bn c cn)
    (hsub : mem_subset' a an b bn) :
    mem_separate' a an c cn := by
  obtain ⟨_, hsep₂, hsep₃⟩ := hsep
  obtain ⟨hsub₁, _, hsub₃, hsub₄⟩ := hsub
  simp_all only [BitVec.le_def]
  constructor <;>
    solve
    | omega
    | assumption

private theorem Nat.sub_mod_eq_of_lt_of_le {x y : Nat} (hx : x < n) (hy : y ≤ x) :
    (x - y) % n = (x % n) - (y % n) := by
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]

-- `mem_subset'` implies mem_subset.
theorem mem_subset_of_mem_subset' (h : mem_subset' a an b bn) (han : an > 0) (hbn : bn > 0) :
  mem_subset a (a + BitVec.ofNat 64 (an - 1)) b (b + BitVec.ofNat 64 (bn - 1)):= by
  unfold mem_subset
  obtain ⟨ha, hb, hstart, hend⟩ := h
  unfold mem_legal' at ha hb
  simp only [bitvec_rules, minimal_theory]
  by_cases hb : bn = 2^64
  · left
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le ]
    · rw [BitVec.toNat_add_eq_toNat_add_toNat]
      · simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [BitVec.toNat_ofNat, Nat.reducePow]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · simp only [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · have hbn : (BitVec.ofNat 64 (bn - 1)).toNat = (bn - 1) := by simp; omega
    have han : (BitVec.ofNat 64 (an - 1)).toNat = (an - 1) := by simp; omega
    rw [BitVec.le_def] at hstart
    right
    constructor
    · rw [BitVec.add_sub_cancel_left]
      · apply (BitVec.le_add_iff_sub_le _ _).mp
        · rw [BitVec.le_def, BitVec.toNat_add, han, BitVec.toNat_add, hbn]; omega
        . rw [BitVec.le_def, BitVec.toNat_add, han]; omega
        · rw [hbn]; omega
      · rw [hbn]; omega
    · rw [BitVec.sub_le_sub_iff_right]
      · rw [BitVec.le_def, BitVec.toNat_add, han]
        omega
      · assumption
      · rw [BitVec.le_def, BitVec.toNat_add, han]
        omega

/- value of read_mem_bytes when separate. -/
theorem read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate'
  (hsep : mem_separate' x xn y yn) -- separation
  (val : BitVec (yn * 8)) :
    read_mem_bytes xn x (write_mem_bytes yn y val mem) =
    read_mem_bytes xn x mem := by
  simp only [bitvec_rules, minimal_theory, memory_rules]
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain ⟨hsrc, hdest, hsplit⟩ := hsep
  rw [Memory.getLsb_read_bytes, Memory.getLsb_write_bytes, Memory.getLsb_read_bytes]
  simp only [i.isLt]
  simp only [decide_True, ite_eq_left_iff, Bool.true_and]
  intros h₁
  intros h₂
  -- we need to make use of mem_separate to show that src_addr + i / 8 < dest_addr | src_addr + i/7 ≥ dest_addr + 16
  exfalso
  · rcases hsplit with this | this
    · simp only [bitvec_rules, minimal_theory, BitVec.not_lt, BitVec.le_def, BitVec.toNat_add,
        BitVec.toNat_ofNat] at h₁
      omega
    · have hcontra_h2 : x.toNat + 16 < y.toNat + 16 := by
        simp at this
        have hi : (i : Nat) / 8 < xn := by
          apply Nat.div_lt_of_lt_mul
          simp only [Nat.mul_comm, Fin.is_lt]
        rw [BitVec.toNat_add_eq_toNat_add_toNat] at h₂
        · omega
        · have := mem_legal'_def hsrc
          apply Nat.lt_of_lt_of_le _ this
          apply Nat.add_lt_add_iff_left.mpr
          simp
          rw [Nat.mod_eq_of_lt]
          omega
          omega
      omega
  · have := hsrc.size_le_two_pow
    omega
  · have := mem_legal'_def hdest
    omega
  · have := hsrc.size_le_two_pow
    omega

/- value of `read_mem_bytes'` when subset. -/
theorem read_mem_bytes_write_mem_bytes_eq_extract_LsB_of_mem_subset
  (hsep : mem_subset' x xn y yn) -- subset relation.
  (val : BitVec (yn * 8)) :
    Memory.read_bytes xn x (Memory.write_bytes yn y val mem) =
      val.extractLsBytes (x.toNat - y.toNat) xn := by
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain ⟨hx, hy, hstart, hend⟩ := hsep

  obtain hx' := hx.size_le_two_pow
  obtain hy' := mem_legal'_def hy

  rw [Memory.getLsb_read_bytes (by omega)]
  rw [Memory.getLsb_write_bytes (by omega)]
  rw [BitVec.getLsb_extractLsByte]
  rw [BitVec.getLsb_extractLsBytes]
  by_cases hxn : xn = 0
  · subst hxn
    exfalso
    have h := i.isLt
    simp at h
  · simp only [show (0 < xn) by omega]
    simp only [show ((x.toNat - y.toNat) * 8 + xn * 8 - 1 - (x.toNat - y.toNat) * 8) = xn * 8 - 1 by omega]
    by_cases h₁ : ↑i < xn * 8
    · simp only [h₁]
      simp only [show (i ≤ xn * 8 - 1) by omega]
      simp only [decide_True, Bool.true_and]
      obtain ⟨i, hi⟩ := i
      simp only at h₁
      simp only []
      have h₁' : (BitVec.ofNat 64 (i / 8)).toNat = (i / 8) := by
        apply BitVec.toNat_ofNat_lt
        omega
      have hadd : (x + BitVec.ofNat 64 (↑i / 8)).toNat = x.toNat + (i / 8) := by
        rw [BitVec.toNat_add_eq_toNat_add_toNat (by omega)]
        rw [BitVec.toNat_ofNat_lt (by omega)]
      simp only [BitVec.lt_def]
      simp only [hadd]
      by_cases h₂ : (x.toNat + i/ 8) < y.toNat
      · -- contradiction
        exfalso
        rw [BitVec.le_def] at hstart
        omega
      · simp only [h₂, if_false]
        by_cases h₃ : x.toNat + i / 8 ≥ y.toNat + yn
        · rw [BitVec.le_def] at hstart
          omega
        · simp only [h₃, if_false]
          simp only [show i % 8 ≤ 7 by omega]
          simp only [decide_True, Bool.true_and]
          -- ⊢ val.getLsb ((x + BitVec.ofNat 64 (i / 8) - y).toNat * 8 + i % 8) = val.getLsb ((y.toNat - x.toNat) * 8 + i)
          /-
          This is clearly true, it simplifes to (x.toNat - y.toNat) * 8 + (i/8)*8 + i % 8.
          which equals (x.toNat - y.toNat + i)
          -/
          congr 1
          rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le (by rw [BitVec.le_def]; omega)]
          rw [BitVec.toNat_add_eq_toNat_add_toNat (by omega)]
          rw [BitVec.toNat_ofNat_lt (by omega)]
          have himod : (i / 8) * 8 + (i % 8) = i := by omega
          rw [Nat.mul_sub_right_distrib, Nat.mul_sub_right_distrib,
            Nat.add_mul]
          conv =>
            rhs
            rw [← himod]
          rw [BitVec.le_def] at hstart
          omega
    · simp only [h₁, bitvec_rules, minimal_theory]
      intros h
      apply BitVec.getLsb_ge
      omega

/- value of read_mem_bytes when subset of another read. -/
theorem read_mem_bytes_eq_extractLsBytes_of_subset_of_read_mem_bytes
    {mem : Memory}
    (hread : mem.read_bytes bn b = val)
    (hsubset : mem_subset' a an b bn) :
    mem.read_bytes an a = val.extractLsBytes (a.toNat - b.toNat) an := by
  apply BitVec.eq_of_extractLsByte_eq
  intros i
  -- simp [memory_rules]
  sorry

/--
info: 'read_mem_bytes_write_mem_bytes_eq_extract_LsB_of_mem_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms read_mem_bytes_write_mem_bytes_eq_extract_LsB_of_mem_subset


end NewDefinitions
