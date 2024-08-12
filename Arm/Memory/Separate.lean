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
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := by simpa? using h
  simp [mem_legal] at ha hb
  rw [BitVec.le_def] at ha hb
  rw [BitVec.le_def] at h₁ h₂ h₃ h₄
  rw [BitVec.lt_def, BitVec.gt_def]
  by_cases h₅ : a2.toNat < b1.toNat
  · simp [h₅]
  · by_cases h₆ : a1.toNat > b2.toNat
    · simp [h₆]
    · exfalso
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le ha] at h₁ h₂
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le hb] at h₃ h₄
      have h₅' : b1.toNat ≤ a2.toNat := by omega
      have h₆' : a1.toNat ≤ b2.toNat := by omega
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le h₅'] at h₄
      rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le h₆'] at h₂
      omega

@[simp]
theorem BitVec.neg_neg (x : BitVec w₁) : - (- x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp
  by_cases h : x.toNat = 0
  · simp [h]
  · rw [Nat.mod_eq_of_lt (a := 2^w₁ - x.toNat) (by omega)]
    rw [Nat.sub_sub_eq_min]
    rw [Nat.min_def]
    simp [show ¬ 2^w₁ ≤ x.toNat by omega]

@[simp]
theorem BitVec.neg_eq_sub_zero (x : BitVec w₁) : - x = 0 - x := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem toNat_sub_eq_two_pow_sub_add_of_lt
    {a b : BitVec w₁} (hab : a.toNat < b.toNat) : (a - b).toNat = 2^w₁ - b.toNat + a.toNat := by
  simp only [toNat_sub]
  rw [Nat.mod_eq_of_lt (by omega)]

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
  simp
  unfold mem_legal at ha hb
  simp [mem_legal] at ha hb
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
If we express a memory region as `[a..(a+n)]` for `(n : Nat)`,
and this memory region is legal, then we could not have had any wraparound.
Thus, it must be the case that (a + n).toNat = a.toNat + n
-/
theorem add_lt_of_mem_legal_of_lt
    (h : mem_legal a (a + n)) :
    a.toNat + n.toNat < 2^64 := by
  simp [mem_legal] at h
  simp [BitVec.le_def, BitVec.toNat_add] at h
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
  simp [BitVec.add_def]
  rw [Nat.mod_eq_of_lt]
  apply add_lt_of_mem_legal_of_lt h

end Separate


/-#

### New Memory Model

The new memory model is different from the old one in two ways:

1. It uses (base pointer, length) to keep track of memory regions instead of closed inntervals of [pointer 1, pointer 2].
2. To faciliatate the new representation, it bakes in the assumption that the memory region is legal
   (i.e. no wraparound).
3. More softly, it tries to keep reasoning in terms of `Nat` rather than `BitVec` in order to allow easier
   automation via `omega` for proving disjointedness / subset assumptions.

All of the new definitions are named after the old definitions with a prime (') after their name.
For robustness (and confidence), we plan to prove theorems that establish the equivalence of the old and new memory models.
-/
section NewDefitions

/--
`mem_legal' a n` witnessses that `(a + n)` does not overflow, and thus `[a..a+n)` is a valid range
of memory. Note that the interval is left closed, right open, and thus `n` is the number of bytes in the memory range.
-/
def mem_legal' (a : BitVec 64) (n : Nat) : Prop :=
  a.toNat + n ≤ 2^64

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
Legal in the new sense implies legal in the old sense.
-/
theorem mem_legal_of_mem_legal' (h : mem_legal' a n) :
    mem_legal a (a + (BitVec.ofNat 64 (n - 1))) := by
  simp only [mem_legal', mem_legal, BitVec.le_def] at h ⊢
  rw [BitVec.toNat_add_eq_toNat_add_toNat]
  simp
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega


/--
Legal in the new sense implies legal in the old sense.
Note that the subtraction could also have been written as `(b - a).toNat + 1`
-/
theorem mem_legal'_of_mem_legal (h: mem_legal a b) : mem_legal' a (b.toNat - a.toNat + 1) := by
  simp [mem_legal] at h
  rw [mem_legal']
  rw [BitVec.le_def] at h
  omega

def mem_legal'.of_mem_legal'_of_lt (h : mem_legal' a n) (m : Nat) (hm : m ≤ n) :
    mem_legal' a m := by
  simp [mem_legal'] at h ⊢
  omega

/--
`mem_separate' a an b bn` asserts that two memory regions [a..an) and [b..bn) are separate.
Note that we use *half open* intervals.
See also: Why numbering should start at zero (https://www.cs.utexas.edu/~EWD/ewd08xx/EWD831.PDF)
-/
structure mem_separate' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  h : a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn

-- @[simp]
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

/-- `mem_subset' a an b bn` witnesses that `[a..a+an)` is a subset of `[b..b+bn)`-/
structure mem_subset' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  hstart : b ≤ a
  hend : a.toNat + an ≤ b.toNat + bn

theorem mem_subset'_refl (h : mem_legal' a an) : mem_subset' a an a an where
  ha := h
  hb := h
  hstart := by simp [BitVec.le_def]
  hend := by simp [BitVec.le_def]

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
  · simp [BitVec.le_def]
  · omega

-- theorem Nat.sub_mod_eq (x y : Nat) : (x - y) % t =

private theorem Nat.sub_mod_eq_of_lt_of_le {x y : Nat} (hx : x < n) (hy : y ≤ x) :
    (x - y) % n = (x % n) - (y % n) := by
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem BitVec.add_sub_cancel_left {a b : BitVec w₁}
    (hab : a.toNat + b.toNat < 2^w₁) : (a + b) - a = b := by sorry

theorem BitVec.le_add_iff_sub_le {a b c : BitVec w₁}
  (hac : c ≤ a) (hbc : b.toNat + c.toNat < 2^w₁) :
  (a ≤ b + c) ↔ (a - c ≤ b) := by sorry


theorem BitVec.sub_le_sub_iff_right (a b c : BitVec w₁) (hac : c ≤ a) (hbc : c ≤ b) : (a - c ≤ b - c) ↔ a ≤ b := sorry


-- mem_subset' is a safe over-approximation of mem_subset.
theorem mem_subset_of_mem_subset' (h : mem_subset' a an b bn) (han : an > 0) (hbn : bn > 0) :
  mem_subset a (a + BitVec.ofNat 64 (an - 1)) b (b + BitVec.ofNat 64 (bn - 1)):= by
  unfold mem_subset
  obtain ⟨ha, hb, hstart, hend⟩ := h
  unfold mem_legal' at ha hb
  simp only [Nat.reducePow, Nat.add_one_sub_one, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true]
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
    read_mem_bytes xn x (write_mem_bytes yn y val state) =
    read_mem_bytes xn x state := by
  simp only [Nat.reduceMul, write_mem_bytes_eq_write_mem_bytes', read_mem_bytes_eq_read_mem_bytes',
  Nat.reduceAdd, BitVec.ofNat_eq_ofNat, read_mem_bytes'_zero_eq,
  BitVec.cast_eq]
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain ⟨hsrc, hdest, hsplit⟩ := hsep
  rw [getLsb_read_mem_bytes']
  rw [getLsb_write_mem_bytes']
  rw [getLsb_read_mem_bytes']
  simp only [i.isLt]
  simp only [decide_True, ite_eq_left_iff, Bool.true_and]
  intros h₁
  intros h₂
  -- we need to make use of mem_separate to show that src_addr + i / 8 < dest_addr | src_addr + i/7 ≥ dest_addr + 16
  exfalso
  · rcases hsplit with this | this
    · simp [BitVec.le_def] at h₁
      omega
    · have hcontra_h2 : x.toNat + 16 < y.toNat + 16 := by
        simp at this
        have hi : (i : Nat) / 8 < xn := by
          apply Nat.div_lt_of_lt_mul
          simp [Nat.mul_comm]
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

theorem BitVec.toNat_ofNat_lt {n w₁ : Nat} (hn : n < 2^w₁) :
    (BitVec.ofNat w₁ n).toNat = n := by
  simp only [toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem BitVec.ge_of_not_lt (x y : BitVec w₁) (h : ¬ (x < y)) : x ≥ y := by sorry

/- value of `read_mem_bytes'` when subset. -/
theorem read_mem_bytes_write_mem_bytes_eq_extract_LsB_of_mem_subset
  (hsep : mem_subset' x (xn*8) y (yn*8)) -- subset relation.
  (val : BitVec (yn * 8)) :
    read_mem_bytes' xn x (write_mem_bytes' yn y val state) =
      val.extractLsBytes (y.toNat - x.toNat) xn := by
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain ⟨hx, hy, hstart, hend⟩ := hsep

  obtain hx' := hx.size_le_two_pow
  obtain hy' := mem_legal'_def hy

  rw [getLsb_read_mem_bytes' (by omega)]
  rw [getLsb_write_mem_bytes' (by omega)]
  rw [BitVec.getLsb_extractLsByte]
  rw [BitVec.getLsb_extractLsBytes]
  by_cases hxn : xn = 0
  · subst hxn
    exfalso
    have h := i.isLt
    simp at h
  · simp only [show (0 < xn) by omega]
    simp only [show ((y.toNat - x.toNat) * 8 + xn * 8 - 1 - (y.toNat - x.toNat) * 8) = xn * 8 - 1 by omega]
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
      -- TODO: change defn of mem_legal' to use `xn * 8`.
      by_cases h₂ : (x.toNat + i/ 8) < y.toNat
      · -- contradiction
        exfalso
        rw [BitVec.le_def] at hstart
        omega
      · simp only [h₂, if_false]
        -- here: we need to take the else branc of the condition.
        sorry
    · simp [h₁]
      intros h
      apply BitVec.getLsb_ge
      omega



----------------------------------------------------------------------
