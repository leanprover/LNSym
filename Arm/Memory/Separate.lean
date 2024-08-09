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
  rw [BitVec.le_def]
  rw [BitVec.lt_def, BitVec.gt_def] at h
  rcases h with h | h
  · sorry
  · sorry
  /-
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
  -/

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

----------------------------------------------------------------------
