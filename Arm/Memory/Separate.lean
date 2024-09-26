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
      bv_omega

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
  bv_omega

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
    bv_omega

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


theorem foo : BitVec.ofNat 64 100 < BitVec.ofNat 64 200 := by
  bv_decide

/--
`mem_legal' a n` witnessses that `(a + n)` does not overflow, and thus `[a..a+n)` is a valid range
of memory. Note that the interval is left closed, right open, and thus `n` is the number of bytes in the memory range.
-/
def mem_legal' (a : BitVec 64) (n : BitVec 64) : Prop :=
  a ≤ a + n

/--
`mem_separate' a an b bn` asserts that two memory regions [a..an) and [b..bn) are separate.
Note that we use *half open* intervals.
In prose, we may notate this as `[a..an) ⟂ [b..bn)`.
See also: Why numbering should start at zero (https://www.cs.utexas.edu/~EWD/ewd08xx/EWD831.PDF)
-/
structure mem_separate' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  h : a + an ≤ b  ∨ a ≥ b + bn

/-- `mem_subset' a an b bn` witnesses that `[a..a+an)` is a subset of `[b..b+bn)`.
In prose, we may notate this as `[a..an) ≤ [b..bn)`.
-/
structure mem_subset' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop where
  ha : mem_legal' a an
  hb : mem_legal' b bn
  hstart : b ≤ a
  hend : a + an ≤ b + bn


theorem mem_separate'_of_mem_separate'_of_mem_subset'
    (hsep : mem_separate' b bn c cn)
    (hsub : mem_subset' a an b bn) :
    mem_separate' a an c cn := by
  obtain ⟨_, hsep₂, hsep₃⟩ := hsep
  obtain ⟨hsub₁, _, hsub₃, hsub₄⟩ := hsub
  simp [mem_legal'] at *
  constructor <;>
    solve
    | bv_decide
    | assumption

/- value of read_mem_bytes when separate from the write. -/
axiom Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'
    {yn : Nat}
    {y : BitVec 64}
    {x : BitVec 64}
    {xn : Nat}
    {mem : Memory}
    (hsep : mem_separate' x xn y yn) -- separation
    (val : BitVec (yn * 8)) :
    Memory.read_bytes xn x (Memory.write_bytes yn y val mem) =
    Memory.read_bytes xn x mem

/- value of `read_mem_bytes'` when subset of the write. -/
axiom Memory.read_bytes_write_bytes_eq_of_mem_subset'
    {yn : Nat}
    {y : BitVec 64}
    {x : BitVec 64}
    {xn : Nat}
    {mem : Memory}
    (hsep : mem_subset' x xn y yn) -- subset relation.
    (val : BitVec (yn * 8)) :
    Memory.read_bytes xn x (Memory.write_bytes yn y val mem) =
      val.extractLsBytes (x.toNat - y.toNat) xn

/- value of read_mem_bytes when subset of another *read*. -/
axiom Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
    {bn : Nat}
    {b : BitVec 64}
    {a : BitVec 64}
    {an : Nat}
    {val : BitVec (bn * 8)}
    {mem : Memory}
    (hread : mem.read_bytes bn b = val)
    (hsubset : mem_subset' a an b bn) :
    mem.read_bytes an a = val.extractLsBytes (a.toNat - b.toNat) an

/-- A region of memory, given by (base pointer, length) -/
abbrev Memory.Region := BitVec 64 × Nat

def Memory.Region.mk (a : BitVec 64) (n : Nat) : Memory.Region := (a, n)

/-- A hypothesis that memory regions `a` and `b` are separate. -/
def Memory.Region.separate (a b : Memory.Region) : Prop :=
  mem_separate' a.fst a.snd b.fst b.snd

/-- A list of memory regions, that are known to be pairwise disjoint. -/
def Memory.Region.pairwiseSeparate (mems : List Memory.Region) : Prop :=
  mems.Pairwise Memory.Region.separate

/-- If `i ≠ j`, then prove that `mems[i] ⟂ mems[j]`.
The theorem is stated in mildly awkward fashion for ease of use during proof automation.
-/
axiom Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem {mems: List Memory.Region}
  (h : Memory.Region.pairwiseSeparate mems)
  (i j : Nat)
  (hij : i ≠ j)
  (a b : Memory.Region)
  (ha : mems.get? i = some a) (hb : mems.get? j = some b) :
    mem_separate' a.fst a.snd b.fst b.snd

end NewDefinitions
