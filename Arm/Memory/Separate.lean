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
Thus, it must be the case that (a + n).toNat = a.base.toNat + n
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
Thus, it must be the case that (a + n).toNat = a.base.toNat + n
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

namespace Memory

/-- A half open interval of memory [base..base+len). -/
structure Region where
  /-- Base pointer of the buffer. -/
  base : BitVec 64
  /-- Length of the buffer. -/
  len : Nat


/--
`buf.legal ` witnessses that `(buf.base + buf.len)` does not overflow.
Thus `[buf..buf+buf.len)`is a valid range of memory.
Note that the interval is left closed, right open, and thus `buf.len` is the
number of bytes in the memory range.
-/
def Region.legal (b : Region) : Prop :=
  b.base.toNat + b.len ≤ 2^64

/-- Build a `Region.legal` from a proof obligation that can be closed by `omega`. -/
def Region.legal.of_omega {b : Region} (h : b.base.toNat + b.len ≤ 2^64) : b.legal := h

theorem Region.legal.omega_def {b : Region} (h : b.legal) : b.base.toNat + b.len ≤ 2^64 := h

/--
@bollu: have proof automation exploit this.
Equation lemma for `Region.legal`.
-/
theorem Region.legal_def {b : Region}
  (h : b.legal) : b.base.toNat + b.len ≤ 2^64 := h

/--
The maximum size of the range we can choose to allocate is 2^64.
@bollu: have proof automation exploit this.
-/
theorem Region.legal.size_le_two_pow {b : Region} (h : b.legal) : b.len ≤ 2 ^ 64 := by
  rw [Region.legal] at h
  omega


/--
If we know that `[a..a+n)` is legal and `a'.toNat + n' < a.base.toNat + n`,
then `[a'..a'+n')` is also legal. -/
theorem Region.legal.of_Region.legal_of_lt
    (h : Region.legal a) (hn : a'.base.toNat + a'.len ≤ a.base.toNat + a.len) :
    Region.legal a' := by
  unfold Region.legal at h ⊢
  omega
/--
Legal in the new sense implies legal in the old sense.
-/
theorem mem_legal_of_Region.legal (h : Region.legal a) :
    mem_legal a.base (a.base + (BitVec.ofNat 64 (a.len - 1))) := by
  simp only [Region.legal, mem_legal, BitVec.le_def] at h ⊢
  rw [BitVec.toNat_add_eq_toNat_add_toNat]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.le_add_right, decide_True]
  bv_omega

/--
Legal in the new sense implies legal in the old sense.
Note that the subtraction could also have been written as `(b - a).toNat + 1`
-/
theorem Region.legal_of_mem_legal (h: mem_legal a b) : Region.legal { base := a , len := (b.toNat - a.toNat + 1) } := by
  simp only [mem_legal, decide_eq_true_eq] at h
  rw [Region.legal]
  bv_omega

def Region.legal_of_Region.legal_of_lt (h : Region.legal a) (m : Nat) (hm : m ≤ a.len) :
    Region.legal { a with len := m } := by
  simp only [Region.legal, Nat.reducePow] at h ⊢
  omega

/--
`mem_legal` is equivalent to `Region.legal`.
-/
theorem mem_legal_iff_Region.legal : mem_legal a b ↔
    Region.legal { base := a, len := ((b - a).toNat + 1) } := by
  constructor
  · intros h
    simp only [mem_legal, decide_eq_true_eq] at h
    rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le h]
    · simp only [Region.legal]
      omega
  · intros h
    simp only [Region.legal] at h
    simp only [mem_legal, BitVec.le_def, decide_eq_true_eq]
    bv_omega

/--
`Region.separate a an b bn` asserts that two memory regions [a..an) and [b..bn) are separate.
Note that we use *half open* intervals.
In prose, we may notate this as `[a..an) ⟂ [b..bn)`.
See also: Why numbering should start at zero (https://www.cs.utexas.edu/~EWD/ewd08xx/EWD831.PDF)
-/
structure Region.Separate (a b : Region) : Prop where
  ha : Region.legal a
  hb : Region.legal b
  h : a.base.toNat + a.len ≤ b.base.toNat ∨ a.base.toNat ≥ b.base.toNat + b.len

scoped notation a " ⟂ " b  => (Region.Separate a b)


/--
Unfold the definition of `Region.Subset` to write definitions that `omega` can process.
-/
theorem Region.Separate.omega_def {a b : Region} (h : Region.Separate a b) :
  (a.base.toNat + a.len ≤ 2^64 ∧
  b.base.toNat + b.len ≤ 2^64 ∧
  (a.base.toNat + a.len ≤ b.base.toNat ∨ a.base.toNat ≥ b.base.toNat + b.len)) := by
  obtain ⟨ha, hb, hsplit⟩ := h
  unfold Region.legal at ha hb
  omega

/-- Build a Region.Subset from a goal that `h` that can be closed by `omega`. -/
theorem Region.Separate.of_omega {a b : Region}
    (h : a.base.toNat + a.len ≤ 2^64 ∧
    b.base.toNat + b.len ≤ 2^64 ∧
    (a.base.toNat + a.len ≤ b.base.toNat ∨ a.base.toNat ≥ b.base.toNat + b.len)) :
    a ⟂ b :=  by
  constructor
  · unfold Region.legal; omega
  · unfold Region.legal; omega
  · omega

theorem BitVec.not_le_eq_lt {a b : BitVec w₁} : (¬ (a ≤ b)) ↔ b < a := by
  rw [BitVec.le_def, BitVec.lt_def]
  omega

/-#
This is a theorem we ought to prove, which establishes the equivalence
between the old and new defintions of 'Region.separate.
However, the proof is finicky, and so we leave it commented for now.
-/
/-
theorem mem_separate_of_Region.separate (h : Region.separate a an b bn)
    (ha' : a' = a + (BitVec.ofNat w₁ (an - 1) ) (hb' : b' = b + (BitVec.ofNat w₁ (bn - 1)))
    (hlegala : mem_legal a an) (hlegalb: mem_legal b bn) :
    mem_separate a a' b b' := by
  simp [mem_separate]
  simp [mem_overlap]
  obtain ⟨ha, hb, hsep⟩ := h
  simp [Region.legal] at ha hb
  subst ha'
  subst hb'
  apply Classical.byContradiction
  intro hcontra
  · sorry
  · sorry
-/

/-- `Region.Subset a b` witnesses that `[a..a+an)` is a subset of `[b..b+bn)`.
In prose, we may notate this as `[a..an) ≤ [b..bn)`.
-/
structure Region.Subset (a b : Region) : Prop where
  ha : a.legal
  hb : b.legal
  hstart : b.base.toNat ≤ a.base.toNat
  hend : a.base.toNat + a.len ≤ b.base.toNat + b.len

scoped notation (name := subset) a " ⊆ " b  => (Region.Subset a b)

/--
Unfold the definition of `Region.Subset` to write definitions that `omega` can process.
-/
theorem Region.Subset.omega_def {a b : Region} (h : a ⊆ b) :
  a.base.toNat + a.len ≤ 2^64 ∧
  b.base.toNat + b.len ≤ 2^64 ∧
  b.base.toNat ≤ a.base.toNat ∧
  a.base.toNat + a.len ≤ b.base.toNat + b.len := by
  obtain ⟨ha, hb, hstart, hend⟩ := h
  unfold Region.legal at ha hb
  omega

/-- Build a Region.Subset from a goal that `h` that can be closed by `omega`. -/
theorem Region.Subset.of_omega {a b : Region}
  (h : a.base.toNat + a.len ≤ 2^64 ∧
  b.base.toNat + b.len ≤ 2^64 ∧
  b.base.toNat ≤ a.base.toNat ∧
  a.base.toNat + a.len ≤ b.base.toNat + b.len) : Region.Subset a b :=  by
constructor
· unfold Region.legal; omega
· unfold Region.legal; omega
· omega
· omega

theorem Region.Subset_refl {a : Region} (h : a.legal) : Region.Subset a a where
  ha := h
  hb := h
  hstart := by simp only [BitVec.le_def, Nat.le_refl]
  hend := by simp only [Nat.le_refl]

/--
If `[a'..a'+an')` begins at least where `[a..an)` begins,
and ends before `[a..an)` ends, and if `[a..an)` is a subset of `[b..bn)`,
then `[a'..a'+an')` is a subset of `[b..bn)`.
-/
theorem Region.Subset_of_le_of_le {a b a' : Region} (h : a ⊆ b)
  (ha' : a.base.toNat ≤ a'.base.toNat) (han' : a'.base.toNat + a'.len ≤ a.base.toNat + a.len) :
  Region.Subset a' b where
  ha := by
    obtain ⟨ha, hb, _, hend⟩ := h
    simp only [Region.legal, Nat.reducePow] at ha hb ⊢
    omega
  hb := h.hb
  hstart := by
    obtain ⟨ha, hb, hstart, _⟩ := h
    simp only [Region.legal, Nat.reducePow] at ha hb
    omega
  hend := by
    obtain ⟨ha, hb, _, hend⟩ := h
    simp only [Region.legal, Nat.reducePow] at ha hb
    omega

/-- if `[a..an) ≤ [b..bn)` and `[b..bn) ⟂ [c..cn)`,
then `[a..an) ⟂ [c..cn)`.
(Recall that `⟂` stands for `Region.separate`.)
-/
theorem Region.separate_of_Region.separate_of_Region.Subset
    (hsep : Region.Separate b c)
    (hsub : Region.Subset a b) :
    Separate a c := by
  obtain ⟨_, hsep₂, hsep₃⟩ := hsep
  obtain ⟨hsub₁, _, hsub₃, hsub₄⟩ := hsub
  constructor <;>
    solve
    | omega
    | assumption

-- `Region.Subset` implies `mem_subset`.
theorem mem_subset_of_Region.Subset (h : Region.Subset a b) (han : a.len > 0) (hbn : b.len > 0) :
  mem_subset a.base (a.base + BitVec.ofNat 64 (a.len - 1)) b.base (b.base + BitVec.ofNat 64 (b.len - 1)):= by
  unfold mem_subset
  obtain ⟨ha, hb, hstart, hend⟩ := h
  unfold Region.legal at ha hb
  simp only [bitvec_rules, minimal_theory]
  by_cases hb : b.len = 2^64
  · left
    bv_omega
  · bv_omega

/- value of read_mem_bytes when separate from the write. -/
theorem read_bytes_write_bytes_eq_read_bytes_of_Region.separate {x y : Region}
    (hsep : x ⟂ y) -- separation
    (val : BitVec (y.len * 8)) :
    Memory.read_bytes x.len x.base (Memory.write_bytes y.len y.base val mem) =
    Memory.read_bytes x.len x.base mem := by
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain := hsep.omega_def
  rw [Memory.getLsb_read_bytes (by omega),
     Memory.getLsb_write_bytes (by omega),
     Memory.getLsb_read_bytes (by omega)]
  simp only [i.isLt]
  simp only [decide_True, ite_eq_left_iff, Bool.true_and]
  intros h₁
  intros h₂
  bv_omega

/- value of `read_mem_bytes'` when subset of the write. -/
theorem read_bytes_write_bytes_eq_of_Region.Subset
    (hsep : x ⊆ y) -- subset relation.
    (val : BitVec (y.len * 8)) :
    Memory.read_bytes x.len x.base (Memory.write_bytes y.len y.base val mem) =
      val.extractLsBytes (x.base.toNat - y.base.toNat) x.len := by
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain ⟨hx, hy, hstart, hend⟩ := hsep

  obtain hx' := hx.size_le_two_pow
  obtain hy' := Region.legal_def hy

  rw [Memory.getLsb_read_bytes (by omega)]
  rw [Memory.getLsb_write_bytes (by omega)]
  rw [BitVec.getLsb_extractLsByte]
  rw [BitVec.getLsb_extractLsBytes]
  by_cases hxn : x.len = 0
  · simp_all [hxn]
  · by_cases h₁ : ↑i < x.len * 8
    · simp only [h₁]
      simp only [decide_True, Bool.true_and]
      obtain ⟨i, hi⟩ := i
      simp only at h₁
      simp only []
      have h₁' : (BitVec.ofNat 64 (i / 8)).toNat = (i / 8) := by
        apply BitVec.toNat_ofNat_lt
        omega
      have hadd : (x.base + BitVec.ofNat 64 (↑i / 8)).toNat = x.base.toNat + (i / 8) := by
        rw [BitVec.toNat_add_eq_toNat_add_toNat (by omega)]
        rw [BitVec.toNat_ofNat_lt (by omega)]
      simp only [BitVec.lt_def]
      simp only [hadd]
      by_cases h₂ : (x.base.toNat + i/ 8) < y.base.toNat
      · -- contradiction
        exfalso
        omega
      · simp only [h₂, if_false]
        by_cases h₃ : x.base.toNat + i / 8 ≥ y.base.toNat + y.len
        · omega
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
          omega
    · simp only [h₁, bitvec_rules, minimal_theory]

/- value of read_mem_bytes when subset of another *read*. -/
theorem read_bytes_eq_extractLsBytes_sub_of_Region.Subset {a b : Region}
    {mem : Memory}
    {val : BitVec (b.len * 8)}
    (hread : mem.read_bytes b.len b.base = val)
    (hsubset : a ⊆ b) :
    mem.read_bytes a.len a.base =
      val.extractLsBytes (a.base.toNat - b.base.toNat) a.len := by
    have ⟨h1, h2, h3, h4⟩ := hsubset.omega_def
    apply BitVec.eq_of_extractLsByte_eq
    intros i
    rw [extractLsByte_read_bytes (by bv_omega)]
    rw [BitVec.extractLsByte_extractLsBytes]
    by_cases h : i < a.len
    · simp only [h, ↓reduceIte]
      apply BitVec.eq_of_getLsb_eq
      intros j
      rw [← hread]
      rw [extractLsByte_read_bytes (by bv_omega)]
      simp only [show a.base.toNat - b.base.toNat + i < b.len by bv_omega, if_true]
      congr 2
      bv_omega
    · simp only [h, ↓reduceIte]

end Memory

end NewDefinitions
