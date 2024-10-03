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

/--
`mem_legal' a n` witnessses that `(a + n)` does not overflow, and thus `[a..a+n)` is a valid range
of memory. Note that the interval is left closed, right open, and thus `n` is the number of bytes in the memory range.
-/
def mem_legal' (a : BitVec 64) (n : Nat) : Prop :=
  a.toNat + n ≤ 2^64

/-- Build a `mem_legal'` from a proof obligation that can be closed by `omega`. -/
def mem_legal'.of_omega (h : a.toNat + n ≤ 2^64) : mem_legal' a n := h

theorem mem_legal'.omega_def (h : mem_legal' a n) : a.toNat + n ≤ 2^64 := h

/-- The linear constraint is equivalent to `mem_legal'`. -/
theorem mem_legal'.iff_omega (a : BitVec 64) (n : Nat) :
    (a.toNat + n ≤ 2^64) ↔ mem_legal' a n := by
  constructor
  · intros h
    apply mem_legal'.of_omega h
  · intros h
    apply h.omega_def

@[bv_toNat]
theorem mem_legal'.iff_omega' (a : BitVec 64) (n : Nat) :
    mem_legal' a n ↔ (a.toNat + n ≤ 2^64) := mem_legal'.iff_omega a n |>.symm

instance : Decidable (mem_legal' a n) :=
  if h : a.toNat + n ≤ 2^64 then
    isTrue (mem_legal'.of_omega h)
  else
    isFalse (fun h' => h h')

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
Legal in the new sense implies legal in the old sense.
-/
theorem mem_legal_of_mem_legal' (h : mem_legal' a n) :
    mem_legal a (a + (BitVec.ofNat 64 (n - 1))) := by
  simp only [mem_legal', mem_legal, BitVec.le_def] at h ⊢
  rw [BitVec.toNat_add_eq_toNat_add_toNat]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.le_add_right, decide_True]
  bv_omega

/--
Legal in the new sense implies legal in the old sense.
Note that the subtraction could also have been written as `(b - a).toNat + 1`
-/
theorem mem_legal'_of_mem_legal (h: mem_legal a b) : mem_legal' a (b.toNat - a.toNat + 1) := by
  simp only [mem_legal, decide_eq_true_eq] at h
  rw [mem_legal']
  bv_omega

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
    bv_omega

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
    (a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn)) :
    mem_separate' a an b bn :=  by
  constructor
  · unfold mem_legal'; omega
  · unfold mem_legal'; omega
  · omega

/-- The linear constraint is equivalent to `mem_separate'`. -/
theorem mem_separate'.iff_omega (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) :
    (a.toNat + an ≤ 2^64 ∧
    b.toNat + bn ≤ 2^64 ∧
    (a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn)) ↔ mem_separate' a an b bn := by
  constructor
  · intros h
    apply mem_separate'.of_omega h
  · intros h
    apply h.omega_def

@[bv_toNat]
  theorem mem_separate'.iff_omega' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) :
    mem_separate' a an b bn ↔ (a.toNat + an ≤ 2^64 ∧ b.toNat + bn ≤ 2^64 ∧ (a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn)) := mem_separate'.iff_omega a an b bn |>.symm

instance : Decidable (mem_separate' a an b bn) :=
  if h : (a.toNat + an ≤ 2^64 ∧ b.toNat + bn ≤ 2^64 ∧ (a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn)) then
    isTrue (mem_separate'.of_omega h)
  else
    isFalse (fun h' => h ⟨h'.ha.omega_def, h'.hb.omega_def, h'.h⟩)

theorem BitVec.not_le_eq_lt {a b : BitVec w₁} : (¬ (a ≤ b)) ↔ b < a := by
  rw [BitVec.le_def, BitVec.lt_def]
  omega

theorem mem_separate'_comm (h : mem_separate' a an b bn) :
    mem_separate' b bn a an := by
  have := h.omega_def
  apply mem_separate'.of_omega
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

/-- The linear constraint is equivalent to `mem_subset'`. -/
theorem mem_subset'.iff_omega (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) :
    (a.toNat + an ≤ 2^64 ∧
    b.toNat + bn ≤ 2^64 ∧
    b.toNat ≤ a.toNat ∧
    a.toNat + an ≤ b.toNat + bn) ↔ mem_subset' a an b bn := by
  constructor
  · intros h
    apply mem_subset'.of_omega h
  · intros h
    apply h.omega_def

@[bv_toNat]
theorem mem_subset'.iff_omega' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) :
    mem_subset' a an b bn ↔ (a.toNat + an ≤ 2^64 ∧ b.toNat + bn ≤ 2^64 ∧ b.toNat ≤ a.toNat ∧ a.toNat + an ≤ b.toNat + bn) := mem_subset'.iff_omega a an b bn |>.symm

instance : Decidable (mem_subset' a an b bn) :=
  if h : (a.toNat + an ≤ 2^64 ∧ b.toNat + bn ≤ 2^64 ∧ b.toNat ≤ a.toNat ∧ a.toNat + an ≤ b.toNat + bn) then
    isTrue (mem_subset'.of_omega h)
  else
    isFalse (fun h' => h ⟨h'.ha.omega_def, h'.hb.omega_def, h'.hstart, h'.hend⟩)

theorem mem_subset'_refl (h : mem_legal' a an) : mem_subset' a an a an where
  ha := h
  hb := h
  hstart := by simp only [BitVec.le_def, Nat.le_refl]
  hend := by simp only [Nat.le_refl]

theorem mem_separate'.symm (h : mem_separate' addr₁ n₁ addr₂ n₂) : mem_separate' addr₂ n₂ addr₁ n₁ := by
  have := h.omega_def
  apply mem_separate'.of_omega
  bv_omega

theorem mem_separate'.of_subset'_of_subset'
  (h : mem_separate' addr₁ n₁ addr₂ n₂)
  (h₁ : mem_subset' addr₁' n₁' addr₁ n₁)
  (h₂ : mem_subset' addr₂' n₂' addr₂ n₂) :
  mem_separate' addr₁' n₁' addr₂' n₂' := by
  have := h.omega_def
  have := h₁.omega_def
  have := h₂.omega_def
  apply mem_separate'.of_omega
  bv_omega

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

-- `mem_subset'` implies `mem_subset`.
theorem mem_subset_of_mem_subset' (h : mem_subset' a an b bn) (han : an > 0) (hbn : bn > 0) :
  mem_subset a (a + BitVec.ofNat 64 (an - 1)) b (b + BitVec.ofNat 64 (bn - 1)):= by
  unfold mem_subset
  obtain ⟨ha, hb, hstart, hend⟩ := h
  unfold mem_legal' at ha hb
  simp only [bitvec_rules, minimal_theory]
  by_cases hb : bn = 2^64
  · left
    bv_omega
  · bv_omega

/- value of read_mem_bytes when separate from the write. -/
theorem Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'
    (hsep : mem_separate' x xn y yn) -- separation
    (val : BitVec (yn * 8)) :
    Memory.read_bytes xn x (Memory.write_bytes yn y val mem) =
    Memory.read_bytes xn x mem := by
  apply BitVec.eq_of_getLsbD_eq
  intros i
  obtain := hsep.omega_def
  rw [Memory.getLsbD_read_bytes (by omega),
     Memory.getLsbD_write_bytes (by omega),
     Memory.getLsbD_read_bytes (by omega)]
  simp only [i.isLt]
  simp only [decide_True, ite_eq_left_iff, Bool.true_and]
  intros h₁
  intros h₂
  bv_omega

/- value of `read_mem_bytes'` when subset of the write. -/
theorem Memory.read_bytes_write_bytes_eq_of_mem_subset'
    (hsep : mem_subset' x xn y yn) -- subset relation.
    (val : BitVec (yn * 8)) :
    Memory.read_bytes xn x (Memory.write_bytes yn y val mem) =
      val.extractLsBytes (x.toNat - y.toNat) xn := by
  apply BitVec.eq_of_getLsbD_eq
  intros i
  obtain ⟨hx, hy, hstart, hend⟩ := hsep

  obtain hx' := hx.size_le_two_pow
  obtain hy' := mem_legal'_def hy

  rw [Memory.getLsbD_read_bytes (by omega)]
  rw [Memory.getLsbD_write_bytes (by omega)]
  rw [BitVec.getLsbD_extractLsByte]
  rw [BitVec.getLsbD_extractLsBytes]
  by_cases hxn : xn = 0
  · subst hxn
    exfalso
    have h := i.isLt
    simp only [Nat.reduceMul, Nat.zero_mul, Nat.not_lt_zero] at h
  · by_cases h₁ : ↑i < xn * 8
    · simp only [h₁]
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
          -- ⊢ val.getLsbD ((x + BitVec.ofNat 64 (i / 8) - y).toNat * 8 + i % 8) = val.getLsbD ((y.toNat - x.toNat) * 8 + i)
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

/- value of read_mem_bytes when subset of another *read*. -/
theorem Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
    {mem : Memory}
    (hread : mem.read_bytes bn b = val)
    (hsubset : mem_subset' a an b bn) :
    mem.read_bytes an a = val.extractLsBytes (a.toNat - b.toNat) an := by
    have ⟨h1, h2, h3, h4⟩ := hsubset.omega_def
    apply BitVec.eq_of_extractLsByte_eq
    intros i
    rw [extractLsByte_read_bytes (by bv_omega)]
    rw [BitVec.extractLsByte_extractLsBytes]
    by_cases h : i < an
    · simp only [h, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq
      intros j
      rw [← hread]
      rw [extractLsByte_read_bytes (by bv_omega)]
      simp only [show a.toNat - b.toNat + i < bn by bv_omega, if_true]
      congr 2
      bv_omega
    · simp only [h, ↓reduceIte]

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
def Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem
  (h : Memory.Region.pairwiseSeparate mems)
  (i j : Nat)
  (hij : i ≠ j)
  (a b : Memory.Region)
  (ha : mems.get? i = some a) (hb : mems.get? j = some b) :
    mem_separate' a.fst a.snd b.fst b.snd := by
  induction h generalizing a b i j
  case nil => simp only [List.get?_eq_getElem?, List.getElem?_nil, reduceCtorEq] at ha
  case cons x xs ihx _ihxs ihxs' =>
    simp only [List.get?_eq_getElem?] at ha hb
    rcases i with rfl | i'
    · simp at ha
      · rcases j with rfl | j'
        · simp only [ne_eq, not_true_eq_false] at hij
        · subst ha
          simp only [List.getElem?_cons_succ] at hb
          apply ihx
          exact List.getElem?_mem hb
    · rcases j with rfl | j'
      · simp only [List.length_cons, Nat.zero_lt_succ, List.getElem?_eq_getElem,
        List.getElem_cons_zero, Option.some.injEq] at hb
        · subst hb
          simp only [List.getElem?_cons_succ] at ha
          apply mem_separate'_comm
          apply ihx
          exact List.getElem?_mem ha
      · simp only [List.getElem?_cons_succ] at ha hb
        apply ihxs' i' j'
        · omega
        · simp only [List.get?_eq_getElem?, ha]
        · simp only [List.get?_eq_getElem?, hb]

end NewDefinitions
