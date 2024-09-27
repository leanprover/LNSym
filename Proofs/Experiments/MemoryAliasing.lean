/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

The goal is to eliminate the sorry, and to simplify the proof to a tactic invocation.
-/
import Arm
import Arm.Memory.MemoryProofs
import Arm.BitVec
import Arm.Memory.SeparateAutomation

-- /-- error: unknown constant 'mem_automation_test_2' -/
-- #guard_msgs in #print axioms mem_automation_test_2

set_option trace.simp_mem.info true
-- set_option trace.Tactic.address_normalization true

namespace MemLegal

/-- Show reflexivity of legality. -/
theorem legal_1 (l : mem_legal' a 16) : mem_legal' a 16 := by
  mem_decide_bv

/--
info: 'MemLegal.legal_1' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms legal_1

end MemLegal

namespace MemSubset
/-- Reflexivity. -/
theorem subset_1 (l : mem_subset' a 16 b 16) : mem_subset' a 16 b 16 := by
  mem_decide_bv

/--
info: 'MemSubset.subset_1' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms subset_1

/-- Show that smaller subsets are also subsets. -/
theorem subset_2 (l : mem_subset' a 16 b 16) : mem_subset' a 10 b 16 := by
  mem_decide_bv

/--
info: 'MemSubset.subset_2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms subset_2

/-- Show that smaller subsets are also subsets, even when moving base pointer. -/
theorem subset_3 (l : mem_subset' a 16 b 16) : mem_subset' (a+6) 10 b 16 := by
  mem_decide_bv

/--
info: 'MemSubset.subset_3' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms subset_3

/-- Show that we can perform address arithmetic based on subset constraints. -/
theorem subset_4 (l : mem_subset' a 16 b 16) : a = b := by
  mem_decide_bv

/-- Show that we can perform address arithmetic based on subset constraints.
Only two configurations possible:

..  a0 a1 a2
b0 b1 b2 b3

a0 a1 a2 ..
b0 b1 b2 b3
-/
theorem subset_5 (l : mem_subset' a 3 b 4) : a ≤ b + 1 := by
  mem_decide_bv

end MemSubset

namespace MemSeparate

/-- Reflexivity. -/
theorem separate_1 (l : mem_separate' a 16 b 16) : mem_separate' a 16 b 16 := by
  mem_decide_bv

/--
info: 'MemSeparate.separate_1' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms separate_1


/-- Symmetry. -/
theorem separate_2 (l : mem_separate' a 16 b 16) : mem_separate' b 16 a 16 := by
  mem_decide_bv

/--
info: 'MemSeparate.separate_2' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms separate_2

/-- Smaller subsets. -/
theorem separate_3 (l : mem_separate' a 16 b 16) : mem_separate' b 10 a 10 := by
  mem_decide_bv

/--
info: 'MemSeparate.separate_3' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms separate_3

/-- sliding subset to the right. -/
theorem separate_4 (l : mem_separate' a 16 b 16) (hab : a < b) :
    mem_separate' a 17 (b+1) 15 := by
  mem_decide_bv

/--
info: 'MemSeparate.separate_4' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms separate_4

-- TODO(@bollu): add an assumption in `mem_legal'` that `n ≤ 2^64`.
-- This will allow us to write arithmetic expressions like `n <<< 4`,
-- and have these be simplified into `(BitVec.ofNat 64 n) <<< 4`, which is something
-- that `bv_omega` can understand?
/-- shifts inside the arithmetic. -/
theorem separate_5 {n : BitVec 64} (hn : n ≠ 0#64)
    (hNoOverflow : n.toNonOverflowing * 16 |>.assert)
    (l : mem_separate' a (n <<< 4) b (n <<< 4))  :
    mem_separate' a 16 b 16 := by
  mem_decide_bv

/--
info: 'MemSeparate.separate_5' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms separate_5

/-- shifts inside the arithmetic. -/
theorem separate_6 {n : BitVec 64} (hn : n ≠ 0)
    (hNoOverflow : n.toNonOverflowing * 16 |>.assert)
    (l : mem_separate' a (n <<< 4) b (n <<< 4))  :
    mem_separate' a (n <<< 3 + 8) b (n <<< 4) := by
  mem_decide_bv

/--
info: 'MemSeparate.separate_6' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms separate_6

#guard_msgs in theorem separate_7 (hm : m ≠ 0)
    (l : mem_separate' a 100 b m)
    (l : mem_separate' (a+100) 100 b m)  :
    mem_separate' a 200 b m := by
  mem_decide_bv -- same problem, it gives a crazy model where `m = 0`.

#guard_msgs in theorem separate_8 (hn : n ≠ 0) (hm : m ≠ 0)
    (l : mem_separate' a n b m)
    (l : mem_separate' (a+n) n b m)  :
    mem_separate' a (2*n) b m := by
  mem_decide_bv

/--
Check that we can close address relationship goals that require
us to exploit memory separateness properties.
-/
theorem mem_separate_9  (h : mem_separate' a 100 b 100)
  (hab : a < b) : a + 50 ≤ b := by
  mem_decide_bv

/--
info: 'MemSeparate.mem_separate_9' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms mem_separate_9

end MemSeparate

theorem mem_automation_test_1
  (h_s0_src_dest_separate : mem_separate' src_addr  16 dest_addr 16) :
  read_mem_bytes 16 src_addr (write_mem_bytes 16 dest_addr blah s0) =
  read_mem_bytes 16 src_addr s0 := by
  simp only [memory_rules]
  simp_mem
  rfl

/--
info: 'mem_automation_test_1' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate',
 Quot.sound]
-/
#guard_msgs in #print axioms mem_automation_test_1

set_option trace.simp_mem.info true in
theorem mem_automation_test_2 (n0 : BitVec 64)
  (hNoOverflow : n0.toNonOverflowing * 16 |>.assert)
  (h_n0 : n0 ≠ 0)
  (h_no_wrap_src_region : mem_legal' src_addr (n0 <<< 4))
  (h_no_wrap_dest_region : mem_legal' dest_addr (n0 <<< 4))
  (h_s0_src_dest_separate :
    mem_separate' src_addr  (n0 <<< 4)
                  dest_addr (n0 <<< 4)) :
  read_mem_bytes 16 src_addr (write_mem_bytes 16 dest_addr blah s0) =
  read_mem_bytes 16 src_addr s0 := by
  simp only [memory_rules]
  simp_mem
  rfl

-- /-- error: unknown constant 'mem_automation_test_2' -/
-- #guard_msgs in #print axioms mem_automation_test_2

set_option trace.simp_mem.info true in
/-- reading from a region `[src_addr+1..10] ⊆ [src_addr..16]` with an
interleaved write `[ignore_addr..ignore_addr+ignore_n)`
-/
theorem mem_automation_test_3 (h_ignore_n : ignore_n ≠ 0)
  (h_no_wrap_src_region : mem_legal' src_addr 16)
  (h_s0_src_ignore_disjoint :
    mem_separate' src_addr  16
                  ignore_addr ignore_n) :
  read_mem_bytes 10 (src_addr + 1) (write_mem_bytes ignore_n.toNat ignore_addr blah s0) =
   read_mem_bytes 10 (src_addr + 1) s0 := by
  simp only [memory_rules]
  simp_mem
  rfl


/--
info: 'mem_automation_test_3' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate',
 Quot.sound]
-/
#guard_msgs in #print axioms mem_automation_test_3

set_option trace.simp_mem.info true in
theorem mem_automation_test_4 (ignore_addr ignore_n : BitVec 64)
  (blah : BitVec (ignore_n.toNat * 8))
  (h_no_wrap_src_region : mem_legal' src_addr 48)
  (h_s0_src_ignore_disjoint :
    mem_separate' src_addr  48
                  ignore_addr ignore_n) :
  read_mem_bytes 10 (1 + src_addr)
    -- | this is complicated, because we need to match on
    (write_mem_bytes (ignore_n.toNat) ignore_addr blah
      (write_mem_bytes 48 src_addr val s0)) =
   val.extractLsBytes 1 10 := by
  simp only [memory_rules]
  simp_mem
  congr
  bv_omega

/--
info: 'mem_automation_test_4' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_write_bytes_eq_of_mem_subset',
 Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate',
 Quot.sound]
-/
#guard_msgs in #print axioms mem_automation_test_4


namespace ReadOverlappingRead

/-- A read overlapping with another read. -/
theorem overlapping_read_test_1 {out : BitVec (16 * 8)}
    (hlegal : mem_legal' src_addr 16)
    (h : read_mem_bytes 16 src_addr s = out) :
    read_mem_bytes 16 src_addr s = out := by
  simp only [memory_rules] at h ⊢
  simp_mem
  simp [bitvec_rules, minimal_theory]

/--
info: 'ReadOverlappingRead.overlapping_read_test_1' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset',
 Quot.sound]
-/
#guard_msgs in #print axioms overlapping_read_test_1

/-- A read overlapping with another read. -/
theorem overlapping_read_test_2 {out : BitVec (16 * 8)}
    (hlegal : mem_legal' src_addr 16)
    (h : read_mem_bytes 16 src_addr s = out) :
    read_mem_bytes 10 (src_addr + 6) s = out.extractLsBytes 6 10 := by
  simp only [memory_rules] at h ⊢
  simp_mem
  · congr
    -- ⊢ (src_addr + 6).toNat - src_addr.toNat = 6
    bv_omega

/--
info: 'ReadOverlappingRead.overlapping_read_test_2' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset',
 Quot.sound]
-/
#guard_msgs in #print axioms overlapping_read_test_2

/-- A read in the goal state overlaps with a read in the
left hand side of the hypotheis `h`.
-/
theorem overlapping_read_test_3
    (hlegal : mem_legal' src_addr 16)
    (h : read_mem_bytes 16 src_addr s = read_mem_bytes 16 other_addr s) :
    read_mem_bytes 10 (src_addr + 6) s =
    -- @bollu: unfortunate, this needs `s.mem` to be public. Annoying.
      (Memory.read_bytes 16 other_addr s.mem).extractLsBytes 6 10 := by
  simp only [memory_rules] at h ⊢
  simp_mem
  · congr
    -- ⊢ (src_addr + 6).toNat - src_addr.toNat = 6
    bv_omega
/--
info: 'ReadOverlappingRead.overlapping_read_test_3' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset',
 Quot.sound]
-/
#guard_msgs in #print axioms overlapping_read_test_3

example  (src_addr other_addr : BitVec 64) (hlegal : mem_legal' src_addr 16)
  : (src_addr + 6).toNat - src_addr.toNat = 6 := by
    bv_omega


/-
set_option linter.all false in
/-- A read in the goal state overlaps with a read in the
right hand side of the hypotheis `h`.
-/
theorem overlapping_read_test_4
    (hlegal : mem_legal' src_addr 16)
    (h : read_mem_bytes 16 other_addr s = read_mem_bytes 16 src_addr s) :
    read_mem_bytes 10 (src_addr + 6) s =
    -- @bollu: unfortunate, this needs `s.mem` to be public. Annoying.
      (Memory.read_bytes 16 other_addr s.mem).extractLsBytes 6 10 := by
  simp only [memory_rules] at h ⊢
  simp_mem
  -- Why does this proof take forever to check?
  have : ((src_addr + 6).toNat - src_addr.toNat) = 6 := by bv_omega
  rw [this]

/--
info: 'ReadOverlappingRead.overlapping_read_test_4' depends on axioms: [propext, sorryAx, Quot.sound]
-/
#guard_msgs in #print axioms overlapping_read_test_4
-/

end ReadOverlappingRead

namespace ReadOverlappingWrite

theorem test_1 {val : BitVec (16 * 8)}
    (hlegal : mem_legal' src_addr 16) :
    Memory.read_bytes 16 src_addr (Memory.write_bytes 16 src_addr val mem) =
     val.extractLsBytes 0 16  := by
  simp_mem
  · -- ⊢ val.extractLsBytes (src_addr.toNat - src_addr.toNat) 16 = val.extractLsBytes 0 16
    congr
    simp only [Nat.sub_self]

theorem test_2 {val : BitVec _}
    (hlegal : mem_legal' src_addr 16) :
    Memory.read_bytes 6 (src_addr + 10) (Memory.write_bytes 16 src_addr val mem) =
    val.extractLsBytes 10 6 := by
  simp_mem
  have : ((src_addr + 10).toNat - src_addr.toNat) = 10 := by bv_omega
  rw [this]

end ReadOverlappingWrite



-- weird, bv_decide does not decide ground arithmetic?
/-
None of the hypotheses are in the supported BitVec fragment.
There are two potential fixes for this:
1. If you are using custom BitVec constructs simplify them to built-in ones.
2. If your problem is using only built-in ones it might currently be out of reach.
   Consider expressing it in terms of different operations that are better supported.
-/

/- We check that we correctly visit the expression tree, both for binders,
and for general walking. -/
namespace ExprVisitor

set_option trace.simp_mem.info true in
/-- Check that we correctly go under binders -/
theorem test_quantified_1 {val : BitVec (16 * 8)}
    (hlegal : mem_legal' 0 16) : ∀ (_irrelevant : Nat),
    Memory.read_bytes 16 0 (Memory.write_bytes 16 0 val mem) =
     val.extractLsBytes 0 16  := by
  simp_mem
  simp

/--
info: 'ExprVisitor.test_quantified_1' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_write_bytes_eq_of_mem_subset',
 Quot.sound]
-/
#guard_msgs in #print axioms test_quantified_1

/-- Check that we correctly walk under applications. -/
theorem test_app_1 {val : BitVec (16 * 8)}
    (hlegal : mem_legal' 0 16) (f : BitVec _ → Nat) :
    f (Memory.read_bytes 16 0 (Memory.write_bytes 16 0 val mem)) =
    f (val.extractLsBytes 0 16)  := by
  simp_mem
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    Nat.sub_self]

/--
info: 'ExprVisitor.test_app_1' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_write_bytes_eq_of_mem_subset',
 Quot.sound]
-/
#guard_msgs in #print axioms test_app_1

/--
Check that we correctly walk under applications (`f <walk inside>`)
and binders (`∀ f, <walk inside>`) simultaneously.
-/
theorem test_quantified_app_1 {val : BitVec (16 * 8)}
    (hlegal : mem_legal' 0 16) : ∀ (f : BitVec _ → Nat),
    f (Memory.read_bytes 16 0 (Memory.write_bytes 16 0 val mem)) =
    f (val.extractLsBytes 0 16)  := by
  simp_mem
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    Nat.sub_self, implies_true]

/--
info: 'ExprVisitor.test_quantified_app_1' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Memory.read_bytes_write_bytes_eq_of_mem_subset',
 Quot.sound]
-/
#guard_msgs in #print axioms test_quantified_app_1

/--
Check that we correctly simplify the *types* of binders as well.
Here, the bound variable `P` has *type* that involves a memory read.
We make sure that we simplify these as well.
-/
theorem test_quantified_app_2 {val : BitVec (16 * 8)}
    (_hlegal : ∀ (addr : Nat), mem_legal' addr 16)
    (f : _ → Nat) :
    f (∀ (_P : Memory.read_bytes 16 0 (Memory.write_bytes 16 0 val mem) = irrelevant), Nat) =
    f (∀ (_P : val.extractLsBytes 0 16 = irrelevant), Nat) := by
  simp_mem
  rfl

end ExprVisitor

namespace MathProperties

/-
We stress the omega reduction, and indirectly, `omega` itself, by
proving generic properties about our definitions of `mem_legal'`,
`mem_separate'`, `mem_subset'`.
-/

/-! ### mem_subset is a partial order. -/
theorem mem_subset_refl {an : Nat} (h : mem_legal' a an) : mem_subset' a an a an := by mem_decide_bv
/-
TODO(@bollu): In such a scenario, we should call `omega` directly on the goal,
and see if it can solve it.
theorem mem_subset_asymm (h : mem_subset' a an b bn) (h' : mem_subset' b bn a an) :
  a = b ∧ an = bn := by
  simp_mem
-/
theorem mem_subset_trans (h : mem_subset' a an b bn) (h' : mem_subset' b bn c cn) :
  mem_subset' a an c cn := by mem_decide_bv

/-! ### mem_separate relationship to arithmetic -/

theorem mem_separate_comm (h : mem_separate' a an b bn) : mem_separate' b bn a an := by mem_decide_bv

/-- if `[a..an)⟂[b..bn)`, then `[a+δ..an-δ)⟂[b..bn)`-/
theorem mem_separate_of_lt_of_lt_sub (h : mem_separate' a an b bn) (hab : a < b)
  (hδ₁ : an ≥ δ)
  (hδ : δ < b - a): mem_separate' (a + δ) (an - δ) b bn := by
    -- here, we get a subtraction of an `ofNat`, no bueno.
  mem_decide_bv

/-- If `[a..an)⟂[b..bn)`, and `a ≤ b`, then `[a'..an+(a-a'))⟂[b..bn)`.
This lets us increase the size of the left memory region.
-/
theorem mem_separate_move_of_lt_of_le  (h : mem_separate' a an b bn)
  (hab : a < b)
  (hlegal : a' ≤ a) : mem_separate' a' (an + (a - a')) b bn := by
  mem_decide_bv

end MathProperties

section PairwiseSeparate
  /- Check that a direct implication of the pairwise separation is proven. -/
  theorem pairwise_direct (h : Memory.Region.pairwiseSeparate [⟨a, 100⟩, ⟨b, 200⟩, ⟨c, 300⟩, ⟨d, 400⟩]) :
    mem_separate' a 100 b 200 := by
    sorry

  /- Check that a direct implication of the pairwise separation is proven. -/
  theorem pairwise_subset (h : Memory.Region.pairwiseSeparate [⟨a, 100⟩, ⟨b, 200⟩, ⟨c, 300⟩, ⟨d, 400⟩]) :
    mem_separate' a 80 b 100 := by
    sorry

end PairwiseSeparate

namespace MemOptions

set_option trace.simp_mem true in
set_option trace.simp_mem.info true in
/--
error: ❌️ simp_mem failed to make any progress.
---
info: [simp_mem.info] Searching for Hypotheses
[simp_mem.info] Summary: Found 0 hypotheses
[simp_mem.info] ⚙️ Matching on ⊢ False
[simp_mem.info] Performing Rewrite At Main Goal
  [simp_mem.info] Simplifying goal.
[simp_mem.info] ❌️ No progress made in this iteration. halting.
-/
#guard_msgs in theorem test_no_fail_if_unchanged : False := by
  simp_mem
  trace_state

set_option trace.simp_mem true in
set_option trace.simp_mem.info true in
/--
error: ❌️ simp_mem failed to make any progress.
---
info: [simp_mem.info] Searching for Hypotheses
[simp_mem.info] Summary: Found 0 hypotheses
[simp_mem.info] ⚙️ Matching on ⊢ False
[simp_mem.info] Performing Rewrite At Main Goal
  [simp_mem.info] Simplifying goal.
[simp_mem.info] ❌️ No progress made in this iteration. halting.
-/
#guard_msgs in theorem test_fail_if_unchanged : False := by
  simp_mem
  trace_state


end MemOptions
