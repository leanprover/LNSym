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
import Arm.State
import Arm.Memory.Separate
import Std.Tactic.BVDecide


#time example : mem_subset a1 a2 a1 a2 := by unfold mem_subset; bv_decide

#time example (h : mem_legal' a1 n₁) : mem_subset' a1 n₁ a1 n₁:= by simp_mem

#time example (h : mem_subset a1 a2 b1 b2) :
  mem_overlap a1 a2 b1 b2 := by
  revert h
  simp [mem_subset, mem_overlap]
  bv_decide


#time example (h : mem_subset a b c d) :
  mem_subset a a c d := by
  revert h
  simp_all [mem_subset]
  bv_decide

#time example (h : mem_subset' a b c d) : mem_subset' a 0 c d := by simp_mem

#time example (h1 : a ≠ b1)
  (h : mem_subset a a b1 b2) :
  mem_subset a a (b1 + 1#64) b2 := by
  revert h
  simp_all [mem_subset]
  bv_decide

set_option trace.simp_mem.info true in
#time example (h1 : a ≠ b)
  (h : mem_subset' a 1 b n) :
  mem_subset' a 1 (b + 1#64) n := by 
  -- simp_mem
  sorry

-- theorem mem_subset_same_address_different_sizes
--   (h : mem_subset addr (addr + n1) addr (addr + n2)) :
--   n1 <= n2 := by
--   revert h
--   simp [mem_subset]
--   bv_check "lrat_files/SeparateProofs.lean-mem_subset_same_address_different_sizes-107-2.lrat"

#time example : mem_subset a a a (a + n) := by
  simp [mem_subset]
  bv_decide

#time example (hn : n > 0) (hlegal : mem_legal' a n) : mem_subset' a 1 a n := by simp_mem
