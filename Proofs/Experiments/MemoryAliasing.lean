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

set_option trace.simp_mem true
set_option trace.simp_mem.info true

namespace MemLegal
/-- Show reflexivity of legality. -/
theorem legal_1 (l : mem_legal' a 16) : mem_legal' a 16 := by
  simp_mem

/-- info: 'MemLegal.legal_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms legal_1

end MemLegal

namespace MemSubset
/-- Reflexivity. -/
theorem subset_1 (l : mem_subset' a 16 b 16) : mem_subset' a 16 b 16 := by
  simp_mem

/-- info: 'MemSubset.subset_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subset_1

/-- Show that smaller subsets are also subsets. -/
theorem subset_2 (l : mem_subset' a 16 b 16) : mem_subset' a 10 b 16 := by
  simp_mem

/-- info: 'MemSubset.subset_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subset_2

/-- Show that smaller subsets are also subsets, even when moving base pointer. -/
theorem subset_3 (l : mem_subset' a 16 b 16) : mem_subset' (a+6) 10 b 16 := by
  simp_mem

/-- info: 'MemSubset.subset_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subset_3

end MemSubset

namespace MemSeparate

/-- Reflexivity. -/
theorem separate_1 (l : mem_separate' a 16 b 16) : mem_separate' a 16 b 16 := by
  simp_mem

/-- info: 'MemSeparate.separate_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separate_1


/-- Symmetry. -/
theorem separate_2 (l : mem_separate' a 16 b 16) : mem_separate' b 16 a 16 := by
  simp_mem

/-- info: 'MemSeparate.separate_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separate_2

/-- Smaller subsets. -/
theorem separate_3 (l : mem_separate' a 16 b 16) : mem_separate' b 10 a 10 := by
  simp_mem

/-- info: 'MemSeparate.separate_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separate_3


/-- sliding subset to the right. -/
theorem separate_4 (l : mem_separate' a 16 b 16) (hab : a < b) :
    mem_separate' a 17 (b+1) 15 := by
  simp_mem

/-- info: 'MemSeparate.separate_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separate_4

/-- shifts inside the arithmetic. -/
theorem separate_5 {n : Nat} (hn : n ≠ 0)
    (l : mem_separate' a (n <<< 4) b (n <<< 4))  :
    mem_separate' a 16 b 16 := by
  simp_mem

/-- info: 'MemSeparate.separate_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separate_5

/-- shifts inside the arithmetic. -/
theorem separate_6 {n : Nat} (hn : n ≠ 0)
    (l : mem_separate' a (n <<< 4) b (n <<< 4))  :
    mem_separate' a (n <<< 3 + 8) b (n <<< 4) := by
  simp_mem

/-- info: 'MemSeparate.separate_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separate_6

end MemSeparate


theorem mem_automation_test_1
  (h_s0_src_dest_separate : mem_separate' src_addr  16 dest_addr 16) :
  read_mem_bytes 16 src_addr (write_mem_bytes 16 dest_addr blah s0) =
  read_mem_bytes 16 src_addr s0 := by
  simp only [memory_rules]
  simp_mem
  rfl

/-- info: 'mem_automation_test_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_automation_test_1

theorem mem_automation_test_2
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


/-- info: 'mem_automation_test_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_automation_test_2


namespace ReadOverlappingRead

/-- A read overlapping with another read. -/
theorem overlapping_read_test_1 {out : BitVec (16 * 8)}
    (hlegal : mem_legal' src_addr 16)
    (h : read_mem_bytes 16 src_addr s = out) :
    read_mem_bytes 16 src_addr s = out := by
  simp only [memory_rules] at h ⊢
  simp_mem
  simp only [Nat.reduceMul, Nat.sub_self, BitVec.extractLsBytes_eq_self]

/--
info: 'ReadOverlappingRead.overlapping_read_test_1' depends on axioms: [propext,
 to_prove_memory_fact,
 Classical.choice,
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
    bv_omega'
/--
info: 'ReadOverlappingRead.overlapping_read_test_2' depends on axioms: [propext,
 to_prove_memory_fact,
 Classical.choice,
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
    bv_omega'
/--
info: 'ReadOverlappingRead.overlapping_read_test_3' depends on axioms: [propext,
 to_prove_memory_fact,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms overlapping_read_test_3

/- TODO(@bollu): This test case hangs at `bv_omega'`. This is to be debugged.
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
  · congr
    -- ⊢ (src_addr + 6).toNat - src_addr.toNat = 6
    bv_omega' -- TODO: Lean gets stuck here?

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
    simp

theorem test_2 {val : BitVec _}
    (hlegal : mem_legal' src_addr 16) :
    Memory.read_bytes 6 (src_addr + 10) (Memory.write_bytes 16 src_addr val mem) =
    val.extractLsBytes 10 6 := by
  simp_mem
  have : ((src_addr + 10).toNat - src_addr.toNat) = 10 := by bv_omega'
  rw [this]

end ReadOverlappingWrite
