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

namespace MemLegal
/-- Show reflexivity of legality. -/
example (l : mem_legal' a 16) : mem_legal' a 16 := by
  bv_omega'
end MemLegal

namespace MemSubset
/-- Show reflexivity of subset. -/
example (l : mem_subset' a 16 b 16) : mem_subset' a 16 b 16 := by
  sorry
end MemSubset

coinductive Bisim (R : S -> S -> Prop) : Prop
|
|


theorem mem_automation_test (l : mem_legal a 16) : mem_legal a 16 := sorry

set_option trace.simp_mem true in
set_option trace.simp_mem.info true in
theorem mem_automation_test
  (h_s0_src_dest_separate : mem_separate' src_addr  16 dest_addr 16) :
  read_mem_bytes 16 src_addr (write_mem_bytes 16 dest_addr blah s0) =
  read_mem_bytes 16 src_addr s0 := by
  -- ⊢ read_mem_bytes 16 src_addr (write_mem_bytes 16 dest_addr blah s0) = read_mem_bytes 16 src_addr s0
  simp_mem
  -- ⊢ read_mem_bytes 16 src_addr s0 = read_mem_bytes 16 src_addr s0
  rfl

/-- info: 'mem_automation_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_automation_test
