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
/-- Show reflexivity of subset. -/
example (l : mem_subset' a 16 b 16) : mem_subset' a 16 b 16 := by
  simp_mem
  sorry

/-- error: unknown constant 'legal_2' -/
#guard_msgs in #print axioms legal_2

end MemSubset

theorem mem_automation_test_1
  (h_s0_src_dest_separate : mem_separate' src_addr  16 dest_addr 16) :
  read_mem_bytes 16 src_addr (write_mem_bytes 16 dest_addr blah s0) =
  read_mem_bytes 16 src_addr s0 := by
  simp_mem
  sorry

/-- info: 'mem_automation_test_1' depends on axioms: [propext, sorryAx, Quot.sound] -/
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
  sorry

/-- info: 'mem_automation_test_2' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in #print axioms mem_automation_test_2
