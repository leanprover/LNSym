/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

The goal is to eliminate the sorry, and to simplify the proof to a tactic invocation.
-/
import Arm
import Arm.Memory.MemoryProofs

theorem mem_automation_test
  (h_n0 : n0 ≠ 0)
  (h_no_wrap_src_region : mem_legal src_addr (src_addr  + ((n0 <<< 4) - 1)))
  (h_no_wrap_dest_region : mem_legal dest_addr (dest_addr  + ((n0 <<< 4) - 1)))
  (h_s0_src_dest_separate :
    mem_separate src_addr  (src_addr  + ((n0 <<< 4) - 1))
                 dest_addr (dest_addr + ((n0 <<< 4) - 1))) :
  read_mem_bytes 16 src_addr (write_mem_bytes 16 dest_addr blah s0) =
  read_mem_bytes 16 src_addr s0 := by
  rw [read_mem_bytes_of_write_mem_bytes_different (by decide) (by decide)]
  rwa [@mem_separate_for_subset_general
            src_addr (src_addr + (n0 <<< 4 - 1))
            dest_addr (dest_addr + (n0 <<< 4 - 1))
            src_addr (src_addr + 15#64)
            dest_addr (dest_addr + 15#64)]
  repeat sorry

/-- info: 'mem_automation_test' depends on axioms: [propext, sorryAx, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in #print axioms mem_automation_test
