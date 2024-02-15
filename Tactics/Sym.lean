/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.MemoryProofs

-- sym1 tactic symbolically simulates a single instruction.
syntax "sym1" "[" term "]" : tactic
macro_rules
  | `(tactic| sym1 [$h_program:term]) =>
    `(tactic|
      (try simp_all (config := {decide := true, ground := true})); 
      unfold run; 
      simp_all [stepi];
      (try rw [fetch_inst_from_rbmap_program $h_program]);
      (try simp (config := {decide := true, ground := true}) only);
      -- After exec_inst is opened up, the exec functions of the
      -- instructions which are tagged with simp will also open up
      -- here.
      simp [exec_inst];
      -- (try simp_all (config := {decide := true, ground := true}) only);
      -- (try simp only [ne_eq, r_of_w_different, r_of_w_same, w_of_w_shadow, w_irrelevant])
      (try simp_all (config := {decide := true, ground := true})))
