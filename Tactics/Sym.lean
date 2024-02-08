/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.MemoryProofs

open Std.BitVec

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


theorem run_onestep (s s': ArmState) (n: ℕ) (h_nonneg: 0 < n):
  (s' = run n s) ↔ ∃ s'', s'' = stepi s ∧ s' = run (n-1) s'' := by
  cases n
  · cases h_nonneg
  · rename_i n
    simp [run]

/--
  An ongoing new version of fine-grained simulation tactics.
--/

macro "init_next_step" h_s:ident : tactic =>
  `(tactic|
    (rw [run_onestep] at $h_s:ident <;> try omega
     cases $h_s:ident
     rename_i h_temp
     cases h_temp
     rename_i h_s'
     simp at h_s'))

macro "fetch_and_decode_inst" h_step:ident h_s_ok:ident h_pc:ident h_program:ident : tactic =>
  `(tactic|
    (unfold stepi at $h_step:ident
     rw [$h_s_ok:ident] at $h_step:ident
     dsimp only at $h_step:ident -- reduce let(zeta) and match
     unfold read_pc at $h_step:ident
     rw [$h_pc:ident] at $h_step:ident
     rw [fetch_inst_from_rbmap_program $h_program:ident] at $h_step:ident
     simp (config := {ground := true}) at $h_step:ident
    ))

macro "exec_inst" h_step:ident h_sp_aligned:ident st_next:ident: tactic =>
  `(tactic|
    (unfold exec_inst at $h_step:ident
     simp at $h_step:ident
     conv at $h_step:ident =>
       arg 2
       apply if_true
       apply $st_next:ident
     simp [$h_sp_aligned:ident] at $h_step:ident
    ))

-- This tactic is WIP.
macro "update_invariants" st_next:ident h_s_ok_new:ident h_pc_new:ident
                          h_sp_aligned_new:ident h_step:ident : tactic =>
  `(tactic|
    (have ($h_s_ok_new:ident): read_err $st_next:ident = StateError.None := by
      rw [$h_step:ident]; simp_all
     -- Q: How can we automatically infer the next PC?
     have ($h_pc_new:ident): r StateField.PC st_next = 1205444#64 := by
      rw [$h_step:ident,h_s0_pc]; simp; simp (config := {ground := true})
     -- TODO: how to do this?
     have ($h_sp_aligned_new:ident): CheckSPAlignment $st_next:ident = true := sorry
     clear $h_step:ident
    ))
