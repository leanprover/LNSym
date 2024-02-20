/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

-- TODO: replace this with an upcoming new lemma in Std
theorem Std.BitVec.foldCtor : { toFin := { val := a, isLt := h } : BitVec n } = BitVec.ofNat n a := by
  simp [BitVec.ofNat, Fin.ofNat', h, Nat.mod_eq_of_lt]

-- init_next_step breaks 'h_s: s_next = run n s' into 'run (n-1) s' and one step.
macro "init_next_step" h_s:ident : tactic =>
  `(tactic|
    (rw [run_onestep] at $h_s:ident <;> try omega
     cases $h_s:ident
     rename_i h_temp
     cases h_temp
     rename_i h_s'
     simp at h_s'))

-- Given 'h_step: s_next = stepi s', fetch_and_decode_inst unfolds stepi,
-- simplifies fetch_inst and decode_raw_inst.
macro "fetch_and_decode_inst" h_step:ident h_s_ok:ident h_pc:ident h_program:ident : tactic =>
  `(tactic|
    (unfold stepi at $h_step:ident
     rw [$h_s_ok:ident] at $h_step:ident
     dsimp at $h_step:ident -- reduce let and match
     rw [$h_pc:ident] at $h_step:ident
     rw [fetch_inst_from_rbmap_program $h_program:ident] at $h_step:ident
     -- Note: this often times out. It tries to evaluate, e.g.,
     -- Std.RBMap.find? sha512_program_test_2 1205560#64
     -- which easily becomes hard.
     simp (config := {ground := true}) at $h_step:ident
     repeat (rw [Std.BitVec.foldCtor] at $h_step:ident)
    ))

-- Given hstep which is the result of fetch_and_decode_inst, exec_inst executes
-- an instruction and generates 's_next = w .. (w .. (... s))'.
macro "exec_inst" h_step:ident h_sp_aligned:ident st_next:ident: tactic =>
  `(tactic|
    (unfold exec_inst at $h_step:ident
     -- A simple case where simp works (e.g., Arm.DPI)
     try (simp (config := {ground := true, decide := true}) at $h_step:ident)
     -- A complicated case (e.g., Arm.LDST)
     try (simp at $h_step:ident; (conv at $h_step:ident =>
         arg 2
         apply if_true
         apply $st_next:ident); simp [$h_sp_aligned:ident] at $h_step:ident)
    ))

-- Given h_step wich is 's_next = w .. (w .. (... s))', it creates assumptions
-- 'read .. s_next = value'.
-- TODO: update_invariants must add all register and memory updates as
-- assumptions.
macro "update_invariants" st_next:ident progname:ident
                          h_s_ok_new:ident
                          h_pc:ident h_pc_new:ident
                          h_sp_aligned:ident h_sp_aligned_new:ident
                          h_program_new:ident
                          h_step:ident pc_next:term : tactic =>
  `(tactic|
     (have $h_s_ok_new:ident: read_err $st_next:ident = StateError.None := by
        rw [$h_step:ident]; simp_all
      -- Q: How can we automatically infer the next PC?
      have $h_pc_new:ident: r StateField.PC $st_next:ident = $pc_next:term := by
        rw [$h_step:ident,$h_pc:ident]; simp; simp (config := {ground := true})
      have $h_sp_aligned_new:ident: CheckSPAlignment $st_next:ident = true := by
        unfold CheckSPAlignment at *
        rw [$h_step:ident]
        simp
        simp at $h_sp_aligned:ident
        /-
          This sorry will be resovled after lean4 that has improved
          `simp (config := { ground := true })` is used.
          See also:
          https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Simplifying.20a.20bitvector.20constant/near/422077748
          The goal:

          h_s0_sp_aligned: extractLsb 3 0 (r (StateField.GPR 31#5) s0) &&& 15#4 = 0#4
          ⊢ extractLsb 3 0 (r (StateField.GPR 31#5) s0 +
            signExtend 64 126#7 <<< (2 + Std.BitVec.toNat (extractLsb 1 1 2#2))) &&&
              15#4 =
            0#4
        -/
        sorry
      have $h_program_new:ident : ($st_next:ident).program =
              Std.RBMap.find? ($progname:ident) := by
        rw [$h_step:ident]
        try (repeat rw [w_program])
        try (rw [write_mem_bytes_program])
        assumption
    ))

def sym_one (curr_state_number:ℕ) (pc_begin:ℕ) (prog:Lean.Ident):
    Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let n_str := toString curr_state_number
    let n'_str := toString (curr_state_number+1)
    let pcexpr := Lean.mkNatLit (pc_begin + 4 * (curr_state_number + 1))
    let pcbv := ← (Lean.mkApp2 (Lean.mkConst ``Std.BitVec.ofNat) (Lean.mkNatLit 64)
                               pcexpr).toSyntax
    -- Question: how can I convert this pcbv into Syntax?
    let mk_name (s:String): Lean.Name :=
      Lean.Name.append Lean.Name.anonymous s
    -- The name of the next state
    let st' := Lean.mkIdent (mk_name ("s_" ++ n'_str))
    let h_st_ok := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_ok"))
    let h_st'_ok := Lean.mkIdent (mk_name ("h_s" ++ n'_str ++ "_ok"))
    let h_st_pc := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_pc"))
    let h_st'_pc := Lean.mkIdent (mk_name ("h_s" ++ n'_str ++ "_pc"))
    let h_st_program := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_program"))
    let h_st'_program := Lean.mkIdent (mk_name ("h_s" ++ n'_str ++ "_program"))
    let h_st_sp_aligned := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_sp_aligned"))
    let h_st'_sp_aligned := Lean.mkIdent (mk_name ("h_s" ++ n'_str ++ "_sp_aligned"))
    -- Temporary hypotheses
    let h_run := Lean.mkIdent (mk_name "h_run")
    Lean.Elab.Tactic.evalTactic (←
      `(tactic|
         (init_next_step $h_run:ident
          rename_i $st':ident h_step $h_run:ident
          -- Simulate one instruction
          fetch_and_decode_inst h_step $h_st_ok:ident $h_st_pc:ident $h_st_program:ident
          exec_inst h_step $h_st_sp_aligned:ident $st':ident

          -- Update invariants
          update_invariants $st':ident $prog:ident
                            $h_st'_ok:ident
                            $h_st_pc:ident $h_st'_pc:ident
                            $h_st_sp_aligned $h_st'_sp_aligned:ident
                            $h_st'_program h_step $pcbv:term
          clear $h_st_ok:ident $h_st_sp_aligned:ident $h_st_pc:ident h_step
                $h_st_program:ident
         )))

-- sym_n tactic symbolically simulates n instructions.
elab "sym_n" n:num pc:num prog:ident : tactic => do
  for i in List.range n.getNat do
    sym_one i pc.getNat prog

-- sym_n tactic symbolically simulates n instructions from
-- state number i.
elab "sym_i_n" i:num n:num pc:num prog:ident : tactic => do
  for j in List.range n.getNat do
    sym_one (i.getNat + j) pc.getNat prog
