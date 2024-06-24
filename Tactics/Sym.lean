/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.MemoryProofs
import Tactics.FetchAndDecode
import Tactics.ExecInst

import Lean.Elab
import Lean.Expr

open BitVec

/- `init_next_step h_run` splits the hypothesis

`h_run: s_final = run n s`

introduces a new state variable, say `s_next` and two new hypotheses:
`h_step: s_next = stepi s`
`h_run': s_final = run (n-1) s_next`

The new state variable and the hypotheses are not named yet.
-/
macro "init_next_step" h_s:ident : tactic =>
  `(tactic|
    (rw [run_onestep] at $h_s:ident <;> try omega
     cases $h_s:ident
     rename_i h_temp
     cases h_temp
     rename_i h_s'
     simp (config := {ground := true}) only at h_s'))

-- Given h_step which is 's_next = w .. (w .. (... s))', it creates assumptions
-- 'read .. s_next = value'.
-- TODO: update_invariants must add all register and memory updates as
-- assumptions.
-- macro "update_invariants" st_next:ident progname:ident
--                           h_s_ok_new:ident
--                           h_pc:ident h_pc_new:ident
--                           h_sp_aligned:ident h_sp_aligned_new:ident
--                           h_program_new:ident
--                           h_step:ident pc_next:term : tactic =>
--   `(tactic|
--      (have $h_s_ok_new:ident : r StateField.ERR $st_next:ident = StateError.None := by
--         rw [$h_step:ident]; simp_all
--       -- Q: How can we automatically infer the next PC?
--       have $h_pc_new:ident : r StateField.PC $st_next:ident = $pc_next:term := by
--         rw [$h_step:ident,$h_pc:ident]; simp; simp (config := {ground := true})
--       have $h_sp_aligned_new:ident : CheckSPAlignment $st_next:ident = true := by
--         unfold CheckSPAlignment at *
--         rw [$h_step:ident]
--         simp
--         simp at $h_sp_aligned:ident
--         /-
--           This sorry will be resovled after lean4 that has improved
--           `simp (config := { ground := true })` is used.
--           See also:
--           https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Simplifying.20a.20bitvector.20constant/near/422077748
--           The goal:

--           h_s0_sp_aligned: extractLsb 3 0 (r (StateField.GPR 31#5) s0) &&& 15#4 = 0#4
--           ⊢ extractLsb 3 0 (r (StateField.GPR 31#5) s0 +
--             signExtend 64 126#7 <<< (2 + BitVec.toNat (extractLsb 1 1 2#2))) &&&
--               15#4 =
--             0#4
--         -/
--         sorry
--       have $h_program_new:ident : ($st_next:ident).program =
--               Map.find? ($progname:ident) := by
--         rw [$h_step:ident]
--         try (repeat rw [w_program])
--         try (rw [write_mem_bytes_program])
--         assumption))

def sym_one (curr_state_number : Nat) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let n_str := toString curr_state_number
    let n'_str := toString (curr_state_number + 1)
    let mk_name (s : String) : Lean.Name :=
      Lean.Name.mkStr Lean.Name.anonymous s
    -- h_st: prefix of user names of hypotheses about state st
    let h_st_prefix := Lean.Syntax.mkStrLit ("h_s" ++ n_str)
    -- h_st_program: name of the hypothesis about the program at state st
    let h_st_program := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_program"))
    let h_st_pc := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_pc"))
    let h_st_err := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_err"))
    -- st': name of the next state
    let st' := Lean.mkIdent (mk_name ("s" ++ n'_str))
    -- h_run: name of the hypothesis with the `run` function
    let h_run := Lean.mkIdent (mk_name "h_run")
    -- h_step_n': name of the hypothesis with the `stepi` function
    let h_step_n' := Lean.mkIdent (mk_name ("h_step_" ++ n'_str))
    Lean.Elab.Tactic.evalTactic (←
      `(tactic|
         (init_next_step $h_run:ident
          rename_i $st':ident $h_step_n':ident $h_run:ident
          -- Simulate one instruction
          fetch_and_decode $h_step_n':ident $h_st_prefix:str
          -- (try clear $h_step_n:ident)
          exec_inst $h_step_n':ident $h_st_prefix:str
          intro_fetch_decode_lemmas $h_step_n':ident $h_st_program:ident $h_st_prefix:str
          (try clear $h_st_pc:ident $h_st_program:ident $h_st_err:ident)
          -- Update invariants
          -- update_invariants $st':ident $prog:ident
          --                   $h_st'_ok:ident
          --                   $h_st_pc:ident $h_st'_pc:ident
          --                   $h_st_sp_aligned $h_st'_sp_aligned:ident
          --                   $h_st'_program $h_step_n':ident $pcbv:term
          -- clear $h_st_ok:ident $h_st_sp_aligned:ident $h_st_pc:ident $h_step_n':ident
          --       $h_st_program:ident
      )))

-- sym_n tactic symbolically simulates n instructions.
elab "sym_n" n:num : tactic => do
  for i in List.range n.getNat do
    sym_one i

-- sym_n tactic symbolically simulates n instructions from
-- state number i.
elab "sym_i_n" i:num n:num : tactic => do
  for j in List.range n.getNat do
    sym_one (i.getNat + j)
