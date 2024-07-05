/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.MemoryProofs
import Tactics.FetchAndDecode
import Tactics.ExecInst
import Tactics.ChangeHyps

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
          -- intro_change_hyps $h_step_n':ident $h_st_prefix:str
          -- (try clear $h_step_n':ident)
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
