/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Memory.MemoryProofs
import Tactics.FetchAndDecode
import Tactics.ExecInst
import Tactics.ChangeHyps
import Tactics.SymContext

import Lean.Elab
import Lean.Expr

initialize
  Lean.registerTraceClass `Sym

open BitVec
open Lean (FVarId)

/-- `init_next_step h_run` splits the hypothesis

`h_run: s_final = run n s`

introduces a new state variable, say `s_next` and two new hypotheses:
`h_step: s_next = stepi s`
`h_run': s_final = run (n-1) s_next`

The new state variable and the hypotheses are not named yet.
-/
macro "init_next_step" h_run:ident h_step:ident sn:ident : tactic =>
  `(tactic|
    (rw [run_onestep _ _ _ (by omega)] at $h_run:ident
    -- I prefer using let instead of obtain because obtain names
    -- the unsolved goal `case intro`. Then we get `.intro` suffixes
    -- there every time we run this tactic.
     let ⟨$sn:ident, ⟨$h_step:ident, _⟩⟩ := $h_run:ident;
     -- obtain ⟨$sn:ident, ⟨$h_step:ident, $h_run:ident⟩⟩ := $h_run:ident
     clear $h_run:ident; rename_i $h_run:ident
     simp (config := {ground := true}) only at $h_run:ident))

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
    let h_st_sp_aligned := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_sp_aligned"))
    -- st': name of the next state
    let st' := Lean.mkIdent (mk_name ("s" ++ n'_str))
    -- h_run: name of the hypothesis with the `run` function
    let h_run := Lean.mkIdent (mk_name "h_run")
    -- h_step_n': name of the hypothesis with the `stepi` function
    let h_step_n' := Lean.mkIdent (mk_name ("h_step_" ++ n'_str))
    Lean.Elab.Tactic.evalTactic (←
      `(tactic|
         (init_next_step $h_run:ident $h_step_n':ident $st':ident
          -- Simulate one instruction
          fetch_and_decode $h_step_n':ident $h_st_prefix:str
          -- (try clear $h_step_n:ident)
          exec_inst $h_step_n':ident $h_st_prefix:str
          intro_fetch_decode_lemmas $h_step_n':ident $h_st_program:ident $h_st_prefix:str
          (try clear $h_st_pc:ident $h_st_program:ident $h_st_err:ident $h_st_sp_aligned:ident)
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

section stepiTac

open Lean Elab Tactic Expr Meta

def stepiTac (goal : MVarId) (h_step : Name) (hyp_prefix : String)
  : TacticM Bool := goal.withContext do
  -- Find all the FVars in the local context whose name begins with
  -- hyp_prefix.
  let h_step_expr ← getFVarFromUserName h_step
  let lctx ← getLCtx
  let matching_decls := filterDeclsWithPrefix lctx hyp_prefix.toName
  -- logInfo m!"matching_decls: {matching_decls[0]!.userName}"

  -- Simplify `fetch_inst`: note: using `ground := true` here causes
  -- maxRecDepth to be reached. Use reduceMapFind? instead.
  let (ctx, simprocs) ←
    LNSymSimpContext (config := {decide := false, ground := false})
                     (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
                     (decls_to_unfold := #[])
                     (thms := #[])
                     (decls := matching_decls)
                     (simprocs := #[])
  let some goal' ← LNSymSimp goal ctx simprocs (fvarid := h_step_expr.fvarId!) |
                   logInfo m!"[stepiTac] The goal appears to be solved, but this tactic \
                              is not a finishing tactic! Something went wrong?"
                   return false
  replaceMainGoal [goal']
  return true

def stepiTacElab (h_step : Name) (hyp_prefix : String) : TacticM Unit :=
  withMainContext
  (do
    let success ← stepiTac (← getMainGoal) h_step hyp_prefix
    if ! success then
      failure)

elab "stepi_tac" h_step:ident hyp_prefix:str : tactic =>
  stepiTacElab (h_step.getId) (hyp_prefix.getString)

end stepiTac

open Lean.Elab.Tactic (TacticM withMainContext evalTactic) in
def sym1 (c : SymContext) : TacticM SymContext :=
  withMainContext do
    let c' := c.nextState
    -- h_st: prefix of user names of hypotheses about state st
    let h_st_prefix := Lean.Syntax.mkStrLit s!"h_{c.state}"
    -- h_step_n': name of the hypothesis with the `stepi` function
    let h_step_n' := Lean.mkIdent (.str .anonymous s!"h_step_{c'.curr_state_number}")
    let stx ←
      `(tactic|
         (init_next_step $c.h_run_ident:ident $h_step_n':ident $c'.state_ident:ident
          -- Simulate one instruction
          stepi_tac $h_step_n':ident $h_st_prefix:str
          intro_fetch_decode_lemmas $h_step_n':ident $c.h_program_ident:ident $h_st_prefix:str
      ))
    trace[Sym] "Running tactic:\n{stx}"
    evalTactic stx
    return c'


open Lean (Name) in



/-- `sym1_i_n i n h_program` will symbolically evaluate a program for `n` steps,
starting from state `i`, where `h_program` is an assumption of the form:
`s{i}.program = someConcreteProgam`.

The context is assumed to contain hypotheses
```
h_s{i}_err : r StateField.ERR s{i} = .None
h_s{i}_pc  : r StateField.PC  s{i} = $PC
h_run      : sf = run $STEPS s0
```
Where $PC and $STEPS are concrete constants.
Note that the tactic will search for assumption of *exactly* these names,
it won't search by def-eq -/
elab "sym1_i_n" i:num n:num _program:(ident)? : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    simp (config := {failIfUnchanged := false}) only [state_simp_rules] at *
  ))
  let mut c := SymContext.default i.getNat
  for _ in List.range n.getNat do
    c ← sym1 c

/--
`sym1_n n` will symbolically evaluate a program for `n` steps.
Alternatively,
  `sym1_n n at s` does the same, with `s` as initial state

If `s` is not passed, the initial state is inferred from the local context

The context is searched (up-to def-eq!) for hypotheses
```
h_program : s.program = ?concreteProgram
    h_err : r StateField.ERR s = .None
     h_pc : r StateField.PC  s = ?PC
    h_run : sf = run ?STEPS s
```
Where ?PC and ?STEPS must reduce to a concrete literal,
and concreteProgram must be a constant (i.e., a global definition refered to by name). -/
syntax sym_at := "at" ident
elab "sym1_n" n:num s:(sym_at)? : tactic =>
  Lean.Elab.Tactic.withMainContext <| do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      simp (config := {failIfUnchanged := false}) only [state_simp_rules] at *
    ))
    let s := s.map fun
      | `(sym_at|at $s:ident) => s.getId
      | _ => panic! "Unexpected syntax: {s}"
    let mut c ← SymContext.fromLocalContext s
    for _ in List.range n.getNat do
      c ← sym1 c
