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

import Lean

initialize
  Lean.registerTraceClass `Sym

open BitVec
open Lean
open Lean.Elab.Tactic (TacticM evalTactic withMainContext)

/-- A wrapper around `evalTactic` that traces the passed tactic script and
then executes those tactics -/
private def evalTacticAndTrace (tactic : TSyntax `tactic) : TacticM Unit := do
  trace[Sym] "running:\n{tactic}"
  evalTactic tactic

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

section stepiTac

/-- Apply the relevant pre-generated stepi lemma to replace a local hypothesis
  `h_step : ?s' = stepi ?s`
with an hypothesis in terms of `w` and `write_mem`
  `h_step : ?s' = w _ _ (w _ _ (... ?s))`
-/
def stepiTac (h_step : Ident) (ctx : SymContext)
  : TacticM Unit := withMainContext do
  let pc := (Nat.toDigits 16 ctx.pc.toNat).asString
  --  ^^ The PC in hex
  let step_lemma := mkIdent <| Name.str ctx.program s!"stepi_0x{pc}"

  evalTacticAndTrace <|← `(tactic| (
    replace $h_step :=
      (propext_iff.mp
        ($step_lemma:ident
          _
          $ctx.next_state_ident:ident
          $ctx.h_program_ident:ident
          $ctx.h_pc_ident:ident
          $ctx.h_err_ident:ident)).mp
      $h_step
  ))

elab "stepi_tac" h_step:ident : tactic => do
  let c ← SymContext.fromLocalContext none
  stepiTac (h_step) c

end stepiTac

def sym1 (c : SymContext) : TacticM SymContext :=
  withMainContext do
    trace[Sym] "(sym1): simulating step {c.curr_state_number}:\n{repr c}"
    let h_step_n' := Lean.mkIdent (.mkSimple s!"h_step_{c.curr_state_number + 1}")

    -- Add new state to local context
    evalTacticAndTrace <|← `(tactic|
      init_next_step $c.h_run_ident:ident $h_step_n':ident $c.next_state_ident:ident
    )

    -- Apply relevant pre-generated `stepi` lemma
    stepiTac h_step_n' c

    -- Prepare `h_program`,`h_err`,`h_pc`, etc. for next state
    let h_st_prefix := Lean.Syntax.mkStrLit s!"h_{c.state}"
    evalTacticAndTrace <|← `(tactic|
      intro_fetch_decode_lemmas
        $h_step_n':ident $c.h_program_ident:ident $h_st_prefix:str
    )
    return c.next


/- used in `sym1_n` tactic -/
syntax sym_at := "at" ident

/--
`sym1_n n` will symbolically evaluate a program for `n` steps.
Alternatively,
  `sym1_n n at s` does the same, with `s` as initial state

If `s` is not passed, the initial state is inferred from the local context

The context is searched (up-to def-eq!) for hypotheses
```
h_program : s.program = ?concreteProgram
     h_pc : r StateField.PC  s = ?PC
    h_run : sf = run ?STEPS s
    h_err : r StateField.ERR s = .None
     h_sp : CheckSPAlignment s
```
Where ?PC and ?STEPS must reduce to a concrete literal,
and ?concreteProgram must be a constant
(i.e., a global definition refered to by name).

Hypotheses `h_err` and `h_sp` may be missing,
in which case a new goal of the appropriate type will be added.
The other hypotheses *must* be present,
since we infer required information from their types. -/
elab "sym1_n" n:num s:(sym_at)? : tactic =>
  let s := s.map fun
    | `(sym_at|at $s:ident) => s.getId
    | _ => panic! "Unexpected syntax: {s}"
  Lean.Elab.Tactic.withMainContext <| do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      simp (config := {failIfUnchanged := false}) only [state_simp_rules] at *
    ))

    let mut c ← SymContext.fromLocalContext s
    c ← c.addGoalsForMissingHypotheses

    let n ←
      if n.getNat ≤ c.runSteps then
        pure n.getNat
      else
        let h_run ← userNameToMessageData c.h_run
        logWarning m!"Symbolic simulation using {h_run} is limited to at most {c.runSteps} steps"
        pure c.runSteps

    -- The main loop
    for _ in List.range n do
      c ← sym1 c
