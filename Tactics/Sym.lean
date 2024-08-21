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

open BitVec
open Lean Meta
open Lean.Elab.Tactic

/-- A wrapper around `evalTactic` that traces the passed tactic script,
executes those tactics, and then traces the new goal state -/
private def evalTacticAndTrace (tactic : TSyntax `tactic) : TacticM Unit :=
  withTraceNode `Tactic.sym (fun _ => pure m!"running: {tactic}") <| do
    evalTactic tactic
    trace[Tactic.sym] "new goal state:\n{← getGoals}"

/-- `init_next_step h_run` splits the hypothesis

`h_run: s_final = run n s`

introduces a new state variable, say `s_next` and two new hypotheses:
`h_step: s_next = stepi s`
`h_run': s_final = run (n-1) s_next`

The new state variable and the hypotheses are not named yet.
-/
macro "init_next_step" h_run:ident h_step:ident sn:ident : tactic =>
  `(tactic|
    (-- use `let` over `obtain` to prevent `.intro` goal tags
     let ⟨$sn:ident, ⟨$h_step:ident, _⟩⟩ := run_onestep $h_run:ident;
     clear $h_run:ident; rename_i $h_run:ident
     simp (config := {ground := true, failIfUnchanged := false}) only
        at $h_run:ident))

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
  let step_lemma := mkIdent <| Name.str ctx.program s!"stepi_eq_0x{pc}"

  evalTacticAndTrace <|← `(tactic| (
    replace $h_step :=
      _root_.Eq.trans $h_step
        ($step_lemma:ident
          $ctx.h_program_ident:ident
          $ctx.h_pc_ident:ident
          $ctx.h_err_ident:ident)
  ))

elab "stepi_tac" h_step:ident : tactic => do
  let c ← SymContext.fromLocalContext none
  stepiTac (h_step) c

end stepiTac

/-- Attempt to show that we have (at least) one more step available,
by ensuring that `h_run`'s type is def-eq to:
  `<finalState> = run (_ + 1) <initialState>`

If the number of steps is statically tracked in `runSteps?`,
(i.e., it is a literal that we managed to reflect)
we check that this number is non-zero, and leave the type of `h_run` unchanged.
This means we trust that the reflected value is accurate
w.r.t. to the current goal state.

Otherwise, if the number is steps is *not* statically known, we assert that
`c.h_run` is of type `<finalState> = run ?runSteps <initialState>`,
for some metavariable `?runSteps`, then create the proof obligation
`?runSteps = _ + 1`, and attempt to close it using `whileTac`.
Finally, we use this proof to change the type of `h_run` accordingly.
-/
def unfoldRun (c : SymContext) (whileTac : Unit → TacticM Unit) :
    TacticM Unit :=
  let msg := m!"unfoldRun (runSteps? := {c.runSteps?})"
  withTraceNode `Tactic.sym (fun _ => pure msg) <|
  match c.runSteps? with
    | some (_ + 1) => do
        trace[Tactic.sym] "runSteps is statically known to be non-zero, \
        no further action required"
        return
    | some 0 =>
        throwError "No more steps available to symbolically simulate!"
        -- NOTE: this error shouldn't occur, as we should have checked in
        -- `sym_n` that, if the number of runSteps is statically known,
        -- that we never simulate more than that many steps
    | none => withMainContext do
        let mut goal :: originalGoals ← getGoals
          | throwNoGoalsToBeSolved
        let hRunDecl ← c.hRunDecl

        -- Assert that `h_run : <finalState> = run ?runSteps <state>`
        let runSteps ← mkFreshExprMVar (mkConst ``Nat)
        guard <|← isDefEq hRunDecl.type (
          mkApp3 (.const ``Eq [1]) (mkConst ``ArmState)
            c.finalState
            (mkApp2 (mkConst ``_root_.run) runSteps (←c.stateExpr)))
        -- NOTE: ^^ Since we check for def-eq on SymContext construction,
        --          this check should never fail

        -- Attempt to prove that `?runSteps` is non-zero
        let runStepsPredId ← mkFreshMVarId
        let runStepsPred ← mkFreshExprMVarWithId runStepsPredId (mkConst ``Nat)
        let subGoalTyRhs := mkApp (mkConst ``Nat.succ) runStepsPred
        let subGoalTy := -- `?runSteps = ?runStepsPred + 1`
          mkApp3 (.const ``Eq [1]) (mkConst ``Nat) runSteps subGoalTyRhs
        let subGoal ← mkFreshMVarId
        let _ ← mkFreshExprMVarWithId subGoal subGoalTy
        trace[Tactic.sym] "attempt to prove that {subGoalTy}"
        subGoal.withContext <|
          setGoals [subGoal]
          let () ← whileTac () -- run `whileTac` to attempt to close `subGoal`

        -- Ensure `runStepsPred` is assigned, by giving it a default value
        -- This is important because of the use of `replaceLocalDecl` below
        if !(← runStepsPredId.isAssigned) then
          let default := mkApp (mkConst ``Nat.pred) runSteps
          trace[Tactic.sym] "{runStepsPred} is unassigned, \
          so we assign to the default value ({default})"
          runStepsPredId.assign default

        -- Change the type of `h_run`
        let typeNew ← do
          let rhs := mkApp2 (mkConst ``_root_.run) subGoalTyRhs (←c.stateExpr)
          mkEq c.finalState rhs
        let eqProof ← do
          let f := -- `fun s => <finalState> = s`
            let eq := mkApp3 (.const ``Eq [1]) (mkConst ``ArmState)
                        c.finalState (.bvar 0)
            .lam `s (mkConst ``ArmState) eq .default
          let g := mkConst ``_root_.run
          let s ← c.stateExpr
          let h ← instantiateMVars (.mvar subGoal)
          mkCongrArg f (←mkCongrFun (←mkCongrArg g h) s)
        let res ← goal.replaceLocalDecl hRunDecl.fvarId typeNew eqProof

        -- Restore goal state
        if !(←subGoal.isAssigned) then
          trace[Tactic.sym] "Subgoal {subGoal} was not closed yet, \
          so add it as a goal for the user to solve"
          originalGoals := originalGoals.concat subGoal
        setGoals (res.mvarId :: originalGoals)

/--
Symbolically simulate a single step, according the the symbolic simulation
context `c`, returning the context for the next step in simulation. -/
def sym1 (c : SymContext) (whileTac : TSyntax `tactic) : TacticM SymContext :=
  let msg := m!"(sym1): simulating step {c.curr_state_number}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| withMainContext do
    trace[Tactic.sym] "SymContext:\n{← c.toMessageData}"
    trace[Tactic.sym] "Goal state:\n {← getMainGoal}"

    let h_step_n' := Lean.mkIdent (.mkSimple s!"h_step_{c.curr_state_number + 1}")

    unfoldRun c (fun _ => evalTactic whileTac)
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


/- used in `sym_n` tactic to specify an initial state -/
syntax sym_at := "at" ident

syntax sym_while := "(" "while" " := " tactic ")"

open Elab.Term (elabTerm) in
/--
`sym_n n` will symbolically evaluate a program for `n` steps.
Alternatively,
  `sym_n n at s` does the same, with `s` as initial state

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
elab "sym_n" whileTac?:(sym_while)? n:num s:(sym_at)? : tactic => do
  let s ← s.mapM fun
    | `(sym_at|at $s:ident) => pure s.getId
    | _ => Lean.Elab.throwUnsupportedSyntax
  let whileTac? : Option (TSyntax `tactic) ← whileTac?.mapM fun
    | `(sym_while|(while := $tactic)) => pure tactic
    | _ => Lean.Elab.throwUnsupportedSyntax
  let whileTac ← match whileTac? with
    | some t => pure t
    | none   => `(tactic|( -- the default `whileTac` is a wrapper around `omega`
        show ?x = (?x - 1) + 1; -- force the meta-variable to be assigned
        apply Nat.succ_pred;
        omega;
        ))

  Lean.Elab.Tactic.withMainContext <| do
    let mut c ← SymContext.fromLocalContext s
    c ← c.addGoalsForMissingHypotheses
    -- c.canonicalizeHypothesisTypes

    -- Check that we are not asked to simulate more steps than available
    let n ← do
      let n := n.getNat
      match c.runSteps? with
        | none => pure n -- Just assume the number makes sense
        | some runSteps =>
            if n ≤ runSteps then
              pure n
            else
              let h_run ← userNameToMessageData c.h_run
              logWarning m!"Symbolic simulation using {h_run} is limited to at most {runSteps} steps"
              pure runSteps

    -- Check that step theorems have been pre-generated
    try
      let pc := c.pc.toHexWithoutLeadingZeroes
      let step_thm := Name.str c.program ("stepi_eq_0x" ++ pc)
      let _ ← getConstInfo step_thm
    catch err =>
      throwErrorAt err.getRef "{err.toMessageData}\n
Did you remember to generate step theorems with:
  #generateStepEqTheorems {c.program}"
-- TODO: can we make this error ^^ into a `Try this:` suggestion that
--       automatically adds the right command just before the theorem?

    -- Check that step theorems have been pre-generated
    try
      let pc := c.pc.toHexWithoutLeadingZeroes
      let step_thm := Name.str c.program ("stepi_eq_0x" ++ pc)
      let _ ← getConstInfo step_thm
    catch err =>
      throwErrorAt err.getRef "{err.toMessageData}\n
Did you remember to generate step theorems with:
  #generateStepEqTheorems {c.program}"
-- TODO: can we make this error ^^ into a `Try this:` suggestion that
--       automatically adds the right command just before the theorem?

    -- The main loop
    for _ in List.range n do
      c ← sym1 c whileTac
