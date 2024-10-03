/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Alex Keizer
-/
import Arm.Exec
import Arm.Memory.MemoryProofs
import Tactics.FetchAndDecode
import Tactics.Sym.Context

import Lean

open BitVec
open Lean
open Lean.Meta Lean.Elab.Tactic

open AxEffects SymContext

/-- A wrapper around `evalTactic` that traces the passed tactic script,
executes those tactics, and then traces the new goal state -/
private def evalTacticAndTrace (tactic : TSyntax `tactic) : TacticM Unit :=
  withTraceNode m!"running: {tactic}" <| do
    evalTactic tactic
    trace[Tactic.sym] "new goal state:\n{← getGoals}"

private def Sym.traceHeartbeats (header : Option String := none) :=
  _root_.traceHeartbeats `Tactic.sym.heartbeats header
open Sym (traceHeartbeats)

/-- `init_next_step h_run stepi_eq sn` splits the hypothesis
  `h_run: s_final = run (n+1) s`
by adding a new state variable, `sn`, and two new hypotheses:
  `stepi_eq : stepi s = s_next`
  `h_run'   : s_final = run n s_next`
to the local context of the main goal.
The names are obtained from the respectively named arguments to the tactic -/
macro "init_next_step" h_run:ident stepi_eq:ident sn:ident : tactic =>
  `(tactic|
    (-- use `let` over `obtain` to prevent `.intro` goal tags
     let ⟨$sn:ident, ⟨$stepi_eq:ident, h_run_new⟩⟩ := run_onestep $h_run:ident
     replace $h_run:ident := h_run_new
     clear h_run_new
    ))

section stepiTac

/-- Apply the relevant pre-generated stepi lemma to an expression
  `stepi_eq : stepi ?s = ?s'`
to add a new local hypothesis in terms of `w` and `write_mem`
  `h_step : ?s' = w _ _ (w _ _ (... ?s))`
-/
def stepiTac (stepiEq : Expr) (hStep : Name) : SymReaderM Unit := fun ctx =>
  withMainContext' <|
  withVerboseTraceNode m!"stepiTac: {stepiEq}" <| do
    let pc := (Nat.toDigits 16 ctx.pc.toNat).asString
    --  ^^ The PC in hex
    let stepLemma := Name.str ctx.program s!"stepi_eq_0x{pc}"
    -- let stepLemma := Expr.const stepLemma []

    let eff := ctx.effects
    let hStepExpr ← mkEqTrans
      (← mkEqSymm stepiEq)
      (← mkAppM stepLemma #[
        eff.programProof,
        (← eff.getField .PC).proof,
        (← eff.getField .ERR).proof
      ])

    let goal ← getMainGoal
    let ⟨_, goal⟩ ← goal.note hStep hStepExpr
    replaceMainGoal [goal]

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
def unfoldRun (whileTac : Unit → TacticM Unit) : SymReaderM Unit := do
  let c ← readThe SymContext
  withTraceNode m!"unfoldRun (runSteps? := {c.runSteps?})" (tag := "unfoldRun") <|
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
    | none => withMainContext' do
        let mut goal :: originalGoals ← getGoals
          | throwNoGoalsToBeSolved
        let hRunDecl ← c.hRunDecl

        -- Assert that `h_run : <finalState> = run ?runSteps <state>`
        let runSteps ← mkFreshExprMVar (mkConst ``Nat)
        guard <|← isDefEq hRunDecl.type (
          mkApp3 (.const ``Eq [1]) (mkConst ``ArmState)
            c.finalState
            (mkApp2 (mkConst ``_root_.run) runSteps (← getCurrentState)))
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

        withTraceNode m!"runSteps is not statically known, so attempt to prove:\
          {subGoal}" <|
        subGoal.withContext <| do
          setGoals [subGoal]
          whileTac () -- run `whileTac` to attempt to close `subGoal`

        -- Ensure `runStepsPred` is assigned, by giving it a default value
        -- This is important because of the use of `replaceLocalDecl` below
        if !(← runStepsPredId.isAssigned) then
          let default := mkApp (mkConst ``Nat.pred) runSteps
          trace[Tactic.sym] "{runStepsPred} is unassigned, \
          so we assign to the default value ({default})"
          runStepsPredId.assign default

        -- Change the type of `h_run`
        let state ← getCurrentState
        let typeNew ← do
          let rhs := mkApp2 (mkConst ``_root_.run) subGoalTyRhs state
          mkEq c.finalState rhs
        let eqProof ← do
          let f := -- `fun s => <finalState> = s`
            let eq := mkApp3 (.const ``Eq [1]) (mkConst ``ArmState)
                        c.finalState (.bvar 0)
            .lam `s (mkConst ``ArmState) eq .default
          let g := mkConst ``_root_.run
          let h ← instantiateMVars (.mvar subGoal)
          mkCongrArg f (←mkCongrFun (←mkCongrArg g h) state)
        let res ← goal.replaceLocalDecl hRunDecl.fvarId typeNew eqProof

        -- Restore goal state
        if !(←subGoal.isAssigned) then
          trace[Tactic.sym] "Subgoal {subGoal} was not closed yet, \
          so add it as a goal for the user to solve"
          originalGoals := originalGoals.concat subGoal
        setGoals (res.mvarId :: originalGoals)

/-- Break an equality `h_step : s{i+1} = w ... (... (w ... s{i})...)` into an
`AxEffects` that characterizes the effects in terms of reads from `s{i+1}`,
add the relevant hypotheses to the local context, and
store an `AxEffects` object with the newly added variables in the monad state
-/
def explodeStep (hStep : Expr) : SymM Unit :=
  withMainContext' <|
  withTraceNode m!"explodeStep {hStep}" (tag := "explodeStep") <| do
    let c ← getThe SymContext
    let mut eff ← AxEffects.fromEq hStep c.effects.stackAlignmentProof?

    let stateExpr ← getCurrentState
    /- Assert that the initial state of the obtained `AxEffects` is equal to
    the state tracked by `c`.
    This will catch and throw an error if the semantics of the current
    instruction still contains unsupported constructs (e.g., an `if`) -/
    if !(← isDefEq eff.initialState stateExpr) then
      throwError "[explodeStep] expected initial state {stateExpr}, but found:\n  \
        {eff.initialState}\nin\n\n{eff}"

    eff ← eff.withProgramEq c.effects.programProof
    eff ← eff.withField (← c.effects.getField .ERR).proof

    if let some hSp := c.effects.stackAlignmentProof? then
      withVerboseTraceNode m!"discharging side condiitions" <| do
        for subGoal in eff.sideConditions do
          trace[Tactic.sym] "attempting to discharge side-condition:\n  {subGoal}"
          let subGoal? ← do
            let (ctx, simprocs) ←
              LNSymSimpContext
                (config := {failIfUnchanged := false, decide := true})
                (exprs := #[hSp])
            LNSymSimp subGoal ctx simprocs

          if let some subGoal := subGoal? then
            trace[Tactic.sym] "subgoal got simplified to:\n{subGoal}"
            subGoal.setTag (.mkSimple s!"h_{← getNextStateName}_sp_aligned")
            appendGoals [subGoal]
          else
            trace[Tactic.sym] "subgoal got closed by simplification"
    else
      appendGoals eff.sideConditions
    eff := { eff with sideConditions := [] }

    -- Add new (non-)effect hyps to the context, and to the aggregation simpset
    withMainContext' <| do
      if ←(getBoolOption `Tactic.sym.debug) then
        eff.validate

      let eff ← eff.addHypothesesToLContext s!"h_{← getNextStateName}_"
      withMainContext' <| do
        let simpThms ← eff.toSimpTheorems
        modifyThe SymContext (·.addSimpTheorems simpThms)
      set eff

/-- A tactic wrapper around `explodeStep`.
Note the use of `SymContext.fromLocalContext`,
so the local context is assumed to be of the same shape as for `sym_n` -/
elab "explode_step" h_step:term " at " state:term : tactic => withMainContext do
  let hStep ← elabTerm h_step none
  let state ← elabTerm state mkArmState
  let .fvar stateFVar := state
    | throwError "Expected fvar, found {state}"
  let stateDecl := (← getLCtx).get! stateFVar
  let c ← SymContext.fromMainContext (some stateDecl.userName)
  let _ ← SymM.run c <| explodeStep hStep

/--
Symbolically simulate a single step, according the the symbolic simulation
context `c`, returning the context for the next step in simulation. -/
def sym1 (whileTac : TSyntax `tactic) : SymM Unit := do
  /- `withCurHeartbeats` sets the initial heartbeats to the current heartbeats,
  effectively resetting our heartbeat budget back to the maximum. -/
  withCurrHeartbeats <| do

  let stateNumber ← getCurrentStateNumber
  withTraceNode m!"(sym1): simulating step {stateNumber}" (tag:="sym1") <|
  withMainContext' do
    withVerboseTraceNode "verbose context" (tag := "infoDump") <| do
      traceSymContext
      trace[Tactic.sym] "Goal state:\n {← getMainGoal}"

    let stepi_eq := Lean.mkIdent (.mkSimple s!"stepi_{← getCurrentStateName}")
    let h_step   := Lean.mkIdent (.mkSimple s!"h_step_{stateNumber + 1}")

    unfoldRun (fun _ => evalTacticAndTrace whileTac)

    -- Add new state to local context
    withTraceNode "initNextStep" (tag := "initNextStep") <| do
      let hRunId      := mkIdent <|← getHRunName
      let nextStateId := mkIdent <|← getNextStateName
      evalTacticAndTrace <|← `(tactic|
        init_next_step $hRunId:ident $stepi_eq:ident $nextStateId:ident
      )

    -- Apply relevant pre-generated `stepi` lemma
    withMainContext' <| do
      let stepiEq ← SymContext.findFromUserName stepi_eq.getId
      stepiTac stepiEq.toExpr h_step.getId

    -- WORKAROUND: eventually we'd like to eagerly simp away `if`s in the
    -- pre-generation of instruction semantics. For now, though, we keep a
    -- `simp` here
    withMainContext' <| do
      let hStep ← SymContext.findFromUserName h_step.getId

      -- If we know SP is aligned, `simp` with that fact
      if let some hSp := (← getThe AxEffects).stackAlignmentProof? then
        let msg := m!"simplifying {hStep.toExpr} with {hSp}"
        withTraceNode msg (tag := "simplifyHStep") <| do
          let some goal ← do
              let (ctx, simprocs) ← LNSymSimpContext
                (config := {decide := false}) (exprs := #[hSp])
              let goal ← getMainGoal
              LNSymSimp goal ctx simprocs hStep.fvarId
            | throwError "internal error: simp closed goal unexpectedly"
          replaceMainGoal [goal]
      else
        trace[Tactic.sym] "we have no relevant local hypotheses, \
          skipping simplification step"

    -- Prepare `h_program`,`h_err`,`h_pc`, etc. for next state
    withMainContext' <| do
      let hStep ← SymContext.findFromUserName h_step.getId
      -- ^^ we can't reuse `hStep` from before, since its fvarId might've been
      --    changed by `simp`
      explodeStep hStep.toExpr
      prepareForNextStep

      let goal ← getMainGoal
      let goal ← goal.clear hStep.fvarId
      replaceMainGoal [goal]

      traceHeartbeats

/-- `ensureLessThanRunSteps n` will
- log a warning and return `m`, if `runSteps? = some m` and `m < n`, or
- return `n` unchanged, otherwise  -/
def ensureAtMostRunSteps (n : Nat) : SymM Nat := do
  withVerboseTraceNode "" (tag := "ensureAtMostRunSteps") <| do
    let ctx ← getThe SymContext
    match ctx.runSteps? with
    | none => pure n
    | some runSteps =>
        if n ≤ runSteps then
          pure n
        else
          withMainContext <| do
            let hRun ← ctx.hRunDecl
            logWarning m!"Symbolic simulation is limited to at most {runSteps} \
              steps, because {hRun.toExpr} is of type:\n  {hRun.type}"
            pure runSteps
    return n

/-- Check that the step-thoerem corresponding to the current PC value exists,
and throw a user-friendly error, pointing to `#genStepEqTheorems`,
if it does not. -/
def assertStepTheoremsGenerated : SymM Unit :=
  withVerboseTraceNode "" (tag := "assertStepTheoremsGenerated") <| do
    let c ← getThe SymContext
    let pc := c.pc.toHexWithoutLeadingZeroes
    if !c.programInfo.instructions.contains c.pc then
      let pcEff ← AxEffects.getFieldM .PC
      throwError "\
        Program {c.program} has no instruction at address {c.pc}.

        We inferred this address as the program-counter from {pcEff.proof}, \
        which has type:
          {← inferType pcEff.proof}"

    let step_thm := Name.str c.program ("stepi_eq_0x" ++ pc)
    try
      let _ ← getConstInfo step_thm
    catch err =>
      throwErrorAt err.getRef "{err.toMessageData}\n
  Did you remember to generate step theorems with:
    #genStepEqTheorems {c.program}"
  -- TODO: can we make this error ^^ into a `Try this:` suggestion that
  --       automatically adds the right command just before the theorem?

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
  traceHeartbeats "initial heartbeats"

  let s ← s.mapM fun
    | `(sym_at|at $s:ident) => pure s.getId
    | _ => Lean.Elab.throwUnsupportedSyntax
  let whileTac? : Option (TSyntax `tactic) ← whileTac?.mapM fun
    | `(sym_while|(while := $tactic)) => pure tactic
    | _ => Lean.Elab.throwUnsupportedSyntax
  let whileTac ← match whileTac? with
    | some t => pure t
    | none   => `(tactic|( -- the default `whileTac` is a wrapper around `omega`
        -- show ?x = (?x - 1) + 1; -- force the meta-variable to be assigned
        apply Eq.symm (Nat.succ_pred ?_);
        omega;
        ))

  let c ← SymContext.fromMainContext s
  SymM.run' c <| withMainContext' <|  do
    -- Check pre-conditions
    assertStepTheoremsGenerated
    let n ← ensureAtMostRunSteps n.getNat

    withMainContext' <| do
      -- The main loop
      for _ in List.range n do
        sym1 whileTac

    traceHeartbeats "symbolic simulation total"
    withCurrHeartbeats <|
    withTraceNode "Post processing" (tag := "postProccessing") <| do
      let c ← getThe SymContext
      -- Check if we can substitute the final state
      if c.runSteps? = some 0 then
        let msg := do
          let hRun ← userNameToMessageData c.h_run
          pure m!"runSteps := 0, substituting along {hRun}"
        withMainContext' <|
        withTraceNode `Tactic.sym (fun _ => msg) <| do
          let sfEq ← mkEq (← getCurrentState) c.finalState

          let goal ← getMainGoal
          trace[Tactic.sym] "original goal:\n{goal}"
          let ⟨hEqId, goal⟩ ← do
            let hRun ← SymContext.findFromUserName c.h_run
            goal.note `this (← mkEqSymm hRun.toExpr) sfEq
          goal.withContext <| do
            trace[Tactic.sym] "added {← userNameToMessageData `this} of type \
              {sfEq} in:\n{goal}"

          let goal ← subst goal hEqId
          trace[Tactic.sym] "performed subsitutition in:\n{goal}"
          replaceMainGoal [goal]

      -- Rudimentary aggregation: we feed all the axiomatic effect hypotheses
      -- added while symbolically evaluating to `simp`
      withMainContext' <|
      withTraceNode m!"aggregating (non-)effects" (tag := "aggregateEffects") <| do
        let goal? ← LNSymSimp (← getMainGoal) c.aggregateSimpCtx c.aggregateSimprocs
        replaceMainGoal goal?.toList

      traceHeartbeats "aggregation"
