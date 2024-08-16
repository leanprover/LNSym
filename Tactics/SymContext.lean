/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean
import Lean.Meta

import Arm.Exec
import Tactics.Common

/-!
This files defines the `SymContext` structure,
which collects the names of various
variables/hypotheses in the local context required for symbolic evaluation.

The canonical way to construct a `SymContext` is through `fromLocalContext`,
which searches the local context (up to def-eq) for variables and hypotheses of
the expected types.

Alternatively, there is `SymContext.default`,
which returns a context using hard-coded names,
simply assuming those hypotheses to be present
without looking at the local context.
This function exists for backwards compatibility,
and is likely to be deprecated and removed in the near future. -/

open Lean Meta Elab.Tactic
open BitVec

/-- A `SymContext` collects the names of various variables/hypotheses in
the local context required for symbolic evaluation -/
structure SymContext where
  /-- `state` is a local variable of type `ArmState` -/
  state : Name
  /-- `finalState` is an expression of type `ArmState` -/
  finalState : Expr
  /-- `runSteps` is the number of steps that we can *maximally* simulate,
  because of the way it occurs in `h_run`.
  Note that `runSteps` is a meta-level natural number, reflecting the fact that
  we expect the number of steps in `h_run` to be expressed as a concrete literal
  -/
  runSteps : Nat
  /-- `h_run` is a local hypothesis of the form
  `finalState = run {runSteps} state` -/
  h_run : Name
  /-- `program` is a *constant* which represents the program being evaluated -/
  program : Name
  /-- `h_program` is a local hypothesis of the form `state.program = program` -/
  h_program : Name
  /-- `pc` is the *concrete* value of the program counter

  Note that for now we only support symbolic evaluation of programs
  at statically known addresses.
  At some point in the near future,
  we will want to support addresses of the type `base + / - offset` as well,
  where `base` is an arbitrary variable and `offset` is statically known.
  We could do so by refactoring `pc` to be of type `Bool × BitVec 64`,
  so long as we assume the instruction addresses in a single program will
  either be all statically known, or all offset against the same `base` address,
  and we assume that no overflow happens
  (i.e., `base - x` can never be equal to `base + y`) -/
  pc : BitVec 64
  /-- `h_pc` is a local hypothesis of the form `r StateField.PC state = pc` -/
  h_pc  : Name
  /-- `h_err?`, if present, is a local hypothesis of the form
  `r StateField.ERR state = .None` -/
  h_err? : Option Name
  /-- `h_sp?`, if present, is a local hypothesis of the form
  `CheckSPAlignment state` -/
  h_sp?  : Option Name

  /-- `state_prefix` is used together with `curr_state_number`
  to determine the name of the next state variable that is added by `sym` -/
  state_prefix      : String := "s"
  /-- `curr_state_number` is incremented each simulation step,
  and used together with `curr_state_number`
  to determine the name of the next state variable that is added by `sym` -/
  curr_state_number : Nat := 0
  deriving Repr

namespace SymContext

/-! ## Simple projections -/
section
open Lean (Ident mkIdent)
variable (c : SymContext)

/-- `next_state` generates the name for the next intermediate state -/
def next_state (c : SymContext) : Name :=
  .mkSimple s!"{c.state_prefix}{c.curr_state_number + 1}"

/-- return `h_err?` if given, or a default hardcoded name -/
def h_err : Name := c.h_err?.getD (.mkSimple s!"h_{c.state}_err")

/-- return `h_sp?` if given, or a default hardcoded name -/
def h_sp  : Name := c.h_err?.getD (.mkSimple s!"h_{c.state}_sp")

def state_ident       : Ident := mkIdent c.state
def next_state_ident  : Ident := mkIdent c.next_state
def h_run_ident       : Ident := mkIdent c.h_run
def h_program_ident   : Ident := mkIdent c.h_program
def h_pc_ident        : Ident := mkIdent c.h_pc
def h_err_ident       : Ident := mkIdent c.h_err
def h_sp_ident        : Ident := mkIdent c.h_sp

def stateExpr : MetaM Expr := do
  let some decl := (← getLCtx).findFromUserName? c.state
    | throwError "Unknown local variable `{c.state}`"
  return Expr.fvar decl.fvarId

end

/-! ## Creating initial contexts -/

/-- Infer `state_prefix` and `curr_state_number` from the `state` name
as follows: if `state` is `s{i}` for some number `i` and a single character `s`,
then `s` is the prefix and `i` the number,
otherwise ignore `state`, and start counting from `s1` -/
def inferStatePrefixAndNumber (ctxt : SymContext) : SymContext :=
  let state := ctxt.state.toString
  let tail := state.toSubstring.drop 1

  if let some curr_state_number := tail.toNat? then
    { ctxt with
      state_prefix := (state.get? 0).getD 's' |>.toString,
      curr_state_number }
  else
    { ctxt with
      state_prefix := "s",
      curr_state_number := 1 }

/-- Annotate any errors thrown by `k` with a local variable (and its type) -/
private def withErrorContext (name : Name) (type? : Option Expr) (k : MetaM α) :
    MetaM α :=
  try k catch e =>
    let h ← userNameToMessageData name
    let type := match type? with
      | some type => m!" : {type}"
      | none      => m!""
    throwErrorAt e.getRef "{e.toMessageData}\n\nIn {h}{type}"

/-- Build a `SymContext` by searching the local context for hypotheses of the
required types (up-to defeq) -/
def fromLocalContext (state? : Option Name) : MetaM SymContext := do
  let lctx ← getLCtx

  -- Either get the state expression from the local context,
  -- or, if no state was given, create a new meta variable for the state
  let stateExpr : Expr ← match state? with
    | some state =>
      let some decl := lctx.findFromUserName? state
        | throwError "Unknown local variable `{state}`"
      pure (Expr.fvar decl.fvarId)
    | none => mkFreshExprMVar (Expr.const ``ArmState [])

  -- Find `h_run`
  let finalState ← mkFreshExprMVar none
  let runSteps ← mkFreshExprMVar (Expr.const ``Nat [])
  let h_run_type := h_run_type finalState runSteps stateExpr
  let h_run ← findLocalDeclUsernameOfTypeOrError h_run_type

  -- Unwrap and reflect `runSteps`
  let runSteps ← withErrorContext h_run h_run_type <| reflectNatLiteral runSteps
  let finalState ← instantiateMVars finalState

  -- At this point, `stateExpr` should have been assigned (if it was an mvar),
  -- so we can unwrap it to get the underlying name
  let stateExpr ← instantiateMVars stateExpr
  let state ← state?.getDM <| do
    let .fvar state := stateExpr
      | let h_run ← userNameToMessageData h_run
        throwError
  "Expected a free variable, found:
    {stateExpr}
  We inferred this as the initial state because we found:
    {h_run} : {← instantiateMVars h_run_type}
  in the local context.

  If this is wrong, please explicitly provide the right initial state,
  as in `sym {runSteps} at ?s0`
  "
    let some state := lctx.find? state
      /- I don't expect this error to be possible in a well-formed state,
      but you never know -/
      | throwError "Failed to find local variable for state {stateExpr}"
    pure state.userName

  -- Try to find `h_program`, and infer `program` from it
  let ⟨h_program, program⟩ ← withErrorContext h_run h_run_type <|
    findProgramHyp stateExpr
  let h_program := h_program.userName
  /-
    TODO: assert that the expected `stepi` theorems have been generated
  -/

  -- Then, try to find `h_pc`
  let pc ← mkFreshExprMVar (← mkAppM ``BitVec #[toExpr 64])
  let h_pc_type := h_pc_type stateExpr pc
  let h_pc ← findLocalDeclUsernameOfTypeOrError h_pc_type

  -- Unwrap and reflect `pc`
  let pc ← instantiateMVars pc
  let pc ← withErrorContext h_pc h_pc_type <| reflectBitVecLiteral 64 pc

  -- Attempt to find `h_err` and `h_sp`
  let h_err? ← findLocalDeclUsernameOfType? (h_err_type stateExpr)
  if h_err?.isNone then
    trace[Sym] "Could not find local hypothesis of type {h_err_type stateExpr}"
  let h_sp?  ← findLocalDeclUsernameOfType? (h_sp_type stateExpr)
  if h_sp?.isNone then
    trace[Sym] "Could not find local hypothesis of type {h_sp_type stateExpr}"

  return inferStatePrefixAndNumber {
    state, finalState, h_run, runSteps, program, h_program, pc, h_pc,
    h_err?, h_sp?
  }
where
  findLocalDeclUsernameOfType? (expectedType : Expr) : MetaM (Option Name) := do
    let decl ← findLocalDeclOfType? expectedType
    return (·.userName) <$> decl
  findLocalDeclUsernameOfTypeOrError (expectedType : Expr) : MetaM Name := do
    let decl ← findLocalDeclOfTypeOrError expectedType
    return decl.userName



/-! ## Massaging the local context -/

/-- If `h_sp` or `h_err` are missing from the `SymContext`,
add new goals of the expected types,
and use these to add `h_sp` and `h_err` to the main goal context -/
def addGoalsForMissingHypotheses (ctx : SymContext) : TacticM SymContext :=
  withMainContext do
    let mut ctx := ctx
    let mut goal ← getMainGoal
    let mut newGoals := []
    let lCtx ← getLCtx
    let some stateExpr :=
      (Expr.fvar ·.fvarId) <$> lCtx.findFromUserName? ctx.state
      | throwError "Could not find '{ctx.state}' in the local context"

    if ctx.h_err?.isNone then
      let h_err? := Name.mkSimple s!"h_{ctx.state}_run"
      let newGoal ← mkFreshMVarId

      goal := ← do
        let goalType := h_err_type stateExpr
        let newGoalExpr ← mkFreshExprMVarWithId newGoal goalType
        let goal' ← goal.assert h_err? goalType newGoalExpr
        let ⟨_, goal'⟩ ← goal'.intro1P
        return goal'

      newGoals := newGoal :: newGoals
      ctx := { ctx with h_err? }

    if ctx.h_sp?.isNone then
      let h_sp? := Name.mkSimple s!"h_{ctx.state}_sp"
      let newGoal ← mkFreshMVarId

      goal := ← do
        let h_sp_type := h_sp_type stateExpr
        let newGoalExpr ← mkFreshExprMVarWithId newGoal h_sp_type
        let goal' ← goal.assert h_sp? h_sp_type newGoalExpr
        let ⟨_, goal'⟩ ← goal'.intro1P
        return goal'

      newGoals := newGoal :: newGoals
      ctx := { ctx with h_sp? }

    replaceMainGoal (goal :: newGoals)
    return ctx

/-- change the type (in the local context of the main goal)
of the hypotheses tracked by the given `SymContext` to be *exactly* of the shape
described in the relevant docstrings.

That is, (un)fold types which were definitionally, but not syntactically,
equal to the expected shape. -/
def changeHypothesisTypes (c : SymContext) : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  let mut goal ← getMainGoal
  let state ← c.stateExpr
  let program := mkConst c.program

  let mut hyps := #[
    (c.h_run, h_run_type c.finalState (toExpr c.runSteps) state),
    (c.h_program, h_program_type state program),
    (c.h_pc, h_pc_type state (toExpr c.pc))
  ]
  if let some h_err := c.h_err? then
    hyps := hyps.push (h_err, h_err_type state)
  if let some h_sp := c.h_sp? then
    hyps := hyps.push (h_sp, h_sp_type state)

  for ⟨name, type⟩ in hyps do
    let some decl := lctx.findFromUserName? name
      | throwError "Unknown local hypothesis `{c.state}`"
    goal ← goal.changeLocalDecl decl.fvarId type
  replaceMainGoal [goal]

/-! ## Incrementing the context to the next state -/

/-- `c.next` generates names for the next intermediate state and its hypotheses

`nextPc?`, if given, will be the pc of the next context.
If `nextPC?` is `none`, then the previous pc is incremented by 4 -/
def next (c : SymContext) (nextPc? : Option (BitVec 64) := none) :
    SymContext :=
  let curr_state_number := c.curr_state_number + 1
  let s := c.next_state
  {
    state       := s
    finalState  := c.finalState
    h_run       := c.h_run
    h_program   := .mkSimple s!"h_{s}_program"
    h_pc        := .mkSimple s!"h_{s}_pc"
    h_err?      := some <| .mkSimple s!"h_{s}_err"
    h_sp?       := some <| .mkSimple s!"h_{s}_sp"
    runSteps    := c.runSteps - 1
    program     := c.program
    pc          := nextPc?.getD (c.pc + 4#64)
    curr_state_number
    state_prefix := c.state_prefix
  }
