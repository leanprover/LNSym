/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean
import Lean.Meta

import Arm.Exec
import Tactics.Common
import Tactics.Attr
import Tactics.Reflect.ProgramInfo
import Tactics.Reflect.AxEffects
import Tactics.Simp

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
  /-- `finalState` is an expression of type `ArmState` -/
  finalState : Expr
  /-- `runSteps?` stores the number of steps that we can *maximally* simulate,
  if known.

  If `runSteps?` is `some n`, where `n` is a meta-level `Nat`,
  then we expect that `<runSteps>` in type of `h_run` is the literal `n`.
  Otherwise, if `runSteps?` is `none`,
  then `<runSteps>` is allowed to be anything, even a symbolic value.

  See also `SymContext.h_run` -/
  runSteps? : Option Nat
  /-- `h_run` is a local hypothesis of the form
    `finalState = run <runSteps> state`

  See also `SymContext.runSteps?` -/
  h_run : Name
  /-- `programInfo` is the relevant cached `ProgramInfo` -/
  programInfo : ProgramInfo

  /-- TODO -/
  effects : AxEffects

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
  /-- `h_sp?`, if present, is a local hypothesis of the form
  `CheckSPAlignment state` -/
  h_sp?  : Option Name

  /-- The `simp` context used for effect aggregation.
  This collects references to all (non-)effect hypotheses of the intermediate
  states, together with sensible default simp-lemmas used for
  effect aggregation -/
  aggregateSimpCtx : Simp.Context
  /-- Simprocs used for aggregation. This is stored for performance benefits,
  but should not be modified during the course of a `sym_n` call -/
  aggregateSimprocs : Simp.SimprocsArray

  /-- `state_prefix` is used together with `curr_state_number`
  to determine the name of the next state variable that is added by `sym` -/
  state_prefix      : String := "s"
  /-- `curr_state_number` is incremented each simulation step,
  and used together with `curr_state_number`
  to determine the name of the next state variable that is added by `sym` -/
  currentStateNumber : Nat := 0

/-! ## Monad -/

/-- `SymM` is a wrapper around `TacticM` with a `SymContext` state -/
abbrev SymM := StateT SymContext TacticM

namespace SymM

def run (ctx : SymContext) (k : SymM α) : TacticM (α × SymContext) :=
  StateT.run k ctx

def run' (ctx : SymContext) (k : SymM α) : TacticM α :=
  StateT.run' k ctx

instance : MonadStateOf AxEffects SymM where
  get         := do return (← get).effects
  set effects := modify ({· with effects })
  modifyGet f := modifyGet fun ctx =>
                    let (a, effects) := f ctx.effects
                    (a, { ctx with effects })

-- We need an alternative to `withMainContext`, which has a continuation in
-- `SymM` rather than `TacticM`
@[inherit_doc Lean.Elab.Tactic.withMainContext]
def withMainContext (k : SymM α) : SymM α := do
  (← getMainGoal).withContext k

end SymM

namespace SymContext

/-! ## Simple projections -/
section
open Lean (Ident mkIdent)
variable (c : SymContext)

/-- `program` is a *constant* which represents the program being evaluated -/
def program : Name := c.programInfo.name

/-- Find the local declaration that corresponds to a given name,
or throw an error if no local variable of that name exists -/
def findFromUserName (name : Name) : MetaM LocalDecl := do
  let some decl := (← getLCtx).findFromUserName? name
    | throwError "Unknown local variable `{name}`"
  return decl

/-- Find the local declaration that corresponds to `c.h_run`,
or throw an error if no local variable of that name exists -/
def hRunDecl : MetaM LocalDecl := do
  findFromUserName c.h_run

section Monad
variable {m} [Monad m] [MonadStateOf SymContext m]

def getCurrentStateNumber : m Nat := do return (← get).currentStateNumber

/-- Retrieve the name of the current state:
* if `AxEffects.getCurrentState` returns a free variable,
    which is in scope in the current ambient local context,
    return the corresponding username
* otherwise, generate a name based on `curr_state_number` and
    `state_prefix` -/
def getCurrentStateName [MonadLCtx m] : m Name := do
  let c ← get
  let fallback := Name.mkSimple s!"{c.state_prefix}{c.currentStateNumber}"
  if let Expr.fvar fvar := c.effects.currentState then
    let decl? := (← getLCtx).find? fvar
    return match decl? with
      | some d => d.userName
      | none   => fallback
  else
    return fallback

/-- Return the name of the hypothesis
  `h_run : <finalState> = run <runSteps> <initialState>` -/
def getHRunName : m Name := do return (← get).h_run

/-- Retrieve the name for the next state

NOTE: `getNextStateName` does not increment the state, so consecutive calls
will give the same name. You should use `prepareForNextStep` to increment the
state -/
def getNextStateName : m Name := do
  let c ← get
  return Name.mkSimple s!"{c.state_prefix}{c.currentStateNumber + 1}"

end Monad

end

/-! ## `ToMessageData` instance and tracing -/

/-- Convert a `SymContext` to `MessageData` for tracing.
This is not a `ToMessageData` instance because we need access to `MetaM` -/
def toMessageData (c : SymContext) : MetaM MessageData := do
  let h_run ← userNameToMessageData c.h_run
  let h_sp?  ← c.h_sp?.mapM userNameToMessageData

  return m!"\{ finalState := {c.finalState},
  runSteps? := {c.runSteps?},
  h_run := {h_run},
  program := {c.program},
  pc := {c.pc},
  h_sp? := {h_sp?},
  state_prefix := {c.state_prefix},
  curr_state_number := {c.currentStateNumber},
  effects := {c.effects} }"

variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadLiftT IO m]
  [MonadRef m] [AddMessageContext m] [MonadOptions m] {ε : Type}
  [MonadAlwaysExcept ε m] [MonadLiftT BaseIO m] in
def withSymTraceNode (msg : MessageData) (k : m α) : m α := do
  withTraceNode `Tactic.sym (fun _ => pure msg) k

def traceSymContext : SymM Unit :=
  withTraceNode `Tactic.sym (fun _ => pure m!"SymContext: ") <| do
    let m ← (← getThe SymContext).toMessageData
    trace[Tactic.sym] m

/-! ## Creating initial contexts -/

/-- Infer `state_prefix` and `curr_state_number` from the `state` name
as follows: if `state` is `s{i}` for some number `i` and a single character `s`,
then `s` is the prefix and `i` the number,
otherwise ignore `state`, and start counting from `s1` -/
def inferStatePrefixAndNumber (ctxt : SymContext) : MetaM SymContext :=
  withSymTraceNode m!"[inferStatePrefixAndNumber]" <| do
  let ((), ctxt) ← StateT.run (s := ctxt) do
    let state ← getCurrentStateName
    let state := state.toString
    let tail  := state.toSubstring.drop 1

    modifyThe SymContext fun ctxt =>
      if let some currentStateNumber := tail.toNat? then
        { ctxt with
          state_prefix := (state.get? 0).getD 's' |>.toString,
          currentStateNumber }
      else
        { ctxt with
          state_prefix := "s",
          currentStateNumber := 1 }
  return ctxt

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
required types (up-to defeq). The local context is modified to unfold the types
to be syntactically equal to the expected type.

If an hypothesis `h_err : r <state> .ERR = None` is not found,
we create a new subgoal of this type
-/
def fromLocalContext (state? : Option Name) : TacticM SymContext := do
  let msg := m!"Building a `SymContext` from the local context"
  withTraceNode `Tactic.sym (fun _ => pure msg) do
  trace[Tactic.Sym] "state? := {state?}"
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
  let h_run ←
    findLocalDeclOfTypeOrError <| h_run_type finalState runSteps stateExpr

  -- Unwrap and reflect `runSteps`
  let runSteps? ← do
    let msg := m!"Reflecting: {runSteps}"
    withTraceNode `Tactic.sym (fun _ => pure msg) <| do
      let runSteps? ← reflectNatLiteral? runSteps
      trace[Tactic.sym] "got: {runSteps?}"
      pure runSteps?
  let finalState ← instantiateMVars finalState

  -- At this point, `stateExpr` should have been assigned (if it was an mvar),
  -- so we can unwrap it to get the underlying name
  let stateExpr ← instantiateMVars stateExpr

  -- Try to find `h_program`, and infer `program` from it
  let ⟨h_program, program⟩ ← withErrorContext h_run.userName h_run.type <|
    findProgramHyp stateExpr

  -- Then, try to find `h_pc`
  let pcE ← mkFreshExprMVar (← mkAppM ``BitVec #[toExpr 64])
  let h_pc ← findLocalDeclOfTypeOrError <| h_pc_type stateExpr pcE

  -- Unwrap and reflect `pc`
  let pcE ← instantiateMVars pcE
  let pc ← withErrorContext h_pc.userName h_pc.type <|
    reflectBitVecLiteral 64 pcE

  -- Attempt to find `h_err`, adding a new subgoal if it couldn't be found
  let errHyp ← do
    let h_err? ← findLocalDeclOfType? (h_err_type stateExpr)
    match h_err? with
    | some d => pure d.toExpr
    | none => do
        let errHyp ← mkFreshExprMVar (h_err_type stateExpr)
        replaceMainGoal [← getMainGoal, errHyp.mvarId!]
        pure errHyp

  let h_sp?  ← findLocalDeclOfType? (h_sp_type stateExpr)
  if h_sp?.isNone then
    trace[Sym] "Could not find local hypothesis of type {h_sp_type stateExpr}"

  -- Finally, retrieve the programInfo from the environment
  let some programInfo ← ProgramInfo.lookup? program
    | throwError "Could not find program info for `{program}`.
        Did you remember to generate step theorems with:
          #generateStepEqTheorems {program}"

  -- Initialize the axiomatic hypotheses with hypotheses for the initial state
  let axHyps := #[h_program, h_pc] ++ h_sp?.toArray
  let (aggregateSimpCtx, aggregateSimprocs) ←
    LNSymSimpContext
      (config := {decide := true, failIfUnchanged := false})
      (decls := axHyps)
      (exprs := #[errHyp])
      (noIndexAtArgs := false)

  -- Build an initial AxEffects
  let effects := AxEffects.initial stateExpr
  let effects := { effects with
    fields := effects.fields
      |>.insert .PC { value := pcE, proof := h_pc.toExpr}
      |>.insert .ERR { value := mkConst ``StateError.None, proof := errHyp}
    programProof := h_program.toExpr
    stackAlignmentProof? := h_sp?.map (·.toExpr)
  }
  let c : SymContext := {
    finalState, runSteps?, pc,
    h_run := h_run.userName,
    h_sp? := (·.userName) <$> h_sp?,
    programInfo,
    effects,
    aggregateSimpCtx, aggregateSimprocs
  }
  inferStatePrefixAndNumber c
where
  /-- Assuming that `decl.type` is def-eq to `expectedType`,
  ensure the type of the fvar is syntactically equal to `expectedType`,
  by modifying the local context of the main goal  -/
  changeType (expectedType : Expr) (decl : LocalDecl) : TacticM Unit := do
    if decl.type != expectedType then
      let goal ← getMainGoal
      let goal ← goal.replaceLocalDeclDefEq decl.fvarId expectedType
      replaceMainGoal [goal]

  findLocalDeclOfType? (expectedType : Expr) : TacticM (Option LocalDecl) := do
    let msg := m!"Searching for hypothesis of type: {expectedType}"
    withTraceNode `Tactic.sym (fun _ => pure msg) <| do
      let decl? ← _root_.findLocalDeclOfType? expectedType
      let _ ← decl?.mapM (changeType expectedType)
      trace[Tactic.sym] "Found: {(·.toExpr) <$> decl?}"
      return decl?

  findLocalDeclOfTypeOrError (expectedType : Expr) : TacticM LocalDecl := do
    let msg := m!"Searching for hypothesis of type: {expectedType}"
    withTraceNode `Tactic.sym (fun _ => pure msg) <| do
      let decl ← _root_.findLocalDeclOfTypeOrError expectedType
      changeType expectedType decl
      trace[Tactic.sym] "Found: {decl.toExpr}"
      return decl

/-! ## Massaging the local context -/

open AxEffects

/-! ## Incrementing the context to the next state -/

/-- `prepareForNextStep` prepares the state for the next step of symbolic
evaluation:
  * `pc` is reflected from the stored `effects`
  * `runSteps?`, if specified, is decremented,
  * the `currentStateNumber` is incremented
-/
def prepareForNextStep : SymM Unit := do
  let s ← getNextStateName
  let pc ← do
    let { value, ..} ← AxEffects.getFieldM .PC
    try
      reflectBitVecLiteral 64 value
    catch err =>
      trace[Tactic.sym] "failed to reflect PC: {err.toMessageData}"
      pure <| (← getThe SymContext).pc + 4

  modifyThe SymContext (fun c => { c with
    pc
    h_sp?       := c.h_sp?.map (fun _ => .mkSimple s!"h_{s}_sp_aligned")
    runSteps?   := (· - 1) <$> c.runSteps?
    currentStateNumber := c.currentStateNumber + 1
  })

/-- Add a set of new simp-theorems to the simp-theorems used
for effect aggregation -/
def addSimpTheorems (c : SymContext) (simpThms : Array SimpTheorem) : SymContext :=
  let addSimpThms := simpThms.foldl addSimpTheoremEntry

  let oldSimpTheorems := c.aggregateSimpCtx.simpTheorems
  let simpTheorems :=
    if oldSimpTheorems.isEmpty then
      oldSimpTheorems.push <| addSimpThms {}
    else
      oldSimpTheorems.modify (oldSimpTheorems.size - 1) addSimpThms

  { c with aggregateSimpCtx.simpTheorems := simpTheorems }
