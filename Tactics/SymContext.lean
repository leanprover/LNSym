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

  /-- the effects of the current state, such as:
  - a proof that the PC is equal to `pc`
  - a proof that the current state is valid (`read_err _ = .None`)
  - a proof that the current state has the right program
  - and more, see `AxEffects` for the full list -/
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
  /-- `h_err?`, if present, is a local hypothesis of the form
  `r StateField.ERR state = .None` -/
  h_err? : Option Name
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

/-- `SymM` is a wrapper around `TacticM` with a mutable `SymContext` state -/
abbrev SymM := StateT SymContext TacticM

/-- `SymM` is a wrapper around `TacticM` with a read-only `SymContext` state -/
abbrev SymReaderM := ReaderT SymContext TacticM

namespace SymM

def run (ctx : SymContext) (k : SymM α) : TacticM (α × SymContext) :=
  StateT.run k ctx

def run' (ctx : SymContext) (k : SymM α) : TacticM α :=
  StateT.run' k ctx

instance : MonadLift SymReaderM SymM where
  monadLift x c := do return (←x c, c)

instance : MonadReaderOf AxEffects SymReaderM where
  read := do return (← readThe SymContext).effects

instance : MonadStateOf AxEffects SymM where
  get := readThe AxEffects
  set effects := do modifyThe SymContext ({· with effects})
  modifyGet f := do
    let (a, effects) := f (← getThe SymContext).effects
    modifyThe SymContext ({· with effects})
    return a

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
variable {m} [Monad m] [MonadReaderOf SymContext m]

def getCurrentStateNumber : m Nat := do return (← read).currentStateNumber

/-- Return the name of the hypothesis
  `h_run : <finalState> = run <runSteps> <initialState>` -/
def getHRunName : m Name := do return (← read).h_run

/-- Retrieve the name for the next state

NOTE: `getNextStateName` does not increment the state, so consecutive calls
will give the same name. Calling `prepareForNextStep` will increment the state.
-/
def getNextStateName : m Name := do
  let c ← read
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

/-- Modify a `SymContext` with a monadic action `k : SymM Unit` -/
def modify (ctxt : SymContext) (k : SymM Unit) : TacticM SymContext := do
  let ((), ctxt) ← SymM.run ctxt k
  return ctxt

/-- Infer `state_prefix` and `curr_state_number` from the `state` name
as follows: if `state` is `s{i}` for some number `i` and a single character `s`,
then `s` is the prefix and `i` the number,
otherwise ignore `state`, and start counting from `s1` -/
def inferStatePrefixAndNumber : SymM Unit := do
  let state ← AxEffects.getCurrentStateName
  let state := state.toString
  let tail := state.toSubstring.drop 1

  modifyThe SymContext fun ctxt =>
    if let some currentStateNumber := tail.toNat? then
      { ctxt with
        state_prefix := (state.get? 0).getD 's' |>.toString,
        currentStateNumber }
    else
      { ctxt with
        state_prefix := "s",
        currentStateNumber := 1 }

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
required types (up-to defeq) . The local context is modified to unfold the types
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

  -- Attempt to find `h_err` and `h_sp`
  let h_err? ← findLocalDeclOfType? (h_err_type stateExpr)
  if h_err?.isNone then
    trace[Sym] "Could not find local hypothesis of type {h_err_type stateExpr}"
  let h_sp?  ← findLocalDeclOfType? (h_sp_type stateExpr)
  if h_sp?.isNone then
    trace[Sym] "Could not find local hypothesis of type {h_sp_type stateExpr}"

  -- Finally, retrieve the programInfo from the environment
  let some programInfo ← ProgramInfo.lookup? program
    | throwError "Could not find program info for `{program}`.
        Did you remember to generate step theorems with:
          #generateStepEqTheorems {program}"

  -- Initialize the axiomatic hypotheses with hypotheses for the initial state
  let axHyps := #[h_program, h_pc] ++ h_err?.toArray ++ h_sp?.toArray
  let (aggregateSimpCtx, aggregateSimprocs) ←
    LNSymSimpContext
      (config := {decide := true, failIfUnchanged := false})
      (decls := axHyps)
      (noIndexAtArgs := false)

  -- Build an initial AxEffects
  let effects := AxEffects.initial stateExpr
  let mut fields :=
    effects.fields.insert .PC { value := pcE, proof := h_pc.toExpr}
  if let some hErr := h_err? then
    fields := fields.insert .ERR {
      value := mkConst ``StateError.None,
      proof := hErr.toExpr
    }
  let effects := { effects with
      programProof := h_program.toExpr
      stackAlignmentProof? := h_sp?.map (·.toExpr)
      fields
  }
  let c : SymContext := {
    finalState, runSteps?, pc,
    h_run := h_run.userName,
    h_err? := (·.userName) <$> h_err?,
    h_sp? := (·.userName) <$> h_sp?,
    programInfo,
    effects,
    aggregateSimpCtx, aggregateSimprocs
  }
  c.modify <|
    inferStatePrefixAndNumber
where
  findLocalDeclOfType? (expectedType : Expr) : MetaM (Option LocalDecl) := do
    let msg := m!"Searching for hypothesis of type: {expectedType}"
    withTraceNode `Tactic.sym (fun _ => pure msg) <| do
      let decl? ← _root_.findLocalDeclOfType? expectedType
      trace[Tactic.sym] "Found: {(·.toExpr) <$> decl?}"
      return decl?
  findLocalDeclOfTypeOrError (expectedType : Expr) : MetaM LocalDecl := do
    let msg := m!"Searching for hypothesis of type: {expectedType}"
    withTraceNode `Tactic.sym (fun _ => pure msg) <| do
      let decl ← _root_.findLocalDeclOfTypeOrError expectedType
      trace[Tactic.sym] "Found: {decl.toExpr}"
      return decl

/-! ## Massaging the local context -/

/-- If `h_sp` or `h_err` are missing from the `SymContext`,
add new goals of the expected types,
and use these to add `h_sp` and `h_err` to the main goal context -/
def addGoalsForMissingHypotheses (addHSp : Bool := false) : SymM Unit :=
  let msg := "Adding goals for missing hypotheses"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| withMainContext' do
    let mut ctx ← getThe SymContext
    let mut goal ← getMainGoal
    let mut newGoals := []
    let stateExpr ← AxEffects.getCurrentState
    let stateName ← AxEffects.getCurrentStateName

    match ctx.h_err? with
      | none =>
          trace[Tactic.sym] "h_err? is none, adding a new goal"

          let h_err? := Name.mkSimple s!"h_{stateName}_err"
          let newGoal ← mkFreshMVarId

          goal := ← do
            let goalType := h_err_type stateExpr
            let newGoalExpr ← mkFreshExprMVarWithId newGoal goalType
            let goal' ← goal.assert h_err? goalType newGoalExpr
            let ⟨_, goal'⟩ ← goal'.intro1P
            return goal'

          newGoals := newGoal :: newGoals
          ctx := { ctx with
            h_err?
            effects := ← ctx.effects.withField (.mvar newGoal)
          }
      | some h_err =>
          let h_err ← userNameToMessageData h_err
          trace[Tactic.sym] "h_err? is {h_err}, no new goal needed"

    match ctx.h_sp? with
      | none =>
          if addHSp then
            trace[Tactic.sym] "h_sp? is none, adding a new goal"

            let h_sp? := Name.mkSimple s!"h_{stateName}_sp"
            let newGoal ← mkFreshMVarId

            goal := ← do
              let h_sp_type := h_sp_type stateExpr
              let newGoalExpr ← mkFreshExprMVarWithId newGoal h_sp_type
              let goal' ← goal.assert h_sp? h_sp_type newGoalExpr
              let ⟨_, goal'⟩ ← goal'.intro1P
              return goal'

            newGoals := newGoal :: newGoals
            ctx := { ctx with
              h_sp?
              effects.stackAlignmentProof? := some (Expr.mvar newGoal)
            }
          else
            trace[Tactic.sym] "h_sp? is none, but addHSp is false, \
              so no new goal is added"
      | some h_sp =>
          let h_sp ← userNameToMessageData h_sp
          trace[Tactic.sym] "h_sp? is {h_sp}, no new goal needed"

    replaceMainGoal (goal :: newGoals)
    set ctx

/-- change the type (in the local context of the main goal)
of the hypotheses tracked by the given `SymContext` to be *exactly* of the shape
described in the relevant docstrings.

That is, (un)fold types which were definitionally, but not syntactically,
equal to the expected shape. -/
def canonicalizeHypothesisTypes : SymReaderM Unit := fun c => withMainContext do
  let lctx ← getLCtx
  let mut goal ← getMainGoal
  let state := c.effects.currentState

  let mut hyps := #[]
  if let some runSteps := c.runSteps? then
    hyps := hyps.push (c.h_run, h_run_type c.finalState (toExpr runSteps) state)
  if let some h_err := c.h_err? then
    hyps := hyps.push (h_err, h_err_type state)
  if let some h_sp := c.h_sp? then
    hyps := hyps.push (h_sp, h_sp_type state)

  for ⟨name, type⟩ in hyps do
    let some decl := lctx.findFromUserName? name
      | throwError "Unknown local hypothesis `{name}`"
    goal ← goal.replaceLocalDeclDefEq decl.fvarId type
  replaceMainGoal [goal]

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
