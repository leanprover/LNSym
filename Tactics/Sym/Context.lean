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
import Tactics.Sym.Common
import Tactics.Sym.ProgramInfo
import Tactics.Sym.AxEffects
import Tactics.Sym.LCtxSearch
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
open Sym (withTraceNode withInfoTraceNode)

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
  then `<runSteps>` is allowed to be anything, including a symbolic value.

  See also `SymContext.h_run` -/
  runSteps? : Option Nat
  /-- `hRun` is an expression of type
    `<finalState> = run <runSteps> state`

  See also `SymContext.runSteps?` -/
  hRun : Expr
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

/-- `SymReaderM` is a wrapper around `TacticM` with a read-only `SymContext` state -/
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

/-!
## WORKAROUND for https://github.com/leanprover/lean4/issues/5457
For some reason, `logWarning` is very slow to elaborate,
so we add a specialized `SymM.logWarning` with a specific instance of `MonadLog`
hidden behind a def. For some reason this is fast to elaborate.
-/

/-- This def may seem pointless, but it is in-fact load-bearing.

Furthermore, making it an `instance` will cause `logWarning` below to be
very slow to elaborate. Why? No clue. -/
protected def instMonadLog : MonadLog SymM := inferInstance

@[inherit_doc Lean.logWarning]
def logWarning (msg : MessageData) : SymM Unit :=
  @Lean.logWarning SymM _ SymM.instMonadLog _ _ msg

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
def findFromUserName (name : Name) : MetaM LocalDecl :=
  withInfoTraceNode m!"[findFromUserName] {name}" <| do
    let some decl := (← getLCtx).findFromUserName? name
      | throwError "Unknown local variable `{name}`"
    return decl

section MonadicGetters
variable {m} [Monad m] [MonadReaderOf SymContext m]

def getCurrentStateNumber : m Nat := do return (← read).currentStateNumber

/-- Return an expression of type
  `<finalState> = run <runSteps> <initialState>` -/
def getHRun : m Expr := do return (← read).hRun

/-- Return the `Name` of a variable of type
  `<finalState> = run <runSteps> <initialState>`

This will return the name of `hRun`, if its an fvar.
Otherwise, add a new variable to the local context, and return the new name.
Note that `hRun` is not modified in either case. -/
def getHRunName [MonadLiftT TacticM m] [MonadLiftT MetaM m] [MonadError m]
    [MonadLCtx m] :
    m Name := do
  let hRun ← getHRun
  if let Expr.fvar id := hRun then
    let some decl := (← getLCtx).find? id
      | throwError "Unknown fvar {Expr.fvar id}"
    return decl.userName
  else
    let ⟨_id, goal⟩ ← (← getMainGoal).note `h_run hRun none
    replaceMainGoal [goal]
    return `h_run

/-- Retrieve the name for the next state

NOTE: `getNextStateName` does not increment the state, so consecutive calls
will give the same name. Calling `prepareForNextStep` will increment the state.
-/
def getNextStateName : m Name := do
  let c ← read
  return Name.mkSimple s!"{c.state_prefix}{c.currentStateNumber + 1}"

end MonadicGetters

end

/-! ## `ToMessageData` instance and tracing -/

/-- Convert a `SymContext` to `MessageData` for tracing.
This is not a `ToMessageData` instance because we need access to `MetaM` -/
def toMessageData (c : SymContext) : MetaM MessageData := do
  return m!"\{ finalState := {c.finalState},
  runSteps? := {c.runSteps?},
  hRun := {c.hRun},
  program := {c.program},
  pc := {c.pc},
  state_prefix := {c.state_prefix},
  curr_state_number := {c.currentStateNumber},
  effects := {c.effects} }"

def traceSymContext : SymM Unit :=
  withTraceNode m!"SymContext: " <| do
    let m ← (← getThe SymContext).toMessageData
    trace[Tactic.sym] m

/-! ## Adding new simp theorems for aggregation -/

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

/-! ## Creating initial contexts -/

/-- Modify a `SymContext` with a monadic action `k : SymM Unit` -/
def modify (ctxt : SymContext) (k : SymM Unit) : TacticM SymContext := do
  let ((), ctxt) ← SymM.run ctxt k
  return ctxt

private def initial (state : Expr) : MetaM SymContext := do
  /- Create an mvar for the final state -/
  let finalState ← mkFreshExprMVar mkArmState
  /- Get the default simp lemmas & simprocs for aggregation -/
  let (aggregateSimpCtx, aggregateSimprocs) ←
    LNSymSimpContext
      (config := {decide := true, failIfUnchanged := false})
      (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules, `memory_rules])
  let aggregateSimpCtx := { aggregateSimpCtx with
    -- Create a new discrtree for effect hypotheses to be added to.
    -- TODO(@alexkeizer): I put this here, since the previous version kept
    -- a seperate discrtree for lemmas. I should run benchmarks to see what
    -- happens if we keep everything in one simpset.
    simpTheorems := aggregateSimpCtx.simpTheorems.push {}
  }
  return {
    finalState
    runSteps? := none
    hRun := ← mkFreshExprMVar none
    programInfo := {
      name := `dummyValue
      instructions := ∅
    }
    pc := 0
    aggregateSimpCtx,
    aggregateSimprocs,
    effects := AxEffects.initial state
  }

/-- Infer `state_prefix` and `curr_state_number` from the `state` name
as follows: if `state` is `s{i}` for some number `i` and a single character `s`,
then `s` is the prefix and `i` the number,
otherwise ignore `state`, log a warning, and start counting from `s1` -/
def inferStatePrefixAndNumber : SymM Unit := do
  let state ← AxEffects.getCurrentStateName
  let state := state.toString
  let tail := state.toSubstring.drop 1

  if let some currentStateNumber := tail.toNat? then
    modifyThe SymContext ({ · with
      state_prefix := (state.get? 0).getD 's' |>.toString,
      currentStateNumber })
  else
    SymM.logWarning m!"\
Expected state to be a single letter followed by a number, but found:
  {state}

Falling back to the default numbering scheme, \
with `s1` as the first new intermediate state"
    modifyThe SymContext ({ · with
      state_prefix := "s",
      currentStateNumber := 0 })

/-- Annotate any errors thrown by `k` with a local variable (and its type) -/
private def withErrorContext (name : Name) (type? : Option Expr) (k : MetaM α) :
    MetaM α :=
  try k catch e =>
    let h ← userNameToMessageData name
    let type := match type? with
      | some type => m!" : {type}"
      | none      => m!""
    throwErrorAt e.getRef "{e.toMessageData}\n\nIn {h}{type}"


/-- Build the lazy search structure (for use with `searchLCtx`)
to populate the `SymContext` state from the local context.

NOTE: some search might be performed eagerly. The resulting search structure
is tied to the specific `SymM` state and local context, it's expected that
neither of these change between construction and execution of the search. -/
protected def searchFor : SearchLCtxForM SymM Unit := do
  let c ← getThe SymContext
  let currentState ← AxEffects.getCurrentState

  /- We start by doing an eager search for `h_run`, outside the `SearchLCxtForM`
  monad. This is needed to instantiate the initial state -/
  let runSteps ← mkFreshExprMVar (Expr.const ``Nat [])
  let hRunType := h_run_type c.finalState runSteps currentState
  let some hRun ← findLocalDeclOfType? hRunType
    | throwNotFound hRunType

  let runSteps? ← reflectNatLiteral? runSteps
  if runSteps?.isNone then
    trace[Tactic.sym] "failed to reflect {runSteps} \
      (from {hRun.toExpr} : {hRun.type})"

  modifyThe SymContext ({ · with
    hRun := hRun.toExpr
    finalState := ←instantiateMVars c.finalState
    runSteps?
  })

  /-
  From here on out, we're building the lazy search patterns
  -/
  -- Find `h_program : <s>.program = <program>`
  let program ← mkFreshExprMVar none
  searchLCtxForOnce (h_program_type currentState program)
    (whenNotFound := throwNotFound)
    (whenFound := fun decl _ => do
      -- Register the program proof
      modifyThe AxEffects ({· with
        programProof := decl.toExpr
      })
      -- Assert that `program` is a(n application of a) constant
      let program := (← instantiateMVars program).getAppFn
      let .const program _ := program
        | throwError "Expected a constant, found:\n\t{program}"
      -- Retrieve the programInfo from the environment
      let some programInfo ← ProgramInfo.lookup? program
        | throwError "Could not find program info for `{program}`.\n\
            Did you remember to generate step theorems with:\n  \
              #generateStepEqTheorems {program}"
      modifyThe SymContext ({· with
        programInfo
      })
    )

  -- Find `h_pc : r .PC <s> = <pc>`
  let pc ← mkFreshExprMVar (← mkAppM ``BitVec #[toExpr 64])
  searchLCtxForOnce (h_pc_type currentState pc)
    (changeType := true)
    (whenNotFound := throwNotFound)
    (whenFound := fun decl _ => do
      let pc ← instantiateMVars pc
      -- Set the field effect
      AxEffects.setFieldEffect .PC {
        value := pc
        proof := decl.toExpr
      }
      -- Then, reflect the value
      let pc ← withErrorContext decl.userName decl.type <|
        reflectBitVecLiteral 64 pc
      modifyThe SymContext ({ · with pc })
    )

  -- Find `h_err : r .ERR <s> = .None`, or add a new subgoal if it isn't found
  searchLCtxForOnce (h_err_type currentState)
    (changeType := true)
    (whenFound := fun decl _ =>
      AxEffects.setErrorProof decl.toExpr
    )
    (whenNotFound := fun _ => do
      let errHyp ← mkFreshExprMVar (h_err_type currentState)
      replaceMainGoal [← getMainGoal, errHyp.mvarId!]
      AxEffects.setErrorProof errHyp
    )

  -- Find `h_sp : CheckSPAlignment <currentState>`.
  searchLCtxForOnce (h_sp_type currentState)
    (changeType := true)
    (whenNotFound := traceNotFound `Tactic.sym)
    -- ^^ Note that `h_sp` is optional, so there's no need to throw an error,
    --    we merely add a message to the trace and move on
    (whenFound := fun decl _ => do
      modifyThe AxEffects ({ · with
        stackAlignmentProof? := some decl.toExpr
      })
    )

  -- Find `r ?field currentState = ?value`
  -- NOTE: this HAS to come after the search for specific fields, like `h_pc`,
  --       or `h_err`, to ensure those take priority and the special handling
  --       of those fields gets applied.
  searchLCtxFor
    (expectedType := do
      let field ← mkFreshExprMVar (mkConst ``StateField)
      let value ← mkFreshExprMVar none
      return mkEqReadField field currentState value
    )
    (whenFound := fun decl ty => do
      let some (field, _state, value) := ty.eqReadField?
        | throwError "internal error: unexpected type:\n  {ty}"

      let field ← reflectStateField (← instantiateMVars field)
      AxEffects.setFieldEffect field {
        value := ←instantiateMVars value,
        proof := decl.toExpr
      }
      return .continu
    )
  /- TODO(@alexkeizer): Should we search for memory as well?
     Probably we can only do so after the memoryProof refactor -/
  return ()

/-- Build a `SymContext` by searching the local context of the main goal for
hypotheses of the required types (up-to defeq).
The local context is modified to unfold the types to be syntactically equal to
the expected types.

If an hypothesis `h_err : r <state> .ERR = None` is not found,
we create a new subgoal of this type.
-/
def fromMainContext (state? : Option Name) : TacticM SymContext := do
  let msg := m!"Building a `SymContext` from the local context"
  withTraceNode msg (tag := "fromMainContext") <| withMainContext' do
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

  -- We create a bogus initial context
  let c ← SymContext.initial stateExpr
  c.modify <| do
    searchLCtx SymContext.searchFor

    withMainContext' <| do
      let thms ← (← readThe AxEffects).toSimpTheorems
      modifyThe SymContext (·.addSimpTheorems thms)

      inferStatePrefixAndNumber

/-! ## Incrementing the context to the next state -/

/-- `prepareForNextStep` prepares the state for the next step of symbolic
evaluation:
  * `pc` is reflected from the stored `effects`
  * `runSteps?`, if specified, is decremented,
  * the `currentStateNumber` is incremented
-/
def prepareForNextStep : SymM Unit := do
  withInfoTraceNode "prepareForNextStep" (tag := "prepareForNextStep") <| do
    let pc ← do
      let { value, ..} ← AxEffects.getFieldM .PC
      try
        reflectBitVecLiteral 64 value
      catch err =>
        trace[Tactic.sym] "failed to reflect PC: {err.toMessageData}"
        pure <| (← getThe SymContext).pc + 4

    modifyThe SymContext (fun c => { c with
      pc
      runSteps?   := (· - 1) <$> c.runSteps?
      currentStateNumber := c.currentStateNumber + 1
    })
