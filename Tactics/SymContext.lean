/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean
import Arm.Exec

/-!
This files defines the `SymContext` structure,
which is collects
-/

open Lean Meta
open BitVec

/--

-/
structure SymContext where
  /-- `state` and `finalState` are local variable of type `ArmState` -/
  state : Name
  /-- `runSteps` is the number of steps that we can *maximally* simulate,
  because of the way it occurs in `h_run`.
  Note that `runSteps` is a meta-level natural number, reflecting the fact that we expect the number
  of steps in `h_run` to be expressed as a concrete literal -/
  runSteps : Nat
  /-- `h_run` is a local hypothesis of the form `finalState = run {runSteps} state` -/
  h_run : Name
  /-- `program` is a *constant* which represents the program being evaluated -/
  program : Name
  /-- `h_program` is a local hypothesis of the form `state.program = program` -/
  h_program : Name
  /-- `pc` is the *concrete* value of the program counter -/
  pc : BitVec 64
  /-- `h_pc` is a local hypothesis of the form `r StateField.PC state = pc` -/
  h_pc  : Name
  /-- `h_err` is a local hypothesis of the form `r StateField.ERR state = .None` -/
  h_err : Option Name
  /-- `h_sp` is a local hypothesis of the form `CheckSPAlignment state` -/
  h_sp  : Option Name

  /-- `state_prefix` is used together with `curr_state_number`
  to determine the name of the next state variable that is added by `sym` -/
  state_prefix      : String := "s"
  /-- `curr_state_number` is incremented each simulation step,
  and used together with `curr_state_number`
  to determine the name of the next state variable that is added by `sym`  -/
  curr_state_number : Nat := 0


namespace SymContext

/-! ## Creating initial contexts -/

/-- Infer `state_prefix` and `curr_state_number` from the `state` name as follows:
if `state` is `s{i}` for some number `i` and a single character `s`,
then `s` is the prefix and `i` the number,
otherwise simple take `{state}_` as the prefix and start counting from zero -/
def inferStatePrefixAndNumber (ctxt : SymContext) : SymContext :=
  let state := ctxt.state.toString
  let tail := state.toSubstring.drop 1

  if let some curr_state_number := tail.toNat? then
    { ctxt with
      state_prefix := (state.get? 0).getD 's' |>.toString,
      curr_state_number }
  else
    { ctxt with
      state_prefix := state ++ "_",
      curr_state_number := 0 }


private def reflectBitVecLiteral (w : Nat) (e : Expr) : MetaM (BitVec w) := do
  let x ← mkFreshExprMVar (Expr.const ``Nat [])
  let e' ← mkAppM ``BitVec.ofNat #[toExpr w, x]
  if !(←isDefEq e e') then
    throwError "Not def-eq:\n\t{e}\nand\n\t{e'}" -- TODO: error message
  else
    let x ← instantiateMVars x
    let some x := x.nat? | throwError "Not a nat:\n\t{x}" -- TODO: error message
    return BitVec.ofNat w x

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

  -- Find `h_run` and infer `runSteps` from it
  let sf ← mkFreshExprMVar none
  let runSteps ← mkFreshExprMVar (Expr.const ``Nat [])
  let h_run_type ← mkEq sf (←mkAppM ``run #[runSteps, stateExpr])
  let h_run ← findLocalDeclUsernameOfTypeOrError h_run_type

  -- Unwrap and reflect `runSteps`
  let some runSteps := (← instantiateMVars runSteps).nat?
    | throwError "Expected a numeric literal, found:\n\t{runSteps}\nIn\n\t {h_run} : {h_run_type}"

  -- At this point, `stateExpr` should have been assigned (if it was an mvar),
  -- so we can unwrap it to get the underlying name
  let stateExpr ← instantiateMVars stateExpr
  let state ← state?.getDM <| do
    let .fvar state := stateExpr
      | throwError
  "Expected a free variable, found:
    {stateExpr}
  We inferred this as the initial state because we found:
    {h_run} : {← instantiateMVars h_run_type}
  in the local context.

  If this is wrong, please explicitly provide the right initial state
  "
    let some state := lctx.find? state
      /- I don't expect this error to be possible in a well-formed state, but you never know -/
      | throwError "Failed to find local variable for state {stateExpr}"
    pure state.userName

  -- Try to find `h_program`, and infer `program` from it
  let program ← mkFreshExprMVar none
  let h_program_type ← mkEq (← mkAppM ``ArmState.program #[stateExpr]) program
  let h_program ← findLocalDeclUsernameOfTypeOrError h_program_type

  -- Assert that `program` is a(n application of a) constant, and find its name
  let program := (← instantiateMVars program).getAppFn
  let .const program _ := program
    | throwError "Expected a constant, found:\n\t{program}\nIn: {h_program} : {h_program_type}"
  /-
    TODO: assert that the expected `stepi` theorems have been generated for `program`
  -/

  -- Then, try to find `h_pc`
  let pc ← mkFreshExprMVar (← mkAppM ``BitVec #[toExpr 64])
  let h_pc_type ← mkEq (← mkAppM ``r #[(.const ``StateField.PC []), stateExpr]) pc
  let h_pc ← findLocalDeclUsernameOfTypeOrError h_pc_type

  -- Unwrap and reflect `pc`
  let pc ← instantiateMVars pc
  let pc ←
    try
      reflectBitVecLiteral 64 pc
    catch e =>
      throwError "{e.toMessageData}\nIn\n\t{h_pc} : {h_pc_type}"

  return inferStatePrefixAndNumber {
    state, h_run, runSteps, program, h_program, pc, h_pc,
    h_err := none,
    h_sp := none,
  }
where
  findLocalDeclUsernameOfType? (expectedType : Expr) : MetaM (Option Name) := do
    let some h_run ← findLocalDeclWithType? expectedType
      | return none
    let decl := (← getLCtx).get! h_run
    return decl.userName
  findLocalDeclUsernameOfTypeOrError (expectedType : Expr) : MetaM Name := do
    let some name ← findLocalDeclUsernameOfType? expectedType
      | throwError "Failed to find a local hypothesis of type {expectedType}"
    return name

/-- `mkName` is a simple helper for turning a string into an unqualified name,
as used for local variables and hypotheses -/
private def mkName : String → Name :=
  Lean.Name.mkStr Lean.Name.anonymous

def default (curr_state_number : Nat) : SymContext :=
  let s := s!"s{curr_state_number}"
  {
    state     := mkName s
    h_run     := mkName s!"h_run"
    h_program := mkName s!"h_{s}_program"
    h_pc      := mkName s!"h_{s}_pc"
    h_err     := mkName s!"h_{s}_err"
    h_sp      := mkName s!"h_{s}_sp"
    /-
      `runSteps`, `pc` and `program` actually require inspection of the context to determine.
      However, these values are not actually used yet,
      they are merely kept because they will be useful in the future.
      We can safely put in bogus values for now.
      (Or we could do the honest thing and make these `Option`s)
    -/
    runSteps  := 9999999999
    program   := `UNUSED
    pc        := 0#64
  }

/-! ## Incrementing the context to the next state -/

/-- `c.nextState` generates names for the next intermediate state in symbolic evaluation.

`nextPc?`, if given, will be the pc of the next context.
If `nextPC?` is `none`, then the previous pc is incremented by 4
 -/
def nextState (c : SymContext) (nextPc? : Option (BitVec 64) := none) : SymContext :=
  let curr_state_number := c.curr_state_number + 1
  let s := s!"{c.state_prefix}{curr_state_number}"
  {
    state     := mkName s
    h_run     := c.h_run
    h_program := mkName s!"h_{s}_program"
    h_pc      := mkName s!"h_{s}_pc"
    h_err     := mkName s!"h_{s}_err"
    h_sp      := mkName s!"h_{s}_sp"
    runSteps  := c.runSteps - 1
    program   := c.program
    pc        := nextPc?.getD (c.pc + 4#64)
    curr_state_number
    state_prefix := c.state_prefix
  }

/-! ## Simple projections -/
open Lean (Ident mkIdent)

def state_ident     (c : SymContext) : Ident := mkIdent c.state
def h_run_ident     (c : SymContext) : Ident := mkIdent c.h_run
def h_program_ident (c : SymContext) : Ident := mkIdent c.h_program
def h_pc_ident      (c : SymContext) : Ident := mkIdent c.h_pc
def h_err_ident     (c : SymContext) : Option Ident := mkIdent <$> c.h_err
def h_sp_ident      (c : SymContext) : Option Ident := mkIdent <$> c.h_sp
