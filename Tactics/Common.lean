/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

import Lean
import Arm.Exec
open Lean Elab Tactic Expr Meta
open BitVec

def addToSimpExt (declName : Name) (simp_ext : Name) : MetaM Unit := do
  let some ext ← getSimpExtension? simp_ext |
    throwError "Simp Extension [simp_ext] not found!"
  addSimpTheorem ext declName false false Lean.AttributeKind.global default

/- Obtain `List α` from `List (Option α)` by discarding any `none`
elements. -/
def optionListtoList (xs : List (Option α)) : List α :=
  List.foldl (fun acc val =>
    match val with
    | none => acc
    | some v => acc.append [v])
  [] xs

/- Obtain `Array α` from `Array (Option α)` by discarding any `none`
elements. -/
def optionArraytoArray (array : Array (Option α)) : Array α :=
  Array.foldl (fun acc val =>
    match val with
    | none => acc
    | some v => acc.append #[v])
  #[] array

/- Find all declarations in the `LocalContext` whose username begins
with `pfxUserName`. -/
def filterDeclsWithPrefix (lctx : LocalContext) (pfxUserName : Name)
  : (Array LocalDecl) :=
  optionArraytoArray
  (PersistentArray.toArray
    (PersistentArray.filter
      lctx.decls
      (fun decl =>
        match decl with
          | none      => false
          | some decl => String.isPrefixOf (toString pfxUserName)
                                           (toString decl.userName))))

/- Get the string representation of `e` if it denotes a bitvector
literal. The bitvector's width is not represented in the resulting
string. -/
def getBitVecString? (e : Expr) (hex : Bool := false): MetaM (Option String) := do
  let maybe_e_literal ← getBitVecValue? e
  match maybe_e_literal with
  | some ⟨_, value⟩ =>
    if hex then
      -- We don't want leading zeroes here.
      return some value.toHexWithoutLeadingZeroes
    else
      return some (ToString.toString value.toNat)
  | none => return none

/- Get the string representation of `e` if it denotes a `PFlag`. -/
def getPFlagString? (e : Expr) : MetaM (Option String) := OptionT.run do
  match_expr e with
  | PFlag.N => return "n_flag"
  | PFlag.Z => return "z_flag"
  | PFlag.C => return "c_flag"
  | PFlag.V => return "v_flag"
  | _       => panic! s!"[getPFlagString?] Unexpected expression: {e}"

/- Get the string representation of `e` if it denotes a `StateField`. -/
def getStateFieldString? (e : Expr) : MetaM (Option String) := OptionT.run do
  match_expr e with
  | StateField.GPR iExpr  => return ("x" ++ (← getBitVecString? iExpr))
  | StateField.SFP iExpr  => return ("q" ++ (← getBitVecString? iExpr))
  | StateField.PC         => return "pc"
  | StateField.FLAG pExpr => getPFlagString? pExpr
  | StateField.ERR        => return "err"
  | _                     => panic! s!"[getStateFieldName?] Unexpected expression: {e}"

/-! ## Reflection of literals (possibly after reduction) -/

/-- A wrapper around `Lean.Meta.getBitVecValue?`
that additionally recognizes:
- a `BitVec.ofFin (Fin.mk _ _)` application (which is the raw normal form)
-/
-- TODO: should this be upstreamed to core?
def getBitVecValue? (e : Expr) : MetaM (Option ((n : Nat) × BitVec n)) :=
  match_expr e with
    | BitVec.ofFin w i => OptionT.run do
      let w ← getNatValue? w
      let v ← do
        match_expr i with
          | Fin.mk _n v _h  => getNatValue? v
          | _               => pure (← getFinValue? i).2.val
      return ⟨w, BitVec.ofNat w v⟩
    | _ => Lean.Meta.getBitVecValue? e

/-- Given a ground term `e` of type `Nat`, fully reduce it,
and attempt to reflect it into a meta-level `Nat`,
returning `none` on failure -/
partial def reflectNatLiteral? (e : Expr) : MetaM (Option Nat) := OptionT.run do
  let e' ← instantiateMVars e
  go e'
where go (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  if let some n ← evalNat e then
    return n

  let_expr Nat.succ e' := e | return none
  let some n ← go e'        | return none
  return some (n + 1)

/-- Given a ground term `e` of type `Nat`, fully reduce it,
and attempt to reflect it into a meta-level `Nat`,
throwing an error on failure -/
def reflectNatLiteral (e : Expr) : MetaM Nat := do
  if e.hasFVar then
    throwError "Expected a ground term, but {e} has free variables"
  let some n ← reflectNatLiteral? e
    | throwError "Failed to reflect expression into a `Nat` literal:\n  {e}"
  return n


/-- For a concrete width `w`,
reduce an expression `e` (of type `BitVec w`) to be of the form `?n#w`,
and then reflect `?n` to build the meta-level bitvector -/
def reflectBitVecLiteral (w : Nat) (e : Expr) : MetaM (BitVec w) := do
  if e.hasFVar || e.hasMVar then
    throwError "Expected a ground term, but {e} has free variables"

  let some ⟨n, x⟩ ← _root_.getBitVecValue? e
    | throwError "Failed to reflect:\n\t{e}\ninto a BitVec"

  if h : n = w then
    return x.cast h
  else
    throwError "Expected a bitvector of width {w}, but\n\t{e}\nhas width {n}"

def reflectPFLag (e : Expr) : MetaM PFlag :=
  match_expr e with
    | PFlag.N => pure .N
    | PFlag.Z => pure .Z
    | PFlag.C => pure .C
    | PFlag.V => pure .V
    | _ =>
      let pflag := mkConst ``PFlag
      throwError "Expected a `{pflag}` constructor, found:\n  {e}"

/-- Reflect a concrete `StateField` -/
def reflectStateField (e : Expr) : MetaM StateField :=
  match_expr e.consumeMData with
    | StateField.GPR x  => StateField.GPR <$> reflectBitVecLiteral _ x
    | StateField.SFP x  => StateField.SFP <$> reflectBitVecLiteral _ x
    | StateField.PC     => pure StateField.PC
    | StateField.FLAG f => StateField.FLAG <$> reflectPFLag f
    | StateField.ERR    => pure StateField.ERR
    | _ =>
      let sf := mkConst ``StateField
      throwError "Expected a `{sf}` constructor, found:\n  {e}"

/-! ## Hypothesis types -/
namespace SymContext

/-- `h_run_type state` returns an Expr for
`<finalState> = run <steps> <initialState>`, the expected type of `h_run` -/
def h_run_type (finalState steps initialState : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1])
    (mkConst ``ArmState)
    finalState
    (mkApp2 (mkConst ``_root_.run) steps initialState)

/-- `h_err_type state` returns an Expr for `r .ERR <state> = .None`,
the expected type of `h_err` -/
def h_err_type (state : Expr) : Expr :=
  mkAppN (mkConst ``Eq [1]) #[
    mkConst ``StateError,
    mkApp2 (.const ``r []) (.const ``StateField.ERR []) state,
    .const ``StateError.None []
  ]

/-- `h_sp_type state` returns an Expr for `CheckSPAlignment <state>`,
the expected type of `h_sp` -/
def h_sp_type (state : Expr) : Expr :=
  mkApp (.const ``CheckSPAlignment []) state

/-- `h_sp_type state` returns an Expr for `<state>.program = <program>`,
the expected type of `h_program` -/
def h_program_type (state program : Expr) : Expr :=
  mkAppN (mkConst ``Eq [1]) #[
    mkConst ``Program,
    mkApp (mkConst ``ArmState.program) state,
    program
  ]

/-- `h_pc_type state` returns an Expr for `r .PC <state> = <address>`,
the expected type of `h_pc` -/
def h_pc_type (state address : Expr) : Expr :=
  mkAppN (mkConst ``Eq [1]) #[
    mkApp (mkConst ``BitVec) (toExpr 64),
    mkApp2 (mkConst ``r) (mkConst ``StateField.PC) state,
    address
  ]

end SymContext

/-! ## Local Context Search -/

/-- Attempt to look-up a `name` in the local context,
so that we can build an expression with its fvarid,
to return a message with nice highlighting.
If lookup fails, we return a message with the plain name, wihout highlighting -/
def userNameToMessageData (name : Name) : MetaM MessageData := do
  return match (← getLCtx).findFromUserName? name with
    | some decl => m!"{Expr.fvar decl.fvarId}"
    | none      => m!"{name}"

def findLocalDeclOfType? (expectedType : Expr) : MetaM (Option LocalDecl) := do
    let fvarId ← findLocalDeclWithType? expectedType
    return ((← getLCtx).get! ·) <$> fvarId
    -- ^^ `findLocalDeclWithType?` only returns `FVarId`s which are present in
    --    the local context, so we can safely pass it to `get!`

def findLocalDeclOfTypeOrError (expectedType : Expr) : MetaM LocalDecl := do
    let some decl ← findLocalDeclOfType? expectedType
      | throwError "Failed to find a local hypothesis of type {expectedType}"
    return decl

/-- `findProgramHyp` searches the local context for an hypothesis of type
  `state.program = ?concreteProgram`,
asserts that `?concreteProgram` is indeed a constant (i.e., global definition),
then returns the decl of the local hypothesis and the name of the program.

Throws an error if no such hypothesis could. -/
def findProgramHyp (state : Expr) : MetaM (LocalDecl × Name) := do
  -- Try to find `h_program`, and infer `program` from it
  let program ← mkFreshExprMVar none
  let h_program_type := SymContext.h_program_type state program
  let h_program ← findLocalDeclOfTypeOrError h_program_type

  -- Assert that `program` is a(n application of a) constant, and find its name
  let program := (← instantiateMVars program).getAppFn
  let .const program _ := program
    | throwError "Expected a constant, found:\n\t{program}"

  return ⟨h_program, program⟩

/-! ## Expr Builders -/

/-- Return the expression for `ArmState` -/
def mkArmState : Expr := mkConst ``ArmState

/-- Return `x = y`, given expressions `x` and `y` of type `ArmState` -/
def mkEqArmState (x y : Expr) : Expr :=
  mkApp3 (.const ``Eq [1]) mkArmState x y

/-- Return a proof of type `x = x`, where `x : ArmState` -/
def mkEqReflArmState (x : Expr) : Expr :=
  mkApp2 (.const ``Eq.refl [1]) mkArmState x

/-- Return `x = y` given expressions `x, y : StateField <field>` -/
def mkEqStateValue (field x y : Expr) : Expr :=
  let ty := mkApp (mkConst ``state_value) field
  mkApp3 (.const ``Eq [1]) ty x y

/-- Return `r <field> <state> = <value>` -/
def mkEqReadField (field state value : Expr) : Expr :=
  let r := mkApp2 (mkConst ``r) field state
  mkEqStateValue field r value

/-- If expression `e` is `r ?field ?state = ?value`, return
`some (field, state, value)`, else return `none` -/
def Lean.Expr.eqReadField? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (_ty, lhs, value) ← e.eq?
  let_expr r field state := lhs
    | none
  some (field, state, value)

/-! ## Tracing helpers -/

def traceHeartbeats (cls : Name) (header : Option String := none) :
    MetaM Unit := do
  let header := (header.map (· ++ ": ")).getD ""
  let heartbeats ← IO.getNumHeartbeats
  let percent ← heartbeatsPercent
  trace cls fun _ =>
    m!"{header}used {heartbeats} heartbeats ({percent}% of maximum)"

/-! ## `withMainContext'` -/

variable {m} [Monad m] [MonadLiftT TacticM m] [MonadControlT MetaM m] in
/-- Execute `x` using the main goal local context and instances.

Unlike the standard `withMainContext`, `x` may live in a generic monad `m`. -/
def withMainContext' (x : m α) : m α := do
  (← getMainGoal).withContext x

/-- An emoji to show that a tactic is processing at an intermediate step. -/
def processingEmoji : String := "⚙️"
