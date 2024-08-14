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
      return some (Nat.toDigits 16 value.toNat).asString
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
    | BitVec.ofFin _ i => OptionT.run do
      let ⟨n, i⟩ ← getFinValue? i
      let n' := Nat.log2 n
      if h : n = 2^n' then
        return ⟨n', .ofFin (Fin.cast h i)⟩
      else
        failure
    | _ => Lean.Meta.getBitVecValue? e

/-- Given a ground term `e` of type `Nat`, fully reduce it,
and attempt to reflect it into a meta-level `Nat` -/
def reflectNatLiteral (e : Expr) : MetaM Nat := do
  if e.hasFVar then
    throwError "Expected a ground term, but {e} has free variables"

  let e' ← reduce (← instantiateMVars e)
  let some x := e'.rawNatLit?
    | throwError "Expected a numeric literal, found:\n\t{e'}
which was obtained by reducing:\n\t{e}"
  -- ^^ The previous reduction will have reduced a canonical-form nat literal
  --    into a raw literal, hence, we use `rawNatLit?` rather than `nat?`
  return x

/-- For a concrete width `w`,
reduce an expression `e` (of type `BitVec w`) to be of the form `?n#w`,
and then reflect `?n` to build the meta-level bitvector -/
def reflectBitVecLiteral (w : Nat) (e : Expr) : MetaM (BitVec w) := do
  if e.hasFVar then
    throwError "Expected a ground term, but {e} has free variables"

  if let some ⟨n, x⟩ ← _root_.getBitVecValue? e then
    if h : n = w then
      return x.cast h
    else
      throwError "Expected a bitvector of width {w}, but\n\t{e}\nhas width {n}"

  let x ← mkFreshExprMVar (Expr.const ``Nat [])
  let e' ← mkAppM ``BitVec.ofNat #[toExpr w, x]
  if (←isDefEq e e') then
    return BitVec.ofNat w (← reflectNatLiteral x)
  else
    throwError "Failed to unify, expected:\n\t{e'}\nbut found:\n\t{e'}"

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
    let some name ← findLocalDeclOfType? expectedType
      | throwError "Failed to find a local hypothesis of type {expectedType}"
    return name

/-- `findProgramHyp` searches the local context for an hypothesis of type
  `state.program = ?concreteProgram`,
asserts that `?concreteProgram` is indeed a constant (i.e., global definition),
then returns the decl of the local hypothesis and the name of the program.

Throws an error if no such hypothesis could. -/
def findProgramHyp (state : Expr) : MetaM (LocalDecl × Name) := do
  -- Try to find `h_program`, and infer `program` from it
  let program ← mkFreshExprMVar none
  let h_program_type ← mkEq (← mkAppM ``ArmState.program #[state]) program
  let h_program ← findLocalDeclOfTypeOrError h_program_type

  -- Assert that `program` is a(n application of a) constant, and find its name
  let program := (← instantiateMVars program).getAppFn
  let .const program _ := program
    |  -- withErrorContext h_run h_run_type <|
        throwError "Expected a constant, found:\n\t{program}"

  return ⟨h_program, program⟩
