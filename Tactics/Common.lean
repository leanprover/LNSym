/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

import Lean
import Arm.Exec
open Lean Elab Tactic Expr Meta
open BitVec

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
