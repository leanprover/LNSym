/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean
import Std.Data.HashMap

open Lean Meta

structure CSEState where
  /-- A map from expressions to variable ids plus a proof that the returned
  variable is equal to the original expression -/
  vars : Std.HashMap Expr (FVarId × Expr) := ∅
  /-- A counter to generate new names. -/
  gensymCount : Nat := 1
  deriving Repr, Inhabited

/-! ## Common Subexpression Elimination -/

variable {m} [Monad m] [MonadStateOf CSEState m]

/-- Generate a fresh variable name, incrementing the `genSymCount` -/
protected def CSEState.generateName : m Name :=
  modifyGet fun state =>
    let i := state.gensymCount
    let name := Name.mkSimple s!"x{i}"
    let state := { state with gensymCount := i + 1 }
    (name, state)

protected def CSEState.lookupVar? (e : Expr) : m (Option (FVarId × Expr)) := do
  return (← get).vars.get? e

protected def CSEState.insertVar (e : Expr) (x : FVarId) (h : Expr) : m Unit :=
  modify fun state => { state with
    vars := state.vars.insert e (x, h) }

open Elab.Tactic in
variable [MonadLiftT MetaM m] [MonadLiftT TacticM m] [MonadControlT MetaM m] in
/-- Given an expression, run the continuation `k` with a CSE'd expresion that is
equal to the original, as witnessed by the second argument.

Note that the returned expression is guaranteed to be well-formed in the
context of the main goal, which might've been modified and thus different from
the ambient context; a call to `withMainContext` might be needed.
We *do* guarantee that `k` is called with the right context.

This will lookup the expression in the CSEState, and if not found,
might add a new variable to the local context. Note that it is *not* guaranteed
that the returned expression is a variable.
The original expression could be returned as-is, for example,
if it is a literal. -/
def cseExpr (e : Expr) (k : Expr → Expr → m α) : m α := do
  -- if e.isFVar || !e.hasFVar then
    let h ← mkEqRefl e
    k e h
  -- else
  --   match ← CSEState.lookupVar? e with
  --   | some (x, h) => k (Expr.fvar x) h
  --   | none =>
  --       let type ← inferType e
  --       let mvar ← getMainGoal
  --       let name ← CSEState.generateName
  --       let mvar ← mvar.define name type e
  --       let ⟨x, mvar⟩ ← mvar.intro name
  --       replaceMainGoal [mvar]
  --       mvar.withContext <| do
  --         let xE := Expr.fvar x
  --         let h ← mkEqRefl xE
  --         CSEState.insertVar e x h
  --         k xE h
