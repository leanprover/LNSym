/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean
import Tactics.QuoteLight.ToExpr

open Lean Meta Elab.Term

namespace QuoteLight

/-- `QL α` is a Lean `Expr` of type `α`, see the `ql(..)` and `QL(..)` macros
for

It's primary utility is to serve as machine-checked documentation of the
expected type of expressions. However, the index is *not* actually checked,
so it is entirely possible to construt  -/
@[pp_using_anonymous_constructor]
structure QL (α : Expr) where
  ofExpr :: toExpr : Expr
deriving Inhabited

attribute [coe] QL.toExpr
instance : CoeOut (QL α) Expr := ⟨QL.toExpr⟩

/-- Given a closed term `t` of type `α` (i.e., `t` may not have free or meta variables) ,
`ql(<t>)` will construct a Lean expression that represents `t`.
You can think of it as a more powerful version of `ToExpr.toExpr`.

For example, `ql(Nat)` will return the expression `.const ``Nat []`, and
`ql(BitVec 64)` gives the same expression as
  `.app (.const ``BitVec []) (toExpr 64)`
-/
elab "ql(" t:term ")" : term <= expectedType? => do
  let t ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let t ← instantiateMVars t

  if t.hasFVar then
    throwError "error: expression has free variables:\n  {t}\n\n\
      ql only supports constant expressions"
  else if t.hasMVar then
    throwError "error: expression has meta variables:\n  {t}\n\n\
      ql only supports constant expressions"

  let expr := toExpr t
  if expectedType? == Expr.const ``Expr [] then
    /- If the exected type is `Expr`, then we output just the raw expression,
       circumventing the need to apply the `QL` to `Expr` coercion.
       This makes the result slightly cleaner. -/
    return expr
  else
    let ty ← inferType t
    let exprTy := toExpr ty
    return mkApp2 (mkConst ``QL.ofExpr) exprTy expr

/-- `QL(<t>)` returns `QL ql(<t>)`.

For example, `QL(BitVec 64)` is the type of Lean expressions of type `BitVec 64`.
-/
macro "QL(" t:term ")" : term => `(QL ql($t))

-- TODO: write a delaborator that delaborates applications of `QL` into
--       the `QL(...)` macro for better readability

/-!
## Simple Tests
-/
section Test

-- Basic check to ensure synthetic mvars get synthesized properly
/--
info: ⟨(Expr.const `List [Level.zero]).app
    ((Expr.const `BitVec []).app
      ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 64))).app
        ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 64)))))⟩ : QL (Expr.sort Level.zero.succ)
-/
#guard_msgs in #check ql(List (BitVec 64))

-- Basic test for `QL(..)` macro
/--
info: QL
  ((Expr.const `List [Level.zero]).app
    ((Expr.const `BitVec []).app
      ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 64))).app
        ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 64)))))) : Type
-/
#guard_msgs in #check QL(List (BitVec 64))

-- Test that bound variables are handled properly
/--
info: ⟨Expr.lam `n (Expr.const `Nat []) ((Expr.const `BitVec []).app (Expr.bvar 0))
    BinderInfo.default⟩ : QL (Expr.forallE `n (Expr.const `Nat []) (Expr.sort Level.zero.succ) BinderInfo.default)
-/
#guard_msgs in #check ql(fun n => BitVec n)

-- Test that free variables are rejected
/--
error: error: expression has free variables:
  BitVec n

ql only supports constant expressions
-/
#guard_msgs in variable (n : Nat) in #check ql(BitVec n)

end Test

end QuoteLight
