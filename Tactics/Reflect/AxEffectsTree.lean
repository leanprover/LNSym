/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Reflect.AxEffects

open Lean Meta


/-- An `AxEffectsTree` adds support for `if-then-else` constructs,
by constructing a tree of `AxEffects`.

Note that all leaves are assumed to have the same initial and current states,
so we store those at the root of the tree -/
protected inductive AxEffectsTree.Base
  /--
  A node in an `AxEffectTree` represents an `if-then-else`, by
  storing a lean expression for the condifion, a left subtree
  which describes the effects assuming the condition is true, and
  a right subtree to describe the effects assuming the condition is false.
  Both subtrees may depend on a proof of the condition being true (resp, false),
  which is stored as a loose bvar. See `AxEffectsTree.fromExpr` for more detail
  -/
  | node (cond : Expr) (thenEff : AxEffectsTree.Base) (elseEff : AxEffectsTree.Base)
  /-- A leaf in an `AxEffectsTree` is simply an instance of `AxEffects` -/
  | leaf (effects : AxEffects.Base)

@[inherit_doc AxEffectsTree.Base]
structure AxEffectsTree where
  /-- `base` stores the tree of conditions, and relevant effects -/
  base : AxEffectsTree.Base
  /-- The initial state -/
  initialState : Expr
  /-- The current state, which may be expressed in either the "exploded form"
  (a sequence of `w`/`write_mem` to the initial state), or as just a variable
  which is (propositionally) equal to that exploded form -/
  currentState : Expr

-- TODO: When checking the `SPAlignment` we don't really care about the else
-- branch -- it throws an error.
-- We could consider an optimization where the `elseEff` stores an `Option`,
-- with `none` indicating that the semantics are malformed when the condition
-- is not true


/-! ## AxEffectsTree  -/

open AxEffects (mkWriteMemBytes mkW)

namespace AxEffectsTree

/-- An initial `AxEffectsTree` which has no writes and no conditions.
That is, the tree only has a single leaf and the given `state` is assigned to be
both the initial and the current state -/
def initial (state : Expr) : AxEffectsTree where
  base          := .leaf (.initial state)
  initialState  := state
  currentState  := state

/-- Map a function over all leaf `AxEffects` in an `AxEffectsTree` -/
def Base.mapM [Monad m] (f : AxEffects.Base → m AxEffects.Base) :
    AxEffectsTree.Base → m AxEffectsTree.Base
  | node cond t e => do return node cond (← mapM f t) (← mapM f e)
  | leaf eff      => do return leaf (← f eff)

/-! ## Tracing -/

def Base.trace (eff : AxEffectsTree.Base) :
    MetaM Unit := do
  match eff with
    | leaf eff      =>
        trace[Tactic.sym] "leaf:\n{eff}"
    | node cond t e =>
        trace[Tactic.sym] "node:\n  cond := {cond}"
        withTraceNode `Tactic.Sym (fun _ => pure m!"then-branch") t.trace
        withTraceNode `Tactic.Sym (fun _ => pure m!"then-branch") e.trace

def trace (eff : AxEffectsTree) (header : MessageData := m!"effects tree") :
    MetaM Unit :=
  withTraceNode `Tactic.sym (fun _ => pure header) <| do
    trace[Tactic.sym] "initialState := {eff.initialState}\n\
      currentState := {eff.currentState}"
    eff.base.trace

/-! ## Updates -/

/-- Execute `write_mem <n> <addr> <val>` against all states stored in `eff`
That is, `currentState` of all leaves of the returned tree will be
  `write_mem <n> <addr> <val> <eff.currentState>`
and all other fields are updated accordingly. -/
private def updateWriteMem (n addr val : Expr) (eff : AxEffectsTree) :
    MetaM AxEffectsTree := do
  let base ← eff.base.mapM (·.updateWriteMem n addr val eff.currentState)
  return {
    base,
    currentState := mkWriteMemBytes n addr val eff.currentState
    initialState := eff.initialState
  }

/-- Execute `w <fld> <val>` against the state stored in `eff`
That is, `currentState` of all leaves of the returned tree will be
  `w <fld> <val> <eff.currentState>`
and all other fields are updated accordingly. -/
private def updateW (eff : AxEffectsTree) (fld val : Expr) :
    MetaM AxEffectsTree := do
  let field ← reflectStateField fld
  let base ← eff.base.mapM (·.updateW field val eff.currentState)
  return {
    base,
    currentState := mkW fld val eff.currentState
    initialState := eff.initialState
  }

/-- Given a proof `eq : s = <currentState>`,
set `s` to be the new `currentState`, and update all proofs accordingly -/
def adjustCurrentStateWithEq (eff : AxEffectsTree) (s eq : Expr) :
    MetaM AxEffectsTree := do
  withTraceNode `Tactic.sym (fun _ => pure "adjusting `currentState`") do
    trace[Tactic.sym] "rewriting along {eq}"
    assertHasType eq <| mkEqArmState s eff.currentState

    let eq ← mkEqSymm eq
    let base ← eff.base.mapM (·.adjustCurrentStateWithEq eq)
    return { eff with
      base
      currentState := s
    }

/-- Return an `AxEffectsTree` whose `currentState` is
  `if <cond> then <eff.currentState> else ?_`
Where the Lean bvar with index `depth` is assumed to contain a proof that the
condition `cond` is true -/
def updateIteThen (depth : Nat) (cond : Expr) (eff : AxEffectsTree) :
    MetaM AxEffectsTree := do
  let elseState ← mkFreshExprMVar mkArmState
  let instDecidable ← mkFreshExprMVar (mkApp (mkConst ``Decidable) cond)

  let currentState := -- `if <cond> then <currentState> else ?_`
    mkAppN (.const ``ite [1]) #[
      mkArmState, cond, instDecidable, eff.currentState, elseState
    ]
  let hEq := -- hEq : `if <cond> then <currentState> else ?_ = <currentState>`
    mkAppN (.const ``ite_cond_eq_true [1]) #[
      mkArmState, cond, instDecidable, eff.currentState, elseState, .bvar depth
    ]

  eff.adjustCurrentStateWithEq hEq currentState

/-- Return an `AxEffectsTree` whose `currentState` is
  `if <cond> then ?_ else <eff.currentState>`
Where the Lean bvar with index `depth` is assumed to contain a proof that the
condition `cond` is false -/
def updateIteElse (depth : Nat) (cond : Expr) (eff : AxEffectsTree) :
    MetaM AxEffectsTree := do
  let thenState ← mkFreshExprMVar mkArmState
  let instDecidable ← mkFreshExprMVar (mkApp (mkConst ``Decidable) cond)

  let currentState := -- `if <cond> then ?_ else <currentState>`
    mkAppN (.const ``ite [1]) #[
      mkArmState, cond, instDecidable, thenState, eff.currentState
    ]
  let hEq := -- hEq : `if <cond> then ?_ else <currentState> = <currentState>`
    mkAppN (.const ``ite_cond_eq_false [1]) #[
      mkArmState, cond, instDecidable, thenState, eff.currentState, .bvar depth
    ]

  eff.adjustCurrentStateWithEq hEq currentState

/-- Add a node the `AxEffectsTree`, such that the resulting `currentState` is
  `if <cond> then <t.currentState>` else `<e.currentState>` -/
def updateIte (depth : Nat) (cond : Expr) (t e : AxEffectsTree) :
    MetaM AxEffectsTree := do
  let t ← updateIteThen depth cond t
  let e ← updateIteElse depth cond e

  assertIsDefEq t.initialState e.initialState
  assertIsDefEq t.currentState e.currentState
  return {
    base := .node cond t.base e.base
    initialState := t.initialState
    currentState := t.currentState
  }


-- TODO: thoroughly update all docstrings of `Tree` ops

/-! ## fromExpr / fromEq -/

/-- Given an expression `e : ArmState`,
which is a sequence of `w`/`write_mem`s to the some state `s`,
return an `AxEffects` where `s` is the intial state, and `e` is `currentState`.

Note that as soon as an unsupported expression (e.g., an `if`) is encountered,
the whole expression is taken to be the initial state,
even if there might be more `w`/`write_mem`s in sub-expressions. -/
partial def fromExpr (e : Expr) (depth : Nat := 0) : MetaM AxEffectsTree := do
  let msg := m!"Building effects with writes from: {e}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do match_expr e with
    | write_mem_bytes n addr val e =>
        let eff ← fromExpr e
        eff.updateWriteMem n addr val

    | w field value e =>
        let eff ← fromExpr e
        eff.updateW field value

    | ite _α cond _instDecidable t e =>
        let t ← fromExpr t (depth + 1)
        let e ← fromExpr e (depth + 1)
        updateIte depth cond t e

    | _ =>
        return .initial e

/-- Given a proof `eq : ?s = <sequence of w/write_mem/ifs to ?s0>`,
where `?s` and `?s0` are arbitrary `ArmState`s,
return an `AxEffectsTree` where each leaf has `?s0` as the initial state,
and `?s` as the current state

Buils upon `AxEffects.fromEq` to add support for `if-then-else` constructs.
-/
def fromEq (eq : Expr) : MetaM AxEffectsTree :=
  let msg := m!"Building effects with equality: {eq}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    let s ← mkFreshExprMVar mkArmState
    let rhs ← mkFreshExprMVar mkArmState
    assertHasType eq <| mkEqArmState s rhs

    let eff ← fromExpr (← instantiateMVars rhs)
    let eff ← eff.adjustCurrentStateWithEq s eq
    eff.trace "new state"
    return eff

/-! ## Accessors -/

/-- Assuming that an `AxEffectsTree` is just a leaf, we can convert it into
a plain `AxEffects`.
Returns `none` if the argument is a node -/
def getLeaf? : AxEffectsTree → Option AxEffects
  | ⟨.leaf eff, initialState, currentState⟩ =>
      some {eff with initialState, currentState}
  | _ => none
