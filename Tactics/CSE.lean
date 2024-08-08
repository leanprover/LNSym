/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

This file contains an implementation of a common subexpression elimination pass,
used to simplify goal states.
-/
import Lean
import Tactics.Attr
import Lean.Meta.Tactic.Generalize
open Lean Elab Tactic Expr Meta

/-- An emoji for when we are processing or trying. -/
def tryEmoji : String := "⌛"

/-! ### Common Subexpression Eliminiation Tactic

cse ⊢
cse ⊢ h h' -- will use all expressions to compute thresholds.

#### TODO

- don't generalize over implicits.
- don't generalize over stuff that's hidden by notation?

#### Algorithm:

- step 1: collect statistics on (sub) expression occurrence in the target expression.
- step 2: once again, working bottom up, call `generalize` for each of these, generating appropriate generalize names.
- step 3: done?
-/

section HashMapUtils

def Lean.HashMap.insertOrUpdate [BEq α] [Hashable α] (h : HashMap α β) (k : α) (v : β) (f : β → β) : (β × HashMap α β) :=
  match h.find? k with
  | .none => (v, h.insert k v)
  | .some v => let v' := (f v); (v', h.insert k v')

end HashMapUtils

namespace Tactic.CSE

inductive ShouldGeneralizeTypes
| generalizeTypes
| generalizeOnlyTerm

inductive ShouldProcessHyps
| ignoreHyps
| allHyps
deriving DecidableEq

structure CSEConfig where
  /-- Whether we should process the hypotheses of the current goal state. -/
  processHyps : ShouldProcessHyps := .ignoreHyps
  /-- Whether we should also be performing CSE on types, or only terms. -/
  types : ShouldGeneralizeTypes := .generalizeOnlyTerm
   /-- The minimum number of references necessary to perform CSE on a term. -/
  minRefsToCSE : Nat := 2

inductive ExprRef
| const (e : Expr) (he : e.isConst)
| app (f : Nat) (x : Nat) -- references.
| fvar (e : Expr) (he : e.isFVar)

/-- TODO: index the key by the expression. -/
structure ExprData where
  /-- Number of references to this expression -/
  refs : Nat
  /-- Size of the expression, disregarding implicits? -/
  size : Nat
deriving Repr

def ExprData.incrRef (data : ExprData) : ExprData :=
  { data with refs := data.refs + 1 }


structure State where
  /-
  A mapping from expression to its canonical index.
  -/
  canon2data : HashMap Expr ExprData := {}
  /-
  an array of expressions, whose order tells us the time they were inserted into the CSE map.
  Since we insert expressions from child to parent, expressions that come later must be parents of expressions that come earlier.
  -/
  insertionTime2Expr : Array Expr := #[]
  /-
  a counter to generate new names
  -/
  gensymCount : Nat := 1

instance : ToMessageData State where
  toMessageData s := Id.run do
    let mut msg := m!""
    for (k, v) in s.canon2data.toArray do
      msg := msg ++ Format.line ++ m!"{k} := {repr v}"
    msg

abbrev CSEM := StateRefT State (ReaderT CSEConfig TacticM)

/-- Get the configuration. -/
def getConfig : CSEM CSEConfig := read

/-- Get the mutable state. -/
def getState : CSEM State := get

/-- Get the mutable state. -/
def setState : State → CSEM Unit := set

def CSEM.run (val : CSEM α) (config : CSEConfig) : TacticM α :=
   val.run' {} |>.run config

-- @bollu: Surely we must have an implementation of this.
private def Array.replicate (n : Nat) (v : α) : Array α := List.replicate n v |>.toArray

/--
The size of an expression, according to the CSE heuristic.
The function is `partial` because the lean termination checker does not understand `match_expr`.
We use the `CSEM` to have access to `Environment`, such that we can ignore implicit arguments.
-/
partial def CSEM.exprSize (e : Expr) : CSEM Nat := do
  match_expr e with
  | OfNat.ofNat _α x _inst  => if x.isRawNatLit then return 1 else exprSize x -- @OfNat.ofNat Nat 1 (instOfNatNat 1)
  | _ =>
    if e.isApp then
      let (fn, args) := (e.getAppFn, e.getAppArgs)
      let paramInfos := (← getFunInfo fn).paramInfo
      let mut size := 1
      for i in [0 : args.size] do
        let arg := args[i]!
        let shouldCount := paramInfos[i]!.isExplicit
        if shouldCount then
          size := size + (← exprSize arg)
      return size
    else return 1

def ExprData.new (e : Expr) : CSEM ExprData := do return {
  refs := 1,
  size := (← CSEM.exprSize e)
}



/-- decides if performing CSE for this expression is profitable. -/
def ExprData.isProfitable? (data : ExprData) : CSEM Bool :=
  return data.size > 1 && data.refs >= (← getConfig).minRefsToCSE

-- x : Nat
-- Nat : Type
-- Eq _ _ : Prop
-- We probably want to give types whose terms should be CSE'd.
-- The function is partial because of the region via e.getAppArgs |>.forM tryAddExpr
partial def CSEM.tryAddExpr (e : Expr) : CSEM (Option ExprData) := do
  let t ← inferType e
  -- for now, we ignore function terms.
  let relevant? := !t.isArrow && !t.isSort && !t.isForall
  trace[Tactic.cse.collection] m!"{if relevant? then checkEmoji else crossEmoji} ({e}):({t})"

  /-
  If we have an application, then only add its children
  that are explicit.

  -/
  let mut size := 1
  if e.isApp then
    let (fn, args) := (e.getAppFn, e.getAppArgs)
    let paramInfos := (← getFunInfo fn).paramInfo
    for i in [0 : args.size] do
      let arg := args[i]!
      let shouldCount := paramInfos[i]!.isExplicit
      if shouldCount then
        if let .some argData ← tryAddExpr arg then
          size := size + 1
  -- the current argument itself was irrelelvannt, so don't bother adding it.
  if !relevant? then return .none
    -- else
    -- TODO: check if we still need the OfNat.ofNat workaround.
    -- match_expr e with
    -- | OfNat.ofNat _α x _inst  => size := 1
  let s ← getState
  match s.canon2data.find? e with
  | .some data => do
    let data := data.incrRef
    trace[Tactic.cse.collection] m!"updated '{e}' with info '{repr data}'" -- TODO: make this a trace node child.
    setState { s with canon2data := s.canon2data.insert e data }
    return .some data
  | .none =>
    let data ← ExprData.new e
    setState {
      s with
      canon2data := s.canon2data.insert e data,
      insertionTime2Expr := s.insertionTime2Expr.push e
    }
    trace[Tactic.cse.collection] m!"added new '{e}' with info '{repr data}'" -- TODO: make this a trace node child.
    return .some data

/-- Execute `x` using the main goal local context and instances -/
def CSEM.withMainContext (x : CSEM α) : CSEM α := do
  (← getMainGoal).withContext x

/-- Generate a new index for CSE'd names. -/
def CSEM.gensym : CSEM Nat :=
  modifyGet fun s => (s.gensymCount, { s with gensymCount := s.gensymCount + 1})

/--
Plan to perform a CSE for this expression, by building a 'GeneralizeArg'.
-/
def CSEM.planCSE (e : Expr): CSEM GeneralizeArg := do
  let ix ← gensym
  let xname := Name.mkSimple s!"x{ix}"
  let hname := Name.mkSimple s!"hx{ix}"
  return { expr := e, hName? := hname, xName? := xname}

/--
Try to recursively perform a CSE of the expression.
It looks up information that has been computed, and uses
it to decide profitability.
-/
def CSEM.planCSERec (e : Expr) (data : ExprData) (args : Array GeneralizeArg) : CSEM (Array GeneralizeArg) := do
  if  ← data.isProfitable? then
    match e with
    | .app f x => do
      let args := args.push (← planCSE f)
      let args := args.push (← planCSE x)
      let args := args.push (← planCSE e)
      return args
    | _ => return args.push (← planCSE e)
  else
    return args

def CSEM.cseImpl : CSEM Unit := do
  withMainContext do
    trace[Tactic.cse.info] m!"running CSE"
    let _ ← tryAddExpr (← getMainTarget)
    /- If we should perform CSE on hypotheses as well. -/
    if (← getConfig).processHyps = .allHyps then
      for hyp in (← getLocalHyps) do
        let _ ← tryAddExpr (← inferType hyp)
        continue
    trace[Tactic.cse.summary] m!"CSE collected expressions: {(← getState)}"

    let mut madeProgress := false
    for e in (← getState).insertionTime2Expr do
      if let .some data := (← getState).canon2data.find? e then
        if !(← data.isProfitable?) then
          trace[Tactic.cse.generalize] "⏭️ Skipping {e}: Unprofitable {repr data} ."
        else
          let generalizes ← planCSE e
          let mvarId ← getMainGoal
          -- implementation stolen from 'Lean.Elab.Tactic.evalGeneralize : Tactic'
          trace[Tactic.cse.generalize] "{tryEmoji} Generalizing {generalizes.hName?.getD Name.anonymous} : {e} = {generalizes.xName?.getD Name.anonymous}"
          try
            let (_, newVars, mvarId) ← mvarId.generalizeHyp #[generalizes] ((← getLCtx).getFVarIds)
            mvarId.withContext do
                -- | it's stupid if I need the thing below, so I'm going to ignore it for now.
                -- for v in newVars, id in xIdents ++ hIdents do
                --   Term.addLocalVarInfo id (.fvar v)
                replaceMainGoal [mvarId]
                trace[Tactic.cse.generalize] "{checkEmoji} succeeded in generalizing: {generalizes.hName?.getD Name.anonymous}"
            madeProgress := true
          catch e =>
            trace[Tactic.cse.generalize] "{bombEmoji} failed to generalize: {generalizes.hName?.getD Name.anonymous}"
    if !madeProgress
    then throwError "found no subterms to successfully CSE."
    return ()

open Lean Elab Tactic Parser.Tactic

/-- The `cse` tactic, for performing common subexpression elimination of goal states. -/
def cseTactic (cfg : CSEConfig) : TacticM Unit := CSEM.cseImpl |>.run cfg

/-- The `omega` tactic, for resolving integer and natural linear arithmetic problems. This
`TacticM Unit` frontend with default configuration can be used as an Aesop rule, for example via
the tactic call `aesop (add 50% tactic Lean.Omega.omegaDefault)`. -/
def cseTacticDefault : TacticM Unit := CSEM.cseImpl |>.run {}

end Tactic.CSE

/--
Allow elaboration of `CseConfig` arguments to tactics.
-/
declare_config_elab elabCSEConfig Tactic.CSE.CSEConfig

/--
common subexpression elimination.
-/
syntax (name := cse) "cse" (Lean.Parser.Tactic.config)? : tactic

@[tactic cse]
def evalCse : Tactic := fun
  | `(tactic| cse $[$cfg]?) => do
    let cfg ← elabCSEConfig (mkOptionalNode cfg)
    Tactic.CSE.cseTactic cfg
  | _ => throwUnsupportedSyntax

set_option trace.Tactic.cse.collection true in
set_option trace.Tactic.cse.summary true in
set_option trace.Tactic.cse.generalize true in
theorem testNat : 1 + 2 = 4 := by
  cse
  sorry

-- set_option trace.Tactic.cse.collection true in
set_option trace.Tactic.cse.summary true in
set_option trace.Tactic.cse.generalize true in
theorem test (x y z : Nat) : (x + x) + ((y + y) + (y + y)) = (((y + y) + (y + y)) + ((y + y) + (y + y))) + (((y + y) + (y + y))) := by
  cse (config := {minRefsToCSE := 3})
  cse
  sorry
