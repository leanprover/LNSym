/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

This file contains an experimental implementation of a common subexpression elimination pass,
used to simplify goal states.
-/
import Lean
import Tactics.Attr
import Lean.Meta.Tactic.Generalize
open Lean Elab Tactic Expr Meta

/-- An emoji for when we are processing or trying. -/
def tryEmoji : String := "⌛"

/-! ### Common Subexpression Eliminiation Tactic

#### Algorithm:

- step 1: collect all terms bottom up, hashing them for structural equality and counting number of occurrences.
- step 2: once again, working top down, call `generalize` for each of these, generating appropriate generalize names.

-/

section HashMapUtils

namespace Tactic.CSE

inductive ShouldProcessHyps
| ignoreHyps
| allHyps
deriving DecidableEq

structure CSEConfig where
  /-- Whether we should process the hypotheses of the current goal state. -/
  processHyps : ShouldProcessHyps := .ignoreHyps
   /-- The minimum number of occurrences necessary to perform CSE on a term. -/
  minOccsToCSE : Nat := 2


structure ExprData where
  /-- Number of references to this expression -/
  occs : Nat
  /-- Size of the expression, disregarding implicits. -/
  size : Nat
deriving Repr

def ExprData.incrRef (data : ExprData) : ExprData :=
  { data with occs := data.occs + 1 }


structure State where
  /--
  A mapping from expression to its canonical index.
  -/
  canon2data : HashMap Expr ExprData := {}
  /--
  an array of expressions, whose order tells us the time they were inserted into the CSE map.
  Since we insert expressions from child to parent, parents will always appear after children.
  -/
  insertionTime2Expr : Array Expr := #[]
  /--
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
  occs := 1,
  size := (← CSEM.exprSize e)
}

/-- decides if performing CSE for this expression is profitable. -/
def ExprData.isProfitable? (data : ExprData) : CSEM Bool :=
  return data.size > 1 && data.occs >= (← getConfig).minOccsToCSE

/--
The function is partial because of the call to `tryAddExpr` that
Lean does not infer is smaller in `e`.
-/
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
        if let .some _ ← tryAddExpr arg then
          size := size + 1
  -- the current argument itself was irrelevant, so don't bother adding it.
  if !relevant? then return .none
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

/-- Execute `x` using the main goal local context. -/
def CSEM.withMainContext (x : CSEM α) : CSEM α := do
  (← getMainGoal).withContext x

/-- Generate a new index for CSE'd names. -/
def CSEM.gensym : CSEM Nat :=
  modifyGet fun s => (s.gensymCount, { s with gensymCount := s.gensymCount + 1})

/--
Plan to perform a CSE for this expression, by building a 'GeneralizeArg'.
-/
partial def CSEM.planCSE (e : Expr): CSEM GeneralizeArg := do
  let ix ← gensym
  let xname := Name.mkSimple s!"x{ix}"
  let hname := Name.mkSimple s!"hx{ix}"
  if ((← getLCtx).findFromUserName? xname).isSome || ((← getLCtx).findFromUserName? hname).isSome
  then planCSE e
  else return { expr := e, hName? := hname, xName? := xname }

/--
Plan to perform a CSE for this expression, by building a 'GeneralizeArg'.
-/
def CSEM.generalize (arg : GeneralizeArg) : CSEM Bool := do
  let hname := arg.hName?.getD .anonymous
  let xname := arg.xName?.getD .anonymous
  let e := arg.expr

  let mvarId ← getMainGoal
  mvarId.withContext do
    -- implementation modeled after `Lean.Elab.Tactic.evalGeneralize`.
    trace[Tactic.cse.generalize] "{tryEmoji} Generalizing {hname} : {e} = {xname}"
    try
      -- Implementation modeled after `Lean.MVarId.generalizeHyp`.
      let e ← instantiateMVars e
      let hyps := ((← getLCtx).getFVarIds)
      let transparency := TransparencyMode.reducible
      let hyps ← hyps.filterM fun h => do
        let type ← instantiateMVars (← h.getType)
        return (← withTransparency transparency <| kabstract type arg.expr).hasLooseBVars
      let (reverted, mvarId) ← mvarId.revert hyps true
      let (newVars, mvarId) ← mvarId.generalize #[arg] transparency
      let (reintros, mvarId) ← mvarId.introNP reverted.size
      let fvarSubst := Id.run do
        let mut subst : FVarSubst := {}
        for h in reverted, reintro in reintros do
          subst := subst.insert h (mkFVar reintro)
        pure subst
      replaceMainGoal [mvarId]
      trace[Tactic.cse.generalize] "{checkEmoji} succeeded in generalizing {hname}. ({← getMainGoal})"
      return true
    catch e =>
      trace[Tactic.cse.generalize] "{bombEmoji} failed to generalize {hname}"
      return false

def CSEM.cseImpl : CSEM Unit := do
  withMainContext do
    trace[Tactic.cse.info] m!"running CSE"
    let _ ← tryAddExpr (← getMainTarget)
    /- If we should perform CSE on hypotheses as well. -/
    if (← getConfig).processHyps = .allHyps then
      for hyp in (← getLocalHyps) do
        let _ ← tryAddExpr (← inferType hyp)
    trace[Tactic.cse.summary] m!"CSE collected expressions: {(← getState)}"

    let mut madeProgress := false
    /-
    Suppose our goal state is `⊢ (large small small) + (large small small)`.
    If a term `small` is a subterm of `large`, then `size small < size large`.
    Let's consider what happens if we generalize `small` first, then `large`.

    ### We start with the proof state:

    ```
    ⊢ (large small small) + (large small small)
    ```

    ### We now generalize `small`, giving:

    ```
    hx : x = small
    x : _
    ⊢ (large x x) + (large x x)
    ```

    If we now try to generalize the term `large small small`, we will find no ocurrences!
    This is because the `small` has been replaced by `x` everywhere.
    For a correct algorithm, we should generalize `large x x`.
    For this correct algorithm,we need some way to track such substitutions within `Expr`s.
    [@bollu: it maybe possible to use `FVarSubst` to achieve this effect.]

    Instead, we use the naive algorithm, and go top-down instead.

    ### We start with the proof state:

    ```
    ⊢ (large small) + (large small)
    ```

    ### We now generalize `(large small)`, giving:

    ```
    hx : x = (large small small)
    large : _
    ⊢ x + x
    ```

    ### We now generalize `small`, giving

    ```
    hy : y = small
    small : _
    hx : x = (large y y)
    large : _
    ⊢ x + x
    ```
    Thus, the size metric ensures that at the end,
    we will get a hypothesis that has been maximally CSEd.
    -/
    for (e, data) in (← getState).canon2data.toArray.qsort (fun kv kv' => kv.2.size > kv'.2.size) do
      -- if let .some data := (← getState).canon2data.find? e then
        if !(← data.isProfitable?) then
          trace[Tactic.cse.generalize] "⏭️ Skipping {e}: Unprofitable {repr data} ."
        else
          let generalizeArg ← planCSE e
          madeProgress := madeProgress || (← generalize generalizeArg)
    if !madeProgress
    then throwError "found no subterms to successfully CSE."
    return ()

open Lean Elab Tactic Parser.Tactic

/-- The `cse` tactic, for performing common subexpression elimination of goal states. -/
def cseTactic (cfg : CSEConfig) : TacticM Unit := CSEM.cseImpl |>.run cfg

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
  try cse
  sorry

set_option trace.Tactic.cse.collection true in
set_option trace.Tactic.cse.summary true in
set_option trace.Tactic.cse.generalize true in
theorem testHypFail (h : 42 + 42 = 2) (h₂ : (42 + 42) + (42 + 42) = 2) : 1 + 2 = 4 := by
  generalize k : 42 + 42 = x -- weird, it doesn't pick it up in h!
  sorry

set_option trace.Tactic.cse.collection true in
set_option trace.Tactic.cse.summary true in
set_option trace.Tactic.cse.generalize true in
theorem testHypCSE (h : 42 + 42 = 2) (h₂ : (42 + 42) + (42 + 42) = 2) : 1 + 2 = 4 := by
  revert h h₂ -- reverting then generalizing seems to succeed.
  generalize k : 42 + 42 = x -- weird, it doesn't pick it up in h!
  intros h₁ h₂ -- we now have goals in terms of `h`.
  sorry


-- set_option trace.Tactic.cse.collection true in
set_option trace.Tactic.cse.summary true in
set_option trace.Tactic.cse.generalize true in
theorem test (x y z : Nat) : (x + x) + ((y + y) + (y + y)) = (((y + y) + (y + y)) + ((y + y) + (y + y))) + (((y + y) + (y + y))) := by
  cse (config := {minOccsToCSE := 3})
  sorry

open BitVec in
set_option trace.Tactic.cse.generalize true in
theorem example3 (a b c d : BitVec 64) : (zeroExtend 128
              (extractLsb 63 0
                  (
                    zeroExtend 128 (extractLsb 127 64 c) <<< 64)) |||
          zeroExtend 128
              (extractLsb 127 64
                  (zeroExtend 128 (extractLsb 127 64 c) <<< 64))) = sorry := by
  -- generalize hy : ((zeroExtend 128 (extractLsb 127 64 c) <<< 64)) = y
  -- generalize hx : (extractLsb 127 64 c) = x
  cse
  sorry
