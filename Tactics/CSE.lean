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

/-! # Common Subexpression Eliminiation Tactic

## Algorithm:

### TL;DR

- step 1: collect all terms bottom up, hashing them for structural equality and counting number of occurrences.
- step 2: once again, working top down, call `generalize` for each of these, generating appropriate generalize names.

Suppose our goal state is `⊢ (large small small) + (large small small)`.
If a term `small` is a subterm of `large`, then `size small < size large`.
Let's consider what happens if we generalize `small` first, then `large`.

### We start with the proof state:

```
⊢ (large small small) + (large small small)
```

### We gather subterms to be CSEd, which are:

- (small)
- (large small small)

### We now generalize `small`, giving:

```
hx : x = small
x : _
⊢ (large x x) + (large x x)
```

If we now try to generalize the term `large small small`, we will find no occurrences!
This is because the `small` has been replaced by `x` everywhere.
For a correct algorithm, we should generalize `large x x`.
For this correct algorithm,we need some way to track such substitutions within `Expr`s.
[@bollu: it maybe possible to use `FVarSubst` to achieve this effect.]

Instead, we use the naive algorithm, and go top-down instead.

### We start with the proof state:

```
⊢ (large small) + (large small)
```

### We gather subterms to be CSEd, which are:

- (small)
- (large small small)

### We now generalize `(large small small)`, giving:

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
  /-- Whether the tactic should throw an error if no CSEable subterms were found. -/
  failIfUnchanged : Bool := true
  /-- Number of steps the tactic should spend searching for subterms to gather information. -/
  fuelSearch : Nat := 1000
  /-- Number of steps the tactic should spend performing subexpression elimination.
   It can be useful to have large amounts of fuel for searching, and very little for eliminating,
   to search for maximal subterm sharing, and to then eliminiate the most common occurrences.
  -/
  fuelEliminate : Nat := 1000
  /--
  Whether we are performing a dry run, where we will identify repeated
  subterms, and simulate the sharing algorithm, but perform no actual sharing.
  This is used for debugging tactics. -/
  dryRun? : Bool := false

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
  a counter to generate new names.
  -/
  gensymCount : Nat := 1
  /-- Number of steps the tactic should spend searching for subterms to gather information. -/
  currentSearchFuel : Nat
  /-- Number of steps the tactic should spend performing subexpression elimination. -/
  currentEliminateFuel : Nat

abbrev CSEM := StateRefT State (ReaderT CSEConfig TacticM)

/-- Get the configuration. -/
def getConfig : CSEM CSEConfig := read

/-- Get the mutable state. -/
def getState : CSEM State := get

/-- Get the mutable state. -/
def setState : State → CSEM Unit := set

def State.ofConfig (cfg : CSEConfig) : State := {
  currentSearchFuel := cfg.fuelSearch,
  currentEliminateFuel := cfg.fuelEliminate,
}

def CSEM.run (val : CSEM α) (config : CSEConfig) : TacticM α :=
   val.run' (State.ofConfig config) |>.run config

def CSEM.hasSearchFuel : CSEM Bool := do
  return (← getState).currentSearchFuel > 0

def CSEM.consumeSearchFuel : CSEM Unit :=
  modify fun s => { s with currentSearchFuel := s.currentSearchFuel - 1 }

def CSEM.hasEliminiateFuel : CSEM Bool := do
  return (← getState).currentEliminateFuel > 0

def CSEM.consumeEliminiateFuel : CSEM Unit :=
  modify fun s => { s with currentEliminateFuel := s.currentEliminateFuel - 1 }

def CSEM.isDryRun : CSEM Bool := do
  return (← getConfig).dryRun?

/-- create a trace node in trace class (i.e. `set_option traceClass true`),
with header `header`, whose default collapsed state is `collapsed`. -/
def CSEM.withTraceNode (header : MessageData) (k : CSEM α)
    (collapsed : Bool := true)
    (traceClass : Name := `Tactic.cse.summary) : CSEM α :=
  Lean.withTraceNode traceClass (fun _ => return header) k (collapsed := collapsed)

/-- Create a trace note that folds `header` with `(NOTE: can be large)`,
and prints `msg` under such a trace node.
-/
def CSEM.traceLargeMsg (header : MessageData) (msg : MessageData) : CSEM Unit :=
    withTraceNode m!"{header} (NOTE: can be large)" do
      trace[Tactic.cse.summary] msg

-- @bollu: Surely we must have an implementation of this.
private def Array.replicate (n : Nat) (v : α) : Array α := List.replicate n v |>.toArray

/-- decides if performing CSE for this expression is profitable. -/
def ExprData.isProfitable? (data : ExprData) : CSEM Bool :=
  return data.size > 1 && data.occs >= (← getConfig).minOccsToCSE

/-- Check if an expression is a nat literal, or a `OfNat.ofNat` of a nat literal.
This lets us avoid CSEing over nat literals, which are already in canonical form.
-/
def CSEM.isNatLit (e : Expr) : Bool :=
  if e.isRawNatLit then true
  else
  match_expr e with
  | OfNat.ofNat _α x _inst  => x.isRawNatLit -- @OfNat.ofNat Nat 1 (instOfNatNat 1)
  | _ => false

/--
The function is partial because of the call to `tryAddExpr` that
Lean does not infer is smaller in `e`.
-/
partial def CSEM.tryAddExpr (e : Expr) : CSEM (Option ExprData) := do
  consumeSearchFuel
  unless (← hasSearchFuel) do
    trace[Tactics.cse.summary] "⏸️ CSE ran out of fuel while looking for subexpressions. Increase `fuelSearch` in CSEConfig."
    return .none

  let t ← inferType e
  -- for now, we ignore function terms.
  let relevant? := !t.isArrow && !t.isSort && !t.isForall && !isNatLit e
  withTraceNode m!"({e}):({t}) [relevant? {if relevant? then checkEmoji else crossEmoji}] (unfold for subexpressions...)" do
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
          if let .some data ← tryAddExpr arg then
            size := size + data.size
    -- the current argument itself was irrelevant, so don't bother adding it.
    if !relevant? then return .none
    let s ← getState
    match s.canon2data.find? e with
    | .some data => do
      let data := data.incrRef
      traceLargeMsg m!"updated expr (...) with info ({repr data})" m!"{e}"
      setState { s with canon2data := s.canon2data.insert e data }
      return .some data
    | .none =>
      let data := { occs := 1, size : ExprData }
      setState {
        s with
        canon2data := s.canon2data.insert e data,
      }
      traceLargeMsg m!"Added new expr (...) with info ({repr data})" m!"{e}"
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
  consumeEliminiateFuel
  unless (← hasEliminiateFuel) do
    trace[Tactics.cse.summary] "⏸️ CSE ran out of fuel while performing subexpression elimination. increase `fuelEliminate`."
    return false

  let hname := arg.hName?.getD .anonymous
  let xname := arg.xName?.getD .anonymous
  let e := arg.expr

  let mvarId ← getMainGoal
  mvarId.withContext do
    -- implementation modeled after `Lean.Elab.Tactic.evalGeneralize`.
    traceLargeMsg m!"{tryEmoji} Generalizing {hname}: {xname} = ..."  m!"{e}"
    let checkpoint ← Tactic.saveState
    try
      if ! (← isDryRun) then
        -- Implementation modeled after `Lean.MVarId.generalizeHyp`.
        let _e ← instantiateMVars e
        let hyps := ((← getLCtx).getFVarIds)
        let transparency := TransparencyMode.reducible
        let hyps ← hyps.filterM fun h => do
          let type ← instantiateMVars (← h.getType)
          return (← withTransparency transparency <| kabstract type arg.expr).hasLooseBVars
        let (reverted, mvarId) ← mvarId.revert hyps true
        let (_newVars, mvarId) ← mvarId.generalize #[arg] transparency
        let (reintros, mvarId) ← mvarId.introNP reverted.size
        let _fvarSubst := Id.run do
          let mut subst : FVarSubst := {}
          for h in reverted, reintro in reintros do
            subst := subst.insert h (mkFVar reintro)
          pure subst
        replaceMainGoal [mvarId]
      traceLargeMsg m!"{checkEmoji} succeeded in generalizing {hname}." m!"{← getMainGoal}"
      return true
    catch e =>
      checkpoint.restore
      traceLargeMsg m!"{bombEmoji} failed to generalize {hname}" m!"{e.toMessageData}"
      return false

def CSEM.cseImpl : CSEM Unit := do
  withMainContext do
    withTraceNode m!"CSE collecting hypotheses:" do
      let _ ← tryAddExpr (← getMainTarget)
      /- If we should perform CSE on hypotheses as well. -/
      if (← getConfig).processHyps = .allHyps then
        for hyp in (← getLocalHyps) do
          let _ ← tryAddExpr (← inferType hyp)

    let newCanon2Data : HashMap Expr ExprData ←
      withTraceNode m!"⏭️ CSE eliminiating unprofitable expressions (#expressions:{(← getState).canon2data.size}):" do
        let mut newCanon2Data := {}
        for (e, data) in (← getState).canon2data.toArray.qsort (fun kv kv' => kv.2.occs > kv'.2.occs) do
          if !(← data.isProfitable?) then
            traceLargeMsg m!"⏭️ Unprofitable {repr data} ." m!"expr: {e}"
          else
            newCanon2Data := newCanon2Data.insert e data
        return newCanon2Data

    withTraceNode m!"CSE summary of profitable expressions (#expressions:{(newCanon2Data).size}):" <| do
      let mut i : Nat := 1
      /- sort to show most numerous first follows by smallest. -/
      for (e, data) in newCanon2Data.toArray.qsort (fun kv kv' => kv.2.occs > kv'.2.occs) do
        if !(← data.isProfitable?) then continue
        traceLargeMsg m!"{i}) {repr data}" m!"{e}"
        i := i + 1


    withTraceNode m!"CSE rewriting (#expressions:{newCanon2Data.size}):" do
      let mut madeProgress := false
      for (e, _data) in newCanon2Data.toArray.qsort (fun kv kv' => kv.2.size > kv'.2.size) do
          let generalizeArg ← planCSE e
          madeProgress := madeProgress || (← generalize generalizeArg)
      if !madeProgress && !(← getConfig).failIfUnchanged
      then throwError "found no subterms to successfully CSE."
      return ()

open Lean Elab Tactic Parser.Tactic

/-- The `cse` tactic, for performing common subexpression elimination of goal states. -/
def cseTactic (cfg : CSEConfig) : TacticM Unit := CSEM.cseImpl |>.run cfg

/-- The `cse` tactic with the default configuration. -/
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
