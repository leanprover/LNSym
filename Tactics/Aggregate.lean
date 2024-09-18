/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean
import Tactics.Common
import Tactics.Simp

open Lean Meta Elab.Tactic

namespace Sym

/-- The default `simp` configuration for `aggregate` -/
def aggregate.defaultSimpConfig : Simp.Config := {
  decide := true,     -- to discharge side-conditions for non-effect hypotheses
  contextual := true, -- to automatically prove non-effect goals
  failIfUnchanged := false,
}

/-- Given an array of (non-)effects hypotheses, aggregate these effects by
`simp`ing at the specified location -/
def aggregate (axHyps : Array LocalDecl) (location : Location)
    (simpConfig? : Option Simp.Config := none) :
    TacticM Unit :=
  let msg := m!"aggregating (non-)effects"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    trace[Tactic.sym] "using hypotheses: {axHyps.map (·.toExpr)}"

    let config := simpConfig?.getD aggregate.defaultSimpConfig
    let (ctx, simprocs) ← LNSymSimpContext
        (config := config)
        (decls := axHyps)

    withLocation location
      (fun hyp => do
        trace[Tactic.sym] "aggregating at {Expr.fvar hyp}"
        let goal ← LNSymSimp (← getMainGoal) ctx simprocs hyp
        replaceMainGoal goal.toList
      )
      (do
        trace[Tactic.sym] "aggregating at the goal"
        let goal ← LNSymSimp (← getMainGoal) ctx simprocs
        replaceMainGoal goal.toList
      )
      (fun _ => pure ())

open Parser.Tactic (location config) in
/--
`sym_aggregate` will search for all local hypotheses of the form
  `r ?fld ?state = _` or `∀ f ..., r ?fld ?state = _`,
and use those hypotheses to simplify the goal

`sym_aggregate at ...` will use those same hypotheses to simplify at the
specified locations, using the same syntax as `simp at ...`

`sym_aggregate (config := ...)` will pass the specified configuration through
to the `simp` call, for fine-grained control. Note that if you do this,
you'll likely want to set `decide := true` yourself, or you might find that
non-effect theorems no longer apply automatically
-/
elab "sym_aggregate" simpConfig?:(config)? loc?:(location)? : tactic => withMainContext do
  let msg := m!"aggregating local (non-)effect hypotheses"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    let simpConfig? ← simpConfig?.mapM fun cfg =>
      elabSimpConfig (mkNullNode #[cfg]) (kind := .simp)

    let lctx ← getLCtx
    -- We keep `expectedRead`/`expectedAlign` as monadic values,
    -- so that we get new metavariables for each localdecl we check
    let expectedRead := do
      let fld ← mkFreshExprMVar (mkConst ``StateField)
      let state ← mkFreshExprMVar mkArmState
      let rhs ← mkFreshExprMVar none
      mkEq (mkApp2 (mkConst ``r) fld state) rhs
    let expectedAlign := do
      let state ← mkFreshExprMVar mkArmState
      return mkApp (mkConst ``CheckSPAlignment) state

    let axHyps ←
      withTraceNode `Tactic.sym (fun _ => pure m!"searching for effect hypotheses") <|
        lctx.foldlM (init := #[]) fun axHyps decl => do
          forallTelescope decl.type <| fun _ type => do
            trace[Tactic.sym] "checking {decl.toExpr} with type {type}"
            let expectedRead ← expectedRead
            let expectedAlign ← expectedAlign
            if ← isDefEq type expectedRead then
              trace[Tactic.sym] "{Lean.checkEmoji} match for {expectedRead}"
              return axHyps.push decl
            else if ← isDefEq type expectedAlign then
              trace[Tactic.sym] "{Lean.checkEmoji} match for {expectedAlign}"
              return axHyps.push decl
            else
              trace[Tactic.sym] "{Lean.crossEmoji} no match"
              return axHyps

    let loc := (loc?.map expandLocation).getD (.targets #[] true)
    aggregate axHyps loc simpConfig?
