/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer, Siddharth Bhat
-/
import Lean
import Tactics.Common
import Tactics.Simp
import Tactics.Sym.LCtxSearch

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
        -- https://github.com/leanprover/lean4/blob/94b1e512da9df1394350ab81a28deca934271f65/src/Lean/Meta/DiscrTree.lean#L371
        -- refines the discrimination tree to also index applied functions. 
        (noIndexAtArgs := false)
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

    /-
    We construct `axHyps` by running a `State` monad, which is
    initialized with an empty array
    -/
    let ((), axHyps) ← StateT.run (s := #[]) <|
      searchLCtx <| do
        let whenFound := fun decl _ => do
          -- Whenever a match is found, we add the corresponding declaration
          -- to the `axHyps` array in the monadic state
          modify (·.push decl)
          return .continu

        -- `r ?field ?state = ?rhs`
        searchLCtxFor (whenFound := whenFound)
          /- By matching under binders, this also matches for non-effect
          hypotheses, which look like:
            `∀ f, f ≠ _ → r f ?state = ?rhs`
          -/
          (matchUnderBinders := true)
          (expectedType := do
            let fld ← mkFreshExprMVar (mkConst ``StateField)
            let state ← mkFreshExprMVar mkArmState
            let rhs ← mkFreshExprMVar none
            return mkEqReadField fld state rhs
          )
        -- `Memory.read_bytes ?n ?addr ?mem = ?rhs`
        searchLCtxFor (whenFound := whenFound)
          (matchUnderBinders := true)
          (expectedType := do
            let n ← mkFreshExprMVar (mkConst ``Nat)
            let addr ← mkFreshExprMVar (mkApp (mkConst ``BitVec) (toExpr 64))
            let mem ← mkFreshExprMVar (mkConst ``Memory)
            let rhs ← mkFreshExprMVar none
            mkEq (mkApp3 (mkConst ``Memory.read_bytes) n addr mem) rhs
          )
        -- `CheckSpAlignment ?state`
        searchLCtxFor (whenFound := whenFound)
          (expectedType := do
            let state ← mkFreshExprMVar mkArmState
            return mkApp (mkConst ``CheckSPAlignment) state)
        -- `?state.program = ?program`
        searchLCtxFor (whenFound := whenFound)
          (expectedType := do
            let mkProgramTy := mkConst ``Program
            let state ← mkFreshExprMVar mkArmState
            let program ← mkFreshExprMVar mkProgramTy
            return mkApp3 (.const ``Eq [1]) mkProgramTy
              (mkApp (mkConst ``ArmState.program) state)
              program)

    let loc := (loc?.map expandLocation).getD (.targets #[] true)
    aggregate axHyps loc simpConfig?
