/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Lean
import Tactics.Common
import Tactics.Simp
open Lean Elab Tactic Expr Meta
open BitVec

/- Given a `goal`, where `st_var` represents a state variable,
`introLNSymHyp` introduces a hypothesis of the form `name : term` in
the context. This function also tries to prove `term` by first
attempting to substitute `st_var` and then calling `LNSymSimp`. This
function returns the original goal that may have the new hypothesis in
its context, and also any unsolved goal that may result from the proof
attempt of the new hypothesis.

The responsibility of providing a well-formed `term` lies with the
caller of this function. -/
def introLNSymHyp (goal : MVarId)
  (st_var : Expr) (name : Name) (term : Expr)
  (ctx : Simp.Context) (simprocs : Array Simp.Simprocs)
  (subst? : Bool := true) (simp_new_goal? : Bool := true) :
  TacticM (MVarId × Option MVarId) :=
  goal.withContext do
  let mvar_expr ← mkFreshExprMVar term MetavarKind.syntheticOpaque name
  -- logInfo m!"New goal: {mvar_expr.mvarId!}"
  let subst_mvar_expr ← if subst? then
                          substVar? mvar_expr.mvarId! st_var.fvarId!
                        else
                          pure (some mvar_expr.mvarId!)
  let term_mvarid ←
    match subst_mvar_expr with
    | none =>
      -- subst_mvar_expr is none only when substVar? could not perform the
      -- substitution.
      logInfo m!"[introLNSymHyp] Could not substitute {st_var} in \
                  goal {mvar_expr.mvarId!}"
      return (goal, none)
    | some mvarid =>
      let new_goal ← if simp_new_goal? then
                      LNSymSimp mvarid ctx simprocs
                     else
                      pure mvarid
      let (_, goal') ← MVarId.intro1P $ ← Lean.MVarId.assert goal name term mvar_expr
      return (goal', new_goal)


def gen_hyp_name (st_name : String) (suffix : String) : Name :=
  Lean.Name.mkSimple ("h_" ++ st_name ++ "_" ++ suffix)

/- Get the value written to `field` (which is an expression
corresponding to a `StateField` value), in the expression `nest`,
which is assumed to be a nest of updates made to the Arm state. If
`nest` does not include an update to `field`, return none. -/
partial def getArmStateComponentNoMem (field : Expr) (nest : Expr) : Option Expr :=
  match_expr nest with
  | w w_field val rest =>
    if field == w_field then
      some val
    else
      getArmStateComponentNoMem field rest
  | write_mem_bytes _ _ _ rest =>
    getArmStateComponentNoMem field rest
  | _ => none
