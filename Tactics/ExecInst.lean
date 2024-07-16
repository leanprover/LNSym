/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Tactics.Common
import Tactics.Simp
import Lean
open Lean Elab Tactic Expr Meta
open BitVec

----------------------------------------------------------------------

def execInst (goal : MVarId) (h_step : Expr) (hyp_prefix : String)
  : TacticM Bool := goal.withContext do
  -- Find all the FVars in the local context whose name begins with
  -- hyp_prefix.
  let lctx ← getLCtx
  let matching_decls := filterDeclsWithPrefix lctx hyp_prefix.toName
  -- logInfo m!"matching_decls: {matching_decls[0]!.userName}"
  let (ctx, simprocs) ←
    LNSymSimpContext (config := {decide := true, ground := true})
                     (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
                     (decls_to_unfold := #[``exec_inst])
                     (thms := #[])
                     (decls := matching_decls)
                     (simprocs := #[``reduceIte])
  let maybe_goal ← LNSymSimp goal ctx simprocs (fvarid := h_step.fvarId!)
  match maybe_goal with
  | none =>
    logInfo m!"[execInst] The goal appears to be solved, but this tactic \
                  is not a finishing tactic! Something went wrong?"
    return false
  | some goal' =>
    replaceMainGoal [goal']
    return true

def execInstElab (h_step : Name) (hyp_prefix : String) : TacticM Unit :=
  withMainContext
  (do
    let h_step ← getFVarFromUserName h_step
    let success ← execInst (← getMainGoal) h_step hyp_prefix
    if ! success then
      failure)

elab "exec_inst" h_step:ident hyp_prefix:str : tactic =>
  execInstElab (h_step.getId) (hyp_prefix.getString)

----------------------------------------------------------------------
