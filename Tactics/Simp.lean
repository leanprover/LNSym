/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Lean
import Arm.Attr
open Lean Elab Tactic Expr Meta
open BitVec

/- Create a context for using the `simp` tactic during symbolic
simulation in LNSym proofs. -/
def LNSymSimpContext
  (config : Simp.Config := {decide := true})
  (simp_attrs : Array Name := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
  -- Functions to unfold during simp.
  (decls_to_unfold : Array Name := #[])
  -- Theorems to use during simp.
  (thms : Array Name := #[])
  -- Local hypotheses to use during simp.
  (decls : Array LocalDecl := #[])
  -- Simprocs to add to the default set.
  (simprocs : Array Name := #[])
  : MetaM (Simp.Context ×  Array Simp.Simprocs) := do
  let mut ext_simpTheorems := #[]
  for a in simp_attrs do
    let some ext ← (getSimpExtension? a) |
                   throwError m!"[LNSymSimpContext] Error: {a} simp attribute not found!"
    ext_simpTheorems := #[(← ext.getTheorems)] ++ ext_simpTheorems
  let mut const_simpTheorems := ({} : SimpTheorems)
  for d in decls_to_unfold do
    const_simpTheorems ← const_simpTheorems.addDeclToUnfold d
  for t in thms do
    const_simpTheorems ← const_simpTheorems.addConst t
  for l in decls do
    let proof := l.toExpr
    let fvar := l.fvarId
    const_simpTheorems ← const_simpTheorems.add (.fvar fvar) #[] proof
  let all_simpTheorems := (#[const_simpTheorems] ++ ext_simpTheorems)
  let (ctx : Simp.Context) := { config := config,
                                simpTheorems := all_simpTheorems,
                                congrTheorems := (← Meta.getSimpCongrTheorems) }
  let default_simprocs ← Simp.getSimprocs
  let mut all_simprocs := (#[default_simprocs] : Simp.SimprocsArray)
  for s in simprocs do
    all_simprocs ← Simp.SimprocsArray.add all_simprocs s false
  return (ctx, all_simprocs)

/- Invoke the `simp` tactic during symbolic simulation in LNSym
proofs. -/
def LNSymSimp (goal : MVarId)
   (ctx : Simp.Context) (simprocs : Array Simp.Simprocs)
  -- Provide an FVarID (i.e., a hypothesis) to simplify; when none is provided,
  -- the goal is simplified.
   (fvarid : Option FVarId := none) : MetaM (Option MVarId) := goal.withContext do
  match fvarid with
  | none =>
    let (new_goal, _) ← simpGoal goal ctx simprocs
                        (simplifyTarget := true) (discharge? := none)
    match new_goal with
    | none => return none
    | some (_, goal') => return goal'
  | some fid =>
    let (new_goal, _) ← simpLocalDecl goal fid ctx simprocs
    match new_goal with
    | none => return none
    | some (_, goal') => return goal'

----------------------------------------------------------------------
