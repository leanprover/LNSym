/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

import Tactics.ArmConstr
import Lean

namespace ArmConstr

open Lean Elab Tactic Expr Meta

abbrev ArmExpr := ArmConstr.Expr
abbrev ArmStateVar := ArmConstr.StateVar
abbrev ArmUpdate := ArmConstr.Update
abbrev ArmUpdates := ArmConstr.Updates

/-! ## Mapping Arm State Update Expressions to Lean Expressions -/

def ArmStateVar.toExpr (s : ArmStateVar) : Lean.Expr :=
  mkNatLit s

instance : ToExpr ArmStateVar where
  toExpr a := a.toExpr
  toTypeExpr := mkConst ``ArmConstr.StateVar

def ArmUpdate.toExpr (u : ArmUpdate) : Lean.Expr :=
  open ArmConstr.Update in
  match u with
  | .w_gpr i (.var v) => mkAppN (mkConst ``w_gpr)
                                #[(Lean.toExpr i),
                                  (mkApp (mkConst ``GPRVal.var) (mkNatLit v))]

instance : ToExpr ArmUpdate where
  toExpr a := a.toExpr
  toTypeExpr := mkConst ``ArmConstr.Update

def ArmUpdates.toExpr (us : ArmUpdates) : Lean.Expr :=
  match us with
  | [] => Lean.toExpr ([] : Updates)
  | u :: rest =>
    mkAppN (mkConst ``List.cons [levelZero])
          #[mkConst ``Update, (Lean.toExpr u), (ArmUpdates.toExpr rest)]

instance : ToExpr ArmUpdates where
  toExpr a := a.toExpr
  toTypeExpr := mkConst ``ArmConstr.Updates

def ArmExpr.toExpr (e : ArmExpr) : Lean.Expr :=
  mkApp3 (mkConst ``ArmConstr.Expr.mk)
         (ArmStateVar.toExpr e.curr_state)
         (ArmStateVar.toExpr e.prev_state)
         (ArmUpdates.toExpr e.writes)

instance : ToExpr ArmExpr where
  toExpr a := a.toExpr
  toTypeExpr := mkConst ``ArmConstr.Expr


/-
def foo : Lean.Expr :=
  open ArmExpr in
  ArmExpr.toExpr { curr_state := 1, prev_state := 0, writes := [.w_gpr 1#5 (.var 0)] }

#eval foo

elab "foo" : term => return foo

#eval foo
-/

/-! ## Mapping Lean Expressions to Arm State Update Expressions -/

namespace ToArmExpr

/- Borrowed from: Lean/Meta/Tactic/LinearArith/Nat/Basic.lean -/
structure State where
   -- It should be fine to use `KExprMap` here because the mapping should be
   -- small and few HeadIndex collisions.
  stateVarMap : KExprMap ArmStateVar := {}
  stateVars   : Array Lean.Expr := #[]
  fldVarMap   : KExprMap GPRVal := {}
  fldVars     : Array Lean.Expr := #[]

abbrev M := StateRefT State MetaM

def addAsStateVar (e : Lean.Expr) : M ArmStateVar := do
  if let some x ← (← get).stateVarMap.find? e then
    return x
  else
    let x := (← get).stateVars.size
    let s ← get
    set { s with stateVarMap := (← s.stateVarMap.insert e x),
                 stateVars := s.stateVars.push e : State }
    return x

def addAsGPRVar (e : Lean.Expr) : M GPRVal := do
  if let some x ← (← get).fldVarMap.find? e then
    return x
  else
    -- TODO: Make GPRVal also be a Nat, for convenience?
    -- logInfo m!"[addAsGPRVar] e.type: {e_typ}"
    -- if (←isDefEq (← inferType e) (mkApp (mkConst ``BitVec) (mkNatLit 64))) then
      -- throwError "state_value IS defeq to bitvec"
    let x := GPRVal.var (← get).fldVars.size
    let s ← get
    set { s with fldVarMap := (← s.fldVarMap.insert e x),
                 fldVars := s.fldVars.push e : State }
    return x

-- partial def toArmUpdates (writes : Lean.Expr) (acc : ArmUpdates) :
--   M (ArmUpdates × Lean.Expr) := do
--   match_expr writes with
--   | w fld val rest =>
--     let (update : ArmUpdate) ←
--       match_expr fld with
--       | StateField.GPR i =>
--         let some ⟨n, i'⟩ ← getBitVecValue? i | failure
--         let var ← addAsGPRVar val
--         logInfo m!"toArmUpdatesAndStateVar 1: FldVars: {(← get).fldVars}"
--         if h : n = 5 then
--             pure (Update.w_gpr (i'.cast h) var)
--         else failure
--       | _ => failure
--       toArmUpdates rest (update :: acc)
--   | _ =>
--     -- writes is just a state var at this point.
--     return (acc, writes)
--
-- partial def toArmStateVars (curr_state prev_state : Lean.Expr) :
--   M (ArmStateVar × ArmStateVar) := do
--   let (prev_state_var : ArmStateVar) ← addAsStateVar prev_state
--   let (curr_state_var : ArmStateVar) ← addAsStateVar curr_state
--   return (curr_state_var, prev_state_var)

instance : ToMessageData GPRVal where
  toMessageData x :=
    match x with
    | .var i => m!"(var {i})"

instance : ToMessageData Update where
  toMessageData x := match x with
  | .w_gpr i v => m!"(w_gpr {i} {v})"

instance : ToMessageData ArmExpr where
  toMessageData x := m!"\{curr: {x.curr_state}; writes: {x.writes} prev: {x.prev_state}}"

def unifyTypes (varExpr : Lean.Expr) (mvarExpr : Lean.Expr) : MetaM Unit := do
  let varType ← (whnf (← inferType varExpr))
  let mvarType ← inferType mvarExpr
  try
    let _ := isDefEq varType mvarType
  catch _ =>
    throwError "Types could not be unified"

partial def toArmUpdatesAndStateVar (curr_state writes : Lean.Expr) (us : ArmUpdates) :
  M (ArmStateVar × ArmUpdates × ArmStateVar) := do
  match_expr writes with
  | w fld val rest =>
    let (update : ArmUpdate) ←
      match_expr fld with
      | StateField.GPR i =>
        let some ⟨n, i'⟩ ← getBitVecValue? i | failure
        -- let orig_val_type ← inferType val
        -- let val_type ← (whnf (← inferType val))
        -- let mvar ← mkFreshExprMVar none
        -- mvar.mvarId!.assign val_type
        -- -- unifyTypes val mvar
        -- logInfo m!"mvar: {mvar}"
        -- -- have h_proof : ∀ i, state_value (.GPR i) = BitVec 64 := by
        --   -- simp only [implies_true]
        -- -- let val ← mkAppM ``cast #[h_proof, mvar]
        -- -- let val ← mkAppM ``cast #[← mkEqRefl orig_val_type, mvar]
        -- let val := mkApp4 (.const ``cast [1]) orig_val_type val_type (← mkEqRefl val_type) val
        -- logInfo m!"val: {val}"
        let var ← addAsGPRVar val
        logInfo m!"toArmUpdatesAndStateVar 1: var: {var} val: {val}"
        logInfo m!"toArmUpdatesAndStateVar 1: FldVars: {(← get).fldVars}"
        if h : n = 5 then
            pure (Update.w_gpr (i'.cast h) var)
        else failure
      | _ => failure
    logInfo m!"toArmUpdatesAndStateVar: Update: {update}"
    toArmUpdatesAndStateVar curr_state rest (us ++ [update])
  | _ =>
    -- writes is just a state var at this point.
    let (prev_state_var : ArmStateVar) ← addAsStateVar writes
    let (curr_state_var : ArmStateVar) ← addAsStateVar curr_state
    -- logInfo m!"toArmUpdatesAndStateVar: Curr_State_Var: {curr_state_var}"
    -- logInfo m!"toArmUpdatesAndStateVar: Prev_State_var: {prev_state_var}"
    -- logInfo m!"toArmUpdatesAndStateVar: FldVars: {(← get).fldVars}"
    logInfo m!"toArmUpdatesAndStateVar: Writes: {us}"
    return (curr_state_var, us, prev_state_var)

partial def toArmExpr? (e : Lean.Expr) : M (Option ArmExpr) := do
  match_expr e with
  | Eq α s writes =>
    let_expr ArmState ← α | failure
    let (curr_state, writes, prev_state) ← toArmUpdatesAndStateVar s writes []
    -- let (writes, prev_state_expr) ← toArmUpdates writes []
    -- logInfo m!"toArmExpr?: FldVars: {(← get).fldVars}"
    -- let (curr_state, prev_state) ← toArmStateVars s prev_state_expr
    logInfo m!"toArmExpr?: Current State ArmStateVar: {curr_state}"
    logInfo m!"toArmExpr?: Previous State ArmStateVar: {prev_state}"
    logInfo m!"toArmExpr?: StateVars: {(← get).stateVars}"
    logInfo m!"toArmExpr?: FldVars: {(← get).fldVars}"
    return some { curr_state, writes, prev_state }
  | _ => failure

def run (x : M α) : MetaM (α × Array Lean.Expr × Array Lean.Expr) := do
  let (a, s) ← x.run {}
  return (a, s.stateVars, s.fldVars)

end ToArmExpr

def toContextExpr (state_ctx : Array Lean.Expr) (gpr_ctx : Array Lean.Expr) :
  MetaM Lean.Expr := do
  let state_ctx ← mkListLit (mkConst ``ArmState) state_ctx.toList
  let gpr_ctx ← (mkListLit (← mkAppM ``BitVec #[mkNatLit 64]) gpr_ctx.toList)
  let ans := (mkApp2 (mkConst ``ArmConstr.Context.mk) state_ctx gpr_ctx)
  logInfo m!"toContextExpr: {ans}"
  return ans

abbrev mkAuxDecl := Lean.Elab.Tactic.BVDecide.Frontend.mkAuxDecl

def ArmExprPruned? (refl_proof_name : Name) (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let (some arm_expr, state_ctx, gpr_ctx) ←
    ToArmExpr.run (ToArmExpr.toArmExpr? e) | return none
  logInfo m!"arm_expr: {arm_expr}"
  logInfo m!"state_ctx: {state_ctx}"
  logInfo m!"gpr_ctx: {gpr_ctx}"
  let arm_expr_pruned := arm_expr.prune

  let auxValue := mkApp2 (mkConst ``ArmConstr.Expr.isPruned)
                         (toExpr arm_expr) (toExpr arm_expr_pruned)
  logInfo m!"auxValue: {auxValue}"
  -- TODO: Use Lean.Elab.Term.mkAuxName for refl_name.
  -- let refl_name := `_armexpr_reflection_def
  mkAuxDecl refl_proof_name auxValue (mkConst ``Bool)

  let refl_proof :=
    mkApp3
    (mkConst ``Lean.ofReduceBool)
    (mkConst refl_proof_name)
    (toExpr true)
    (← mkEqRefl (toExpr true))

  logInfo m!"poised to check refl_proof"
  check refl_proof
  logInfo m!"checked refl_proof"
  -- logInfo m!"poised to check native_decide proof"
  -- let native_decide_proof := (mkApp (mkConst ``of_decide_eq_true) refl_proof)
  -- logInfo m!"checked native_decide proof"

  let ctx_expr ← toContextExpr state_ctx gpr_ctx
  logInfo m!"poised to check ctx_expr {ctx_expr}"
  check ctx_expr
  logInfo m!"checked ctx_expr"

  let p := mkAppN (mkConst ``ArmConstr.Expr.eq_true_of_denote)
                    #[ctx_expr,
                      (toExpr arm_expr),
                      (toExpr arm_expr_pruned),
                      -- mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true)
                      refl_proof]
  logInfo m!"Proof: {p}"
  check p
  logInfo m!"checked proof {p}"
  return some (mkConst ``True, p)

def ReflectionProofName : Lean.Elab.TermElabM Name := do
  Lean.Elab.Term.mkAuxName `_armexpr_reflection_def

open Lean.Elab.Tactic

elab "prune_updates" h_state_eq:term : tactic => withMainContext do
  logInfo m!"This is h_state_eq: {h_state_eq}"
  let h_state_eq_expr ← elabTerm h_state_eq none
  let hStateEq ← inferType h_state_eq_expr
  logInfo m!"This is hStateEq {hStateEq}"
  let refl_proof_name ← ReflectionProofName
  let some (_, e) ← ArmExprPruned? refl_proof_name hStateEq | return
  -- logInfo m!"This is after pruning e: {e}"
  logInfo m!"This is after pruning proof:\n {e}"
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← goal.getType
  let type ← inferType e
  logInfo m!"Target {target}"
  logInfo m!"E {e}"
  logInfo m!"About to check E"
  check e
  logInfo m!"Checked E"
  let e_ctor := e.ctorName
  logInfo m!"e_ctor: {e_ctor}"
  -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
  -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `proof_type` does
  -- not have this form, `args` is empty and `conclusion = type`.)
  let (args, _, conclusion) ← forallMetaTelescopeReducing type
  logInfo m!"args: {args} conclusion: {conclusion}"
  if ← isDefEq target conclusion then
    -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
    -- metavariables in `args`.
    logInfo m!"goal_type and conclusion are defEq!"
    if ← isDefEq args[0]! h_state_eq_expr then
      logInfo m!"args[0] and h_state_eq_expr are defEq!"
    let new_goal_term := mkAppN e args
    -- let new_goal_term := goal_type
    logInfo m!"new_goal_term: {new_goal_term}"
    -- logInfo m!"new_goal_term.mvarId!.isAssigned: {← new_goal_term.mvarId!.isAssigned}"
    -- logInfo m!"args[0]!.mvarId!.isAssigned: {← args[0]!.mvarId!.isAssigned}"
    goal.assign new_goal_term
    -- `isDefEq` may have assigned some of the `args`. Report the rest as new
    -- goals.
    let newGoals ← args.filterMapM λ mvar => do
      let mvarId := mvar.mvarId!
      if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
        return some mvarId
      else
        return none
    logInfo m!"newGoals: {newGoals.toList}"
    setGoals newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
  else
    throwTacticEx `prune_updates goal m!"{e} is not applicable to goal with target {target}"

namespace ArmConstr

#time
open Expr Update in
theorem example2
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 0#5) x1 s0))) :
  s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 s0) := by
  prune_updates h_s1
  done
--
#print example2

#time
open Expr Update in
theorem example4
  (h_s1 : s1 = w (.GPR 1#5) (x100 + x100') (w (.GPR 0#5) x500 (w (.GPR 8#5) x1 s0))) :
  s1 = w (.GPR 0#5) x500 (w (.GPR 1#5) (x100 + x100') (w (.GPR 8#5) x1 s0)) := by
  prune_updates h_s1
  done

#print example4
