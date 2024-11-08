/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

import Tactics.PruneUpdatesLogic
import Tactics.Attr

import Lean

namespace ArmConstr

open Lean Elab Tactic Expr Meta

abbrev ArmExpr := ArmConstr.Expr
abbrev ArmStateVar := ArmConstr.StateVar
abbrev ArmUpdate := ArmConstr.Update
abbrev ArmUpdates := ArmConstr.Updates

section Tracing
-- (FIXME): Move to Sym/Common.lean?

variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadLiftT IO m]
  [MonadRef m] [AddMessageContext m] [MonadOptions m] {ε : Type}
  [MonadAlwaysExcept ε m] [MonadLiftT BaseIO m]

/-- Add a trace node with the `Tactic.prune_updates` trace class -/
def withTraceNode (msg : MessageData) (k : m α)
    (collapsed : Bool := true)
    (tag : String := "")
    : m α := do
  Lean.withTraceNode `Tactic.prune_updates (fun _ => pure msg) k collapsed tag

end Tracing

/-! ## Mapping Arm State Update Expressions to Lean Expressions -/

def ArmStateVar.toExpr (s : ArmStateVar) : Lean.Expr :=
  mkNatLit s

instance : ToExpr ArmStateVar where
  toExpr a := a.toExpr
  toTypeExpr := mkConst ``ArmConstr.StateVar

def ArmUpdate.toExpr (u : ArmUpdate) : Lean.Expr :=
  open ArmConstr.Update in
  match u with
  | .err v => mkAppN (mkConst ``err) #[(mkNatLit v)]
  | .pc v => mkAppN (mkConst ``pc) #[(mkNatLit v)]
  | .gpr i v => mkAppN (mkConst ``gpr)
                       #[(Lean.toExpr i), (mkNatLit v)]
  | .sfp i v => mkAppN (mkConst ``sfp)
                        #[(Lean.toExpr i), (mkNatLit v)]
  | .flag i v => mkAppN (mkConst ``flag)
                        #[(Lean.toExpr i), (mkNatLit v)]

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
  ArmExpr.toExpr { curr_state := 1, prev_state := 0, writes := [.gpr 1#5 (0), .err (0)] }

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
  stateVarMap  : KExprMap ArmStateVar := {}
  stateVars    : Array Lean.Expr := #[]
  gprVarMap    : KExprMap GPRVar := {}
  gprVars      : Array Lean.Expr := #[]
  sfpVarMap    : KExprMap SFPVar := {}
  sfpVars      : Array Lean.Expr := #[]
  flagVarMap   : KExprMap FlagVar := {}
  flagVars     : Array Lean.Expr := #[]
  errVarMap    : KExprMap ErrVar := {}
  errVars      : Array Lean.Expr := #[]
  pcVarMap     : KExprMap PCVar := {}
  pcVars       : Array Lean.Expr := #[]

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

def addAsPCVar (e : Lean.Expr) : M Nat := do
  if let some x ← (← get).pcVarMap.find? e then
    return x
  else
    let x := (← get).pcVars.size
    let s ← get
    set { s with pcVarMap := (← s.pcVarMap.insert e x),
                 pcVars := s.pcVars.push e : State }
    return x

def addAsErrVar (e : Lean.Expr) : M Nat := do
  if let some x ← (← get).errVarMap.find? e then
    return x
  else
    let x := (← get).errVars.size
    let s ← get
    set { s with errVarMap := (← s.errVarMap.insert e x),
                 errVars := s.errVars.push e : State }
    return x

def addAsGPRVar (e : Lean.Expr) : M Nat := do
  if let some x ← (← get).gprVarMap.find? e then
    return x
  else
    let x := (← get).gprVars.size
    let s ← get
    set { s with gprVarMap := (← s.gprVarMap.insert e x),
                 gprVars := s.gprVars.push e : State }
    return x

def addAsSFPVar (e : Lean.Expr) : M Nat := do
  if let some x ← (← get).sfpVarMap.find? e then
    return x
  else
    let x := (← get).sfpVars.size
    let s ← get
    set { s with sfpVarMap := (← s.sfpVarMap.insert e x),
                 sfpVars := s.sfpVars.push e : State }
    return x

def addAsFlagVar (e : Lean.Expr) : M Nat := do
  if let some x ← (← get).flagVarMap.find? e then
    return x
  else
    let x := (← get).flagVars.size
    let s ← get
    set { s with flagVarMap := (← s.flagVarMap.insert e x),
                 flagVars := s.flagVars.push e : State }
    return x

instance : ToMessageData ArmExpr where
  toMessageData x := m!"\{curr: {x.curr_state}; writes: {x.writes} prev: {x.prev_state}}"

def getPFlagValue? (e : Lean.Expr) : MetaM (Option PFlag) := OptionT.run do
  match_expr e with
  | PFlag.N => return PFlag.N
  | PFlag.Z => return PFlag.Z
  | PFlag.C => return PFlag.C
  | PFlag.V => return PFlag.V
  | _ => failure

partial def toArmUpdatesAndStateVar (curr_state writes : Lean.Expr) (us : ArmUpdates) :
  M (ArmStateVar × ArmUpdates × ArmStateVar) :=
  withTraceNode m!"toArmUpdatesAndStateVar" (tag := "toArmUpdatesAndStateVar") <| do
  match_expr writes with
  | w fld val rest =>
    let (update : ArmUpdate) ←
      match_expr fld with
      | StateField.ERR =>
        let var ← addAsErrVar val
        trace[Tactic.prune_updates] "Adding ERR value {val} as {var}"
        trace[Tactic.prune_updates] "All variables in the Err map: {(← get).errVars}"
        pure (Update.err var)
      | StateField.PC =>
        let var ← addAsPCVar val
        trace[Tactic.prune_updates] "Adding PC value {val} as {var}"
        trace[Tactic.prune_updates] "All variables in the PC map: {(← get).pcVars}"
        pure (Update.pc var)
      | StateField.GPR i =>
        let some ⟨n, i'⟩ ← getBitVecValue? i | failure
        let var ← addAsGPRVar val
        trace[Tactic.prune_updates] "Adding GPR value {val} as {var}"
        trace[Tactic.prune_updates] "All variables in the GPR map: {(← get).gprVars}"
        if h : n = 5 then
            pure (Update.gpr (i'.cast h) var)
        else failure
      | StateField.SFP i =>
        let some ⟨n, i'⟩ ← getBitVecValue? i | failure
        let var ← addAsSFPVar val
        trace[Tactic.prune_updates] "Adding SFP value {val} as {var}"
        trace[Tactic.prune_updates] "All variables in the SFP map: {(← get).sfpVars}"
        if h : n = 5 then
            pure (Update.sfp (i'.cast h) var)
        else failure
      | StateField.FLAG i =>
        let some i' ← getPFlagValue? i | failure
        let var ← addAsFlagVar val
        trace[Tactic.prune_updates] "Adding FLAG value {val} as {var}"
        trace[Tactic.prune_updates] "All variables in the Flag map: {(← get).flagVars}"
        pure (Update.flag i' var)
      | _ => failure
    toArmUpdatesAndStateVar curr_state rest (us ++ [update])
  | _ =>
    -- writes is just a state var at this point.
    let (prev_state_var : ArmStateVar) ← addAsStateVar writes
    let (curr_state_var : ArmStateVar) ← addAsStateVar curr_state
    trace[Tactic.prune_updates] "Current State: {curr_state} var: {curr_state_var}"
    trace[Tactic.prune_updates] "Previous State: {writes} var: {prev_state_var}"
    trace[Tactic.prune_updates] "All Updates: {us}"
    return (curr_state_var, us, prev_state_var)

partial def toArmExpr? (e : Lean.Expr) : M (Option ArmExpr) :=
  withTraceNode m!"toArmExpr?" (tag := "toArmExpr?") <| do
  match_expr e with
  | Eq α s writes =>
    let_expr ArmState ← α | failure
    let (curr_state, writes, prev_state) ← toArmUpdatesAndStateVar s writes []
    return some { curr_state, writes, prev_state }
  | _ => failure

def run (x : M α) : MetaM (α × State) := do
  let (a, s) ← x.run {}
  return (a, s)

end ToArmExpr

def toContextExpr (s : ToArmExpr.State) : MetaM Lean.Expr :=
  withTraceNode m!"toContextExpr" (tag := "toContextExpr") <| do
  let state_ctx ← mkListLit (mkConst ``ArmState) s.stateVars.toList
  let err_ctx   ← (mkListLit (mkConst ``StateError) s.errVars.toList)
  let pc_ctx    ← (mkListLit (← mkAppM ``BitVec #[mkNatLit 64]) s.pcVars.toList)
  let gpr_ctx   ← (mkListLit (← mkAppM ``BitVec #[mkNatLit 64]) s.gprVars.toList)
  let sfp_ctx   ← (mkListLit (← mkAppM ``BitVec #[mkNatLit 128]) s.sfpVars.toList)
  let flag_ctx  ← (mkListLit (← mkAppM ``BitVec #[mkNatLit 1]) s.flagVars.toList)
  let ans := (mkAppN (mkConst ``ArmConstr.Context.mk)
                      #[state_ctx, err_ctx, pc_ctx, gpr_ctx, sfp_ctx, flag_ctx])
  trace[Tactic.prune_updates] m!"ArmConstr.Context: {ans}"
  return ans

abbrev mkAuxDecl := Lean.Elab.Tactic.BVDecide.Frontend.mkAuxDecl

-- (FIXME) Better formatting; change into code action, etc.!
def toArmMessageData (e : Expr) (s : ToArmExpr.State) : MessageData :=
  let curr_state := s.stateVars[e.curr_state]!
  let prev_state := s.stateVars[e.prev_state]!
  let writes := go e.writes prev_state s 0
  m!"{curr_state} = {writes}"
  where go (us : Updates) (prev_state : Lean.Expr)
           (s : ToArmExpr.State) (paren_count : Nat) :=
    match us with
    | [] =>
        let closing_parens := List.asString (List.replicate paren_count ')')
        m!"{prev_state}{closing_parens}"
    | u :: rest =>
      let m :=
        match u with
        | .err v => m!"(w .ERR ({s.errVars[v]!}) "
        | .pc v => m!"(w .PC ({s.pcVars[v]!}) "
        | .gpr i v => m!"(w (.GPR {i}) ({s.gprVars[v]!}) "
        | .sfp i v => m!"(w (.SFP {i}) ({s.sfpVars[v]!}) "
        | .flag i v => m!"(w (.FLAG {i}) ({s.flagVars[v]!}) "
      m!"{m} {go rest prev_state s (1 + paren_count)}"

def ArmExprPruned? (refl_proof_name : Name) (e : Lean.Expr) :
  MetaM (Option (Lean.Expr × Lean.Expr)) :=
  withTraceNode m!"ArmExprPruned?" (tag := "ArmExprPruned?") <| do
  let validate ←(getBoolOption `Tactic.prune_updates.validate)
  let (some arm_expr, state) ←
    ToArmExpr.run (ToArmExpr.toArmExpr? e) | return none
  trace[Tactic.prune_updates] "Arm Expr: {arm_expr}"
  trace[Tactic.prune_updates] "State Context: {state.stateVars}"
  trace[Tactic.prune_updates] "ERR Context: {state.errVars}"
  trace[Tactic.prune_updates] "PC Context: {state.pcVars}"
  trace[Tactic.prune_updates] "GPR Context: {state.gprVars}"
  trace[Tactic.prune_updates] "SFP Context: {state.sfpVars}"
  trace[Tactic.prune_updates] "Flag Context: {state.flagVars}"
  let arm_expr_pruned := arm_expr.prune
  trace[Tactic.prune_updates] "Pruned Arm Expr: {arm_expr_pruned}"

  let ctx_expr ← toContextExpr state
  if validate then
    check ctx_expr
    trace[Tactic.prune_updates] "Checked context expressions: {ctx_expr}"

  let answer := toArmMessageData arm_expr_pruned state
  trace[Tactic.prune_updates.answer] "Pruned Answer: {answer}"

  let auxValue := mkApp2 (mkConst ``ArmConstr.Expr.isPruned)
                         (toExpr arm_expr) (toExpr arm_expr_pruned)
  trace[Tactic.prune_updates] "Aux Value: {auxValue}"
  mkAuxDecl refl_proof_name auxValue (mkConst ``Bool)

  let refl_proof :=
    mkApp3
    (mkConst ``Lean.ofReduceBool)
    (mkConst refl_proof_name)
    (toExpr true)
    (← mkEqRefl (toExpr true))

  if validate then
    check refl_proof
    trace[Tactic.prune_updates] "Checked reflection proof: {refl_proof}"

  let p := mkAppN (mkConst ``ArmConstr.Expr.eq_true_of_denote)
                    #[ctx_expr,
                      (toExpr arm_expr),
                      (toExpr arm_expr_pruned),
                      refl_proof]
  if validate then
    check p
    trace[Tactic.prune_updates] "Checked proof: {p}"
  return some (mkConst ``True, p)

def ReflectionProofName : Lean.Elab.TermElabM Name := do
  Lean.Elab.Term.mkAuxName `_armexpr_reflection_def

open Lean.Elab.Tactic in
elab "prune_updates" h_state_eq:term : tactic =>
  withTraceNode m!"prune_updates" (tag := "prune_updates") <| withMainContext do
  trace[Tactic.prune_updates] "h_state_eq: {h_state_eq}"
  let h_state_eq_expr ← elabTerm h_state_eq none
  let hStateEq ← inferType h_state_eq_expr
  trace[Tactic.prune_updates] "hStateEq: {hStateEq}"
  let refl_proof_name ← ReflectionProofName
  let some (_, e) ← ArmExprPruned? refl_proof_name hStateEq | return
  trace[Tactic.prune_updates] "Ctor of Proof after ArmExprPruned?: {e.ctorName}"
  trace[Tactic.prune_updates] "Proof after ArmExprPruned?: {e}"
  /-
  The rest of this code is heavily borrowed from `myApply` in Metaprogramming in
  Lean 4
  (https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html)
  -/
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← goal.getType
  let type ← inferType e
  trace[Tactic.prune_updates] "Target: {target}"
  trace[Tactic.prune_updates] "Proof, after `inferType`: {type}"
  -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
  -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `proof_type` does
  -- not have this form, `args` is empty and `conclusion = type`.)
  let (args, _, conclusion) ← forallMetaTelescopeReducing type
  trace[Tactic.prune_updates] "Args: {args}"
  trace[Tactic.prune_updates] "Conclusion: {conclusion}"
  if ← isDefEq target conclusion then
    trace[Tactic.prune_updates] "Target and conclusion are DefEq!"
    -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
    -- metavariables in `args`.
    if ← isDefEq args[0]! h_state_eq_expr then
    trace[Tactic.prune_updates] "Args[0]! and h_state_eq_expr are DefEq!"
    let new_goal_term := mkAppN e args
    trace[Tactic.prune_updates] "New Goal: {new_goal_term}"
    goal.assign new_goal_term
    -- `isDefEq` may have assigned some of the `args`. Report the rest as new
    -- goals.
    let newGoals ← args.filterMapM λ mvar => do
      let mvarId := mvar.mvarId!
      if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
        return some mvarId
      else
        return none
    trace[Tactic.prune_updates] "newGoals: {newGoals.toList}"
    setGoals newGoals.toList
  else
    -- If the conclusion does not unify with the target, throw an error.
    throwTacticEx `prune_updates goal m!"{e} is not applicable to goal with target {target}"

namespace ArmConstr

section Tests

#time
-- set_option trace.Tactic.prune_updates.answer true in
private theorem example1
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 0#5) x1 s0))) :
  s1 = (w (.GPR 0x00#5) x0  (w (.GPR 0x01#5) x1  s0)) := by
  prune_updates h_s1
  done

-- #print example1

#time
private theorem example2
  (h_s1 : s1 = w (.GPR 1#5) (x100 + x100') (w (.GPR 0#5) x500 (w (.GPR 8#5) x1 s0))) :
  s1 = w (.GPR 0#5) x500 (w (.GPR 1#5) (x100 + x100') (w (.GPR 8#5) x1 s0)) := by
  prune_updates h_s1
  done

#time
-- set_option trace.Tactic.prune_updates.answer true in
private theorem example3
  (h_s1 : s1 =
   (w StateField.PC (if ¬r (StateField.GPR 0x2#5) s = 0x0#64 then 0x126500#64 else 0x126c94#64)
    (w (StateField.SFP 0x3#5)
      (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x3#5) s) (r (StateField.SFP 0x1d#5) s) 0x0#128)
      (w StateField.PC 0x126c8c#64
        (w (StateField.SFP 0x2#5)
          (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x2#5) s) (r (StateField.SFP 0x1c#5) s)
            0x0#128)
          (w StateField.PC 0x126c88#64
            (w (StateField.SFP 0x1#5)
              (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x1#5) s) (r (StateField.SFP 0x1b#5) s)
                0x0#128)
              (w StateField.PC 0x126c84#64
                (w (StateField.SFP 0x0#5)
                  (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x0#5) s)
                    (r (StateField.SFP 0x1a#5) s) 0x0#128)
                  s))))))))) :
  s1 = (w .PC (if ¬r (StateField.GPR 2#5) s = 0#64 then 1205504#64
    else
      1207444#64)  (w (.SFP 0x00#5) (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0#5) s)
      (r (StateField.SFP 26#5) s)
      0#128)  (w (.SFP 0x01#5) (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 1#5) s)
      (r (StateField.SFP 27#5) s)
      0#128)  (w (.SFP 0x02#5) (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 2#5) s)
      (r (StateField.SFP 28#5) s)
      0#128)  (w (.SFP 0x03#5) (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 3#5) s)
      (r (StateField.SFP 29#5) s) 0#128)  s)))))
  := by
  prune_updates h_s1
  done

end Tests
