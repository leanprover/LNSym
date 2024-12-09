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

structure Context where
  stateVars    : Array Lean.Expr := #[]
  gprVars      : Array Lean.Expr := #[]
  sfpVars      : Array Lean.Expr := #[]
  flagVars     : Array Lean.Expr := #[]
  errVars      : Array Lean.Expr := #[]
  pcVars       : Array Lean.Expr := #[]

def mkContextFromState (s : State) : Context :=
  ⟨
    s.stateVars,
    s.gprVars,
    s.sfpVars,
    s.flagVars,
    s.errVars,
    s.pcVars
  ⟩

abbrev M := StateRefT State MetaM


def addAsStateVar (e : Lean.Expr) : M Nat := do
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

partial def toArmUpdatesAndStateVar (writes : Lean.Expr) (us : ArmUpdates) :
  M (ArmUpdates × ArmStateVar) :=
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
    toArmUpdatesAndStateVar rest (us ++ [update])
  | _ =>
    -- writes is just a state var at this point.
    let (prev_state_var : ArmStateVar) ← addAsStateVar writes
    trace[Tactic.prune_updates] "Previous State: {writes} var: {prev_state_var}"
    trace[Tactic.prune_updates] "All Updates: {us}"
    return (us, prev_state_var)

partial def toArmExpr? (e : Lean.Expr) : M (Option ArmExpr) :=
  withTraceNode m!"toArmExpr?" (tag := "toArmExpr?") <| do
  match_expr e with
  | Eq α s writes =>
    let_expr ArmState ← α | failure
    let (writes, prev_state) ← toArmUpdatesAndStateVar writes []
    let (curr_state : ArmStateVar) ← addAsStateVar s
    return some { curr_state, writes, prev_state }
  | _ => failure

def run (x : M α) (s : State := {}): MetaM (α × State) := do
  let (a, s) ← x.run s
  return (a, s)

end ToArmExpr

def toContextExpr (s : ToArmExpr.Context) : MetaM Lean.Expr :=
  withTraceNode m!"toContextExpr" (tag := "toContextExpr") <| do
  let state_ctx ←  mkListLit (mkConst ``ArmState) s.stateVars.toList
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
def toArmMessageData (prev_state : StateVar) (updates : Updates) (s : ToArmExpr.Context) : MessageData :=
  let prev_state := s.stateVars[prev_state]!
  let writes := go updates prev_state s 0
  m!"{writes}"
  where go (us : Updates) (prev_state : Lean.Expr)
           (s : ToArmExpr.Context) (paren_count : Nat) :=
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

def ArmExprBuildProofTerm (state : ToArmExpr.Context) (lhs_writes rhs_writes : Updates)
  (refl_proof_name : Name) (validate : Bool) (s0 : ArmStateVar): MetaM Lean.Expr := do
  let ctx_expr ← toContextExpr state
  let prune_eq := mkApp2 (mkConst ``ArmConstr.Updates.prune_eq)
                  (toExpr lhs_writes) (toExpr rhs_writes)
  mkAuxDecl refl_proof_name prune_eq (mkConst ``Bool)
  let refl_proof :=
    mkApp3
    (mkConst ``Lean.ofReduceBool)
    (mkConst refl_proof_name)
    (toExpr true)
    (← mkEqRefl (toExpr true))

  if validate then
    check refl_proof
    trace[Tactic.prune_updates] "Checked reflection proof: {refl_proof}"

  let p := mkAppN (mkConst ``ArmConstr.Expr.eq_of_denote_writes)
                  #[ctx_expr,
                    (toExpr lhs_writes),
                    (toExpr rhs_writes),
                    (mkNatLit s0),
                    refl_proof]
  if validate then
    check p
    trace[Tactic.prune_updates] "Checked proof: {p}"
  return p

def withAbstractGPRAtoms (state : ToArmExpr.Context) (k : ToArmExpr.Context → MetaM (Option Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  let atoms := state.gprVars
  let declsGPR : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) ← atoms.mapM fun _ => do
    return ((← mkFreshUserName `x), fun _ => return (mkApp (mkConst ``BitVec) (mkNatLit 64)))
  withLocalDeclsD declsGPR fun ctxt => do
    let state := {state with gprVars := ctxt}
    let some p ← k state | return none
    let p := mkAppN (← mkLambdaFVars ctxt p) atoms
    return some p

def withAbstractStateAtoms (state : ToArmExpr.Context) (k : ToArmExpr.Context → MetaM (Option Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  let atoms := state.stateVars
  let declsGPR : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) ← atoms.mapM fun _ => do
    return ((← mkFreshUserName `x), fun _ => return mkConst ``ArmState)
  withLocalDeclsD declsGPR fun ctxt => do
    let state := {state with stateVars := ctxt}
    let some p ← k state | return none
    let p := mkAppN (← mkLambdaFVars ctxt p) atoms
    return some p

def withAbstractSFPAtoms (state : ToArmExpr.Context) (k : ToArmExpr.Context → MetaM (Option Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  let atoms := state.sfpVars
  let declsGPR : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) ← atoms.mapM fun _ => do
    return ((← mkFreshUserName `x), fun _ => return mkApp (mkConst ``BitVec) (mkNatLit 128))
  withLocalDeclsD declsGPR fun ctxt => do
    let state := {state with sfpVars := ctxt}
    let some p ← k state | return none
    let p := mkAppN (← mkLambdaFVars ctxt p) atoms
    return some p

def withAbstractPCAtoms (state : ToArmExpr.Context) (k : ToArmExpr.Context → MetaM (Option Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  let atoms := state.pcVars
  let declsGPR : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) ← atoms.mapM fun _ => do
    return ((← mkFreshUserName `x), fun _ => return mkApp (mkConst ``BitVec) (mkNatLit 64))
  withLocalDeclsD declsGPR fun ctxt => do
    let state := {state with pcVars := ctxt}
    let some p ← k state | return none
    let p := mkAppN (← mkLambdaFVars ctxt p) atoms
    return some p

def withAbstractFlagAtoms (state : ToArmExpr.Context) (k : ToArmExpr.Context → MetaM (Option Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  let atoms := state.flagVars
  let declsGPR : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) ← atoms.mapM fun _ => do
    return ((← mkFreshUserName `x), fun _ => return mkApp (mkConst ``BitVec) (mkNatLit 1))
  withLocalDeclsD declsGPR fun ctxt => do
    let state := {state with flagVars := ctxt}
    let some p ← k state | return none
    let p := mkAppN (← mkLambdaFVars ctxt p) atoms
    return some p

def withAbstractErrAtoms (state : ToArmExpr.Context) (k : ToArmExpr.Context → MetaM (Option Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  let atoms := state.errVars
  let declsGPR : Array (Name × (Array Lean.Expr → MetaM Lean.Expr)) ← atoms.mapM fun _ => do
    return ((← mkFreshUserName `x), fun _ => return mkConst ``StateError)
  withLocalDeclsD declsGPR fun ctxt => do
    let state := {state with errVars := ctxt}
    let some p ← k state | return none
    let p := mkAppN (← mkLambdaFVars ctxt p) atoms
    return some p

def withAbstractAtoms (state : ToArmExpr.Context) (k : ToArmExpr.Context → MetaM (Option Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  withAbstractStateAtoms state fun s1 =>
    withAbstractGPRAtoms s1 fun s2 =>
      withAbstractSFPAtoms s2 fun s3 =>
        withAbstractPCAtoms s3 fun s4 =>
          withAbstractFlagAtoms s4 fun s5 =>
            withAbstractErrAtoms s5 k

def ArmExprPruned? (refl_proof_name : Name) (e : Lean.Expr) :
  MetaM (Option Lean.Expr) :=
  withTraceNode m!"ArmExprPruned?" (tag := "ArmExprPruned?") <| do
  let validate ←(getBoolOption `Tactic.prune_updates.validate)
  let_expr Eq _ lhs rhs := e | return none
  let ((lhs_writes, lhs_s0), state) ←
    ToArmExpr.run (ToArmExpr.toArmUpdatesAndStateVar lhs []) {}
  let ctx := ToArmExpr.mkContextFromState state
  trace[Tactic.prune_updates.answer] "Pruned Updates: {toArmMessageData lhs_s0 lhs_writes.prune ctx}"
  if ←(getBoolOption `Tactic.prune_updates.only_answer) then
    return none
  let ((rhs_writes, rhs_s0), state) ←
    ToArmExpr.run (ToArmExpr.toArmUpdatesAndStateVar rhs []) state
  trace[Tactic.prune_updates] "LHS writes: {lhs_writes}"
  trace[Tactic.prune_updates] "RHS writes: {rhs_writes}"
  trace[Tactic.prune_updates] "State Context: {state.stateVars}"
  trace[Tactic.prune_updates] "ERR Context: {state.errVars}"
  trace[Tactic.prune_updates] "PC Context: {state.pcVars}"
  trace[Tactic.prune_updates] "GPR Context: {state.gprVars}"
  trace[Tactic.prune_updates] "SFP Context: {state.sfpVars}"
  trace[Tactic.prune_updates] "Flag Context: {state.flagVars}"
  --  let arm_expr_pruned := lhs_arm_expr.prune
  --  trace[Tactic.prune_updates] "Pruned Arm Expr: {arm_expr_pruned}"
  --
  withAbstractAtoms ctx fun ctx' => do
    if lhs_s0 = rhs_s0 then
      return some (← ArmExprBuildProofTerm ctx'
                     lhs_writes rhs_writes refl_proof_name validate lhs_s0)
    else
      return none

def ReflectionProofName : Lean.Elab.TermElabM Name := do
  Lean.Elab.Term.mkAuxName `_armexpr_reflection_def

open Lean.Elab.Tactic in
elab "prune_updates" : tactic =>
  withTraceNode m!"prune_updates" (tag := "prune_updates") <| withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  trace[Tactic.prune_updates] "Goal: {goal}"
  let goal_type ← goal.getType
  trace[Tactic.prune_updates] "Goal Type: {goal_type}"
  let refl_proof_name ← ReflectionProofName
  let some p ← ArmExprPruned? refl_proof_name goal_type | return
  trace[Tactic.prune_updates] "Ctor of Proof after ArmExprPruned?: {p.ctorName}"
  trace[Tactic.prune_updates] "Proof after ArmExprPruned?: {p}"
  let proof_type ← inferType p
  trace[Tactic.prune_updates] "Proof Type: {proof_type}"
  Lean.setReducibilityStatus `List.getD .reducible
  Lean.setReducibilityStatus `List.get? .reducible
  Lean.setReducibilityStatus `Option.getD .reducible
  Lean.setReducibilityStatus `Option.getD.match_1 .reducible
  -- Lean.setIrreducibleAttribute `Nat.casesOn
  trace[Tactic.prune_updates] "Reduced proof_type: \
                                {← withTransparency .reducible (reduceAll proof_type)}"
  if (← withTransparency .reducible (isDefEq goal_type proof_type)) then
    trace[Tactic.prune_updates] "goal_type and proof_type are DefEq!"
    -- if (← withTransparency .reducible
    --       (isDefEq (mkMVar goal) (← mkExpectedTypeHint p goal_type))) then
    closeMainGoal `prune_updates (← mkExpectedTypeHint p goal_type)
  else
    -- If the proof_type does not unify with goal_type, throw an error.
    throwTacticEx `prune_updates goal m!"{p} is not applicable to goal {goal_type}"

namespace ArmConstr

section Tests

#time
-- set_option diagnostics true in
-- set_option diagnostics.threshold 5 in
-- set_option trace.Tactic.prune_updates true in
-- set_option pp.all true in
private theorem example1
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 0#5) x1 s0))) :
  s1 = (w (.GPR 0x00#5) x0  (w (.GPR 0x01#5) x1  s0)) := by
  rw [h_s1]
  prune_updates
  done

/--
info: private theorem ArmConstr.ArmConstr.example1 : ∀ {s1 : ArmState} {x0 : state_value (StateField.GPR 0#5)}
  {x1 : state_value (StateField.GPR 1#5)} {s0 : ArmState},
  s1 = w (StateField.GPR 0#5) x0 (w (StateField.GPR 1#5) x1 (w (StateField.GPR 0#5) x1 s0)) →
    s1 = w (StateField.GPR 0#5) x0 (w (StateField.GPR 1#5) x1 s0) :=
fun {s1} {x0} {x1} {s0} h_s1 =>
  Eq.mpr (id (congrArg (fun _a => _a = w (StateField.GPR 0#5) x0 (w (StateField.GPR 1#5) x1 s0)) h_s1))
    (id
      ((fun x =>
          (fun x_1 x_2 =>
              eq_of_denote_writes { state := [x], err := [], pc := [], gpr := [x_1, x_2], sfp := [], flag := [] }
                [Update.gpr (0#5) 0, Update.gpr (1#5) 1, Update.gpr (0#5) 1] [Update.gpr (0#5) 0, Update.gpr (1#5) 1] 0
                (ofReduceBool ArmConstr.ArmConstr.example1._armexpr_reflection_def_1 true (Eq.refl true)))
            x0 x1)
        s0))
-/
#guard_msgs in
#print example1

/-

set_option trace.Tactic.prune_updates.answer true in
theorem timeout_example (test : Bool)
  (h_step : s' = w (StateField.GPR 0x1#5)
                  (if (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xffffffffffffffff#64 0x1#1).snd.z = 0#1 then
                   (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xffffffffffffffff#64 0x1#1).fst
                  else
                   (AddWithCarry (r (StateField.GPR 0x2#5) s) 0#64 0x1#1).fst)
                  (w StateField.PC 0x126520#64
                    (w (StateField.SFP 0x1d#5) (r (StateField.SFP 0x3#5) s) s))) :
  s' =  (w .PC (1205536#64)
              (w (.GPR 0x01#5)
                  (if (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xffffffffffffffff#64 0x1#1).snd.z = 0#1 then
                    (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xffffffffffffffff#64 0x1#1).fst
                  else
                    (AddWithCarry (r (StateField.GPR 0x2#5) s) 0#64 0x1#1).fst)
                  (w (.SFP 0x1d#5) (r (StateField.SFP 3#5) s)  s)))  := by
  rw [h_step]
  prune_updates

-- set_option allowUnsafeReducibility true
seal AddWithCarry
-- seal Prod.snd
-- seal PState.z
-- seal PFlag.Z

#time
-- set_option trace.Tactic.prune_updates.answer true in
set_option diagnostics true in
set_option diagnostics.threshold 5 in
-- set_option trace.Tactic.prune_updates true in
set_option maxRecDepth 2000 in
theorem timeout_example1
  (h_step : s' = w (StateField.FLAG PFlag.Z)
                   (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xff#64 0x1#1).snd.z
                  (w StateField.PC 0x126520#64
                    (w (StateField.SFP 0x1d#5) (r (StateField.SFP 0x3#5) s) s))) :
  s' = (w .PC (1205536#64)  (w (.SFP 0x1d#5) (r (StateField.SFP 3#5)
      s)  (w (.FLAG PFlag.Z) (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xff#64 0x1#1).snd.z s)))  := by
  rw [h_step]
  prune_updates


seal AddWithCarry
set_option allowUnsafeReducibility true in
seal Prod.snd

-- #time
-- set_option diagnostics true in
-- set_option diagnostics.threshold 5 in
-- -- set_option trace.Tactic.prune_updates true in
-- set_option trace.Tactic.prune_updates.answer true in
-- set_option maxRecDepth 2000 in
-- theorem timeout_example2
--   (h_step : s' = w (StateField.GPR 0x1#5)
--     (if ¬(AddWithCarry (r (StateField.GPR 0x2#5) s) 0xffffffffffffffff#64 0x1#1).snd.z = 0x1#1 then
--       r (StateField.GPR 0x1#5) s
--     else r (StateField.GPR 0x1#5) s - 0x80#64)
--     (w StateField.PC 0x126520#64
--       (w (StateField.SFP 0x1d#5) (r (StateField.SFP 0x3#5) s) s))) :
--   s' =  (w .PC (1205536#64)  (w (.GPR 0x01#5) (if
--         ¬(AddWithCarry (r (StateField.GPR 2#5) s) 0xffffffffffffffff#64 1#1).snd.z = 1#1 then r (StateField.GPR 1#5) s
--     else r (StateField.GPR 1#5) s - 128#64)  (w (.SFP 0x1d#5) (r (StateField.SFP 3#5) s)  s)))  := by
--   rw [h_step]
--   prune_updates

/-
#time
-- set_option diagnostics true in
-- set_option diagnostics.threshold 5 in
-- set_option trace.Tactic.prune_updates true in
-- set_option maxRecDepth 2000 in
theorem timeout_example2
  (h_step : s' = w (StateField.GPR 0x1#5)
    (if ¬(AddWithCarry (r (StateField.GPR 0x2#5) s) 0xffff#64 0x1#1).snd.z = 0x1#1 then
      r (StateField.GPR 0x1#5) s
    else r (StateField.GPR 0x1#5) s - 0x80#64)
    (w StateField.PC 0x126520#64
      (w (StateField.SFP 0x1d#5) (r (StateField.SFP 0x3#5) s)
        (w StateField.PC 0x126518#64
          (w (StateField.SFP 0x1c#5) (r (StateField.SFP 0x2#5) s)
            (w StateField.PC 0x126514#64
              (w (StateField.SFP 0x1b#5) (r (StateField.SFP 0x1#5) s)
                (w StateField.PC 0x126510#64
                  (w (StateField.SFP 0x1a#5) (r (StateField.SFP 0x0#5) s)
                    (w (StateField.GPR 0x4#5) (r (StateField.GPR 0x1#5) s - 0x80#64)
                      (w StateField.PC 0x12650c#64
                        (w (StateField.GPR 0x2#5) (r (StateField.GPR 0x2#5) s - 0x1#64)
                          (w (StateField.FLAG PFlag.V)
                            (AddWithCarry (r (StateField.GPR 0x2#5) s) 0x0#64 0x1#1).snd.v
                            (w (StateField.FLAG PFlag.C)
                              (AddWithCarry (r (StateField.GPR 0x2#5) s) 0x0#64 0x1#1).snd.c
                              (w (StateField.FLAG PFlag.Z)
                                (AddWithCarry (r (StateField.GPR 0x2#5) s) 0x0#64 0x1#1).snd.z
                                (w (StateField.FLAG PFlag.N)
                                  (AddWithCarry (r (StateField.GPR 0x2#5) s) 0x0#64 0x1#1).snd.n
                                  (w StateField.PC 0x126508#64
                                    (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                      (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                        s))))))))))))))))))) :
  s' = (w .PC (1205536#64)  (w (.GPR 0x01#5) (if
        ¬(AddWithCarry (r (StateField.GPR 2#5) s) 0xffff#64 1#1).snd.z = 1#1 then r (StateField.GPR 1#5) s
    else
      r (StateField.GPR 1#5) s - 128#64)
      (w (.GPR 0x02#5) (r (StateField.GPR 2#5) s - 1#64)
        (w (.GPR 0x03#5) (r (StateField.GPR 3#5) s + 16#64)
         (w (.GPR 0x04#5) (r (StateField.GPR 1#5) s - 128#64)
          (w (.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 3#5) s) s)
            (w (.SFP 0x1a#5) (r (StateField.SFP 0#5) s)
             (w (.SFP 0x1b#5) (r (StateField.SFP 1#5) s)
               (w (.SFP 0x1c#5) (r (StateField.SFP 2#5) s)
                (w (.SFP 0x1d#5) (r (StateField.SFP 3#5) s)
                 (w (.FLAG PFlag.N) ((AddWithCarry (r (StateField.GPR 2#5) s) 0x0#64 1#1).snd.n)
                   (w (.FLAG PFlag.Z) ((AddWithCarry (r (StateField.GPR 2#5) s) 0x0#64 1#1).snd.z)
                     (w (.FLAG PFlag.C) ((AddWithCarry (r (StateField.GPR 2#5) s) 0x0#64 1#1).snd.c)
                      (w (.FLAG PFlag.V) ((AddWithCarry (r (StateField.GPR 2#5) s) 0x0#64 1#1).snd.v) s)))))))))))))) := by
    rw [h_step]
    prune_updates
-/
-/
end Tests
