/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Tactics.Common
import Lean
open Lean Elab Tactic Expr Meta
open BitVec

/-
Tactic `intro_change_hyps h`:

The tactic `intro_change_hyps` operates on a given declaration `h` in the
goal, where `h` is of the form
`state_var_new = write ... (write ... state_var_old)`.
It then introduces a hypothesis involving corresponding `read` terms, and also
attempts to prove it. Additionally, it introduces another hypothesis stating which
state components remained unchanged.

Here is an example:

Goal:
h : s1 = w (StateField.GPR 31#5) 1#64 (w StateField.PC 2#64 s0)
...
|-
conclusion

`intro_change_hyps h` modifies the goal as follows; note the new hypotheses
`h_s1_changed` and `h_s1_unchanged`. `intro_change_hyps h` also attempts to
prove each of these new hypotheses using `simp/decide` with theorems in
our own custom simp sets, `minimal_theory`, `bitvec_rules`, and
`state_simp_rules`.

Goal:
h : s1 = w (StateField.GPR 31#5) 1#64 (w StateField.PC 2#64 s0)
h_s1_changed : r (StateField.GPR 31#5) s1 = 1#64 ∧ r StateField.PC s1 = 2#64
h_s1_unchanged : ∀ (f : StateField),
  f ∉ [StateField.GPR 31#5, StateField.PC] → r f s1 = r f s0

...
|-
conclusion

TODO: Introduce hypotheses for memory reads/writes as well.
-/


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

def expr_in (x : Expr) (xs : List Expr) : Bool :=
  match xs with
  | [] => false
  | e :: rest => if e == x then true else expr_in x rest

partial def collectReads (writes : Expr) (st_var : Expr)
  (seen_fields : List Expr) (collected : List Expr) :
  MetaM (Expr × List Expr × List Expr) := do
  if writes.isFVar then
    return (writes, seen_fields, collected)
  else
    match_expr writes with
    | w field val rest =>
      let some _field_str ←
        getStateFieldString? field |
        throwError m!"[collectReads] Unexpected field argument of function w: {field}"
      if expr_in field seen_fields then
        -- Skip if we have already generated a hypothesis for this field.
        collectReads rest st_var seen_fields collected
      else
        let val_type ← whnfD (← inferType val)
        let read_term := mkAppN (Expr.const ``Eq [1])
                          #[val_type,
                             (mkAppN (Expr.const ``r []) #[field, st_var]),
                             val]
        collectReads rest st_var (field :: seen_fields) (read_term :: collected)

    | write_mem_bytes num_bytes address value rest =>
      -- TODO: Handle overlapping memory writes.
      let num_bytes ← whnfD num_bytes
      let address ← whnfR address
      let value ← whnfR value
      let value_type ← whnfD (← inferType value)
      let read_term := mkAppN (Expr.const ``Eq [1])
                          #[value_type,
                             (mkAppN (Expr.const ``read_mem_bytes [])
                                  #[num_bytes, address, st_var]),
                             value]
      collectReads rest st_var seen_fields (read_term :: collected)
      -- logInfo m!"Skipping hypothesis generation for memory writes for now."
      -- collectReads rest st_var seen_fields collected

    -- | ite _ c _ t e =>
    --   let (err, ok_nest) :=
    --     match_expr c with
    --     | Eq _ lhs rhs =>
    --       match_expr lhs with
    --       | CheckSPAlignment _ =>
    --         let ok_nest := if rhs == mkConst ``false then e else t
    --         (false, ok_nest)
    --       | _ => (true, lhs)
    --     | _ => (true, c)
    --   if err == false then
    --     collectReads ok_nest st_var seen_fields collected
    --   else
    --     throwError m!"[collectReads] If term encountered: if {c} then {t} else {e}"

    | _ =>
      throwError m!"[collectReads] Unexpected write term encountered: {writes}"

def genUnchangedAntecedent (var : Expr) (fields : List Expr) (acc : List Expr)
  : Expr :=
  match fields with
  | [] => List.foldl mkAnd acc.head! acc.tail!
  | fld :: rest =>
    let neq_term := (mkAppN (Expr.const ``Ne [1])
                     #[(mkConst ``StateField), var, fld])
    genUnchangedAntecedent var rest (neq_term :: acc)

def unchangedFieldProp (st_var : Expr) (prev_st_var : Expr)
  (seen_fields : List Expr) : Expr :=
   let antecedent := fun f => genUnchangedAntecedent f seen_fields []
   let consequent := fun f =>
                      mkAppN (Expr.const ``Eq [1])
                          #[(mkApp (mkConst ``state_value) f),
                             (mkAppN (Expr.const ``r []) #[f, st_var]),
                             (mkAppN (Expr.const ``r []) #[f, prev_st_var])]
   let expr := forallE `f (mkConst ``StateField)
                (forallE Lean.Name.anonymous
                  (antecedent (Lean.Expr.bvar 0))
                  (consequent (Lean.Expr.bvar 1))
                  (Lean.BinderInfo.default))
                Lean.BinderInfo.default
  expr

-- def foo : Expr := unchangedFieldProp (mkConst `s1) (mkConst `s0)
--                     [(mkConst ``StateField.PC),
--                      (mkConst ``StateField.ERR)]
-- elab "foo" : term => return foo
-- #check foo

def getChangedUnchangedExprs (step : Expr) (program : Expr) : MetaM (Expr × Expr × Expr) := do
  let_expr Eq _ _ prog ← program |
           throwError m!"[getChangedUnchangedExprs] Unsupported program expression: {program}"
  let_expr Eq _ st_var nest ← step |
           throwError m!"[getChangedUnchangedExprs] Unsupported step expression: {step}"
  -- Remove metadata, if present, from st_var and nest.
  let st_var := consumeMData st_var
  let nest := consumeMData nest
  -- logInfo m!"var: {st_var} nest: {nest}"
  if ! (st_var.isFVar && nest.isApp) then
      throwError m!"[getChangedUnchangedExprs] Unexpected expression(s). We expect \
                  the state variable on the LHS to be an FVar and the \
                  term on the RHS to be a function application. Here is \
                  what they actually are: \
                  st_var: {st_var.ctorName}; nest: {nest.ctorName}."
  else
    let (prev_st_var, seen_fields, reads) ← collectReads nest st_var [] []
    -- let changed_expr := List.foldl mkAnd (mkConst ``True) reads
    let program_unchanged_expr :=
      (mkAppN (mkConst ``Eq [1])
                        #[(mkConst ``Program),
                          (mkAppN (mkConst ``ArmState.program) #[st_var]),
                          prog])
    let error_none_expr :=
      (mkAppN (mkConst ``Eq [1])
                        #[(mkConst ``StateError),
                          (mkAppN (mkConst ``r) #[mkConst ``StateField.ERR, st_var]),
                          mkConst ``StateError.None])
    let changed_expr := List.foldl mkAnd program_unchanged_expr (error_none_expr :: reads)
    let unchanged_expr := unchangedFieldProp st_var prev_st_var seen_fields
    return (st_var, changed_expr, unchanged_expr)

partial def introChangeHyps (goal : MVarId) (hStep : Expr) (hProgram : Expr) (hyp_prefix : String):
  TacticM Bool := goal.withContext do
    let step ← inferType hStep
    let program ← inferType hProgram
    let (st_var, changed_hyp, unchanged_hyp) ← getChangedUnchangedExprs step program
    -- logInfo m!"unchanged_hyp: {unchanged_hyp}"
    let lctx ← getLCtx
    let matching_decls := filterDeclsWithPrefix lctx hyp_prefix.toName
    let (ctx, simprocs) ←
      LNSymSimpContext (config := {decide := true})
                       (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
                       (decls_to_unfold := #[])
                       (thms := #[])
                       (decls := matching_decls)
                       (simprocs := #[])
    let st_var_str := toString (← (getFVarLocalDecl st_var)).userName
    let (goal, maybe_changed_hyp_goal) ←
      introLNSymHyp goal st_var (gen_hyp_name st_var_str "changed")
        changed_hyp ctx simprocs
    if Option.isSome maybe_changed_hyp_goal then
      throwError m!"Could not prove the goal {maybe_changed_hyp_goal.get!}"
    let (goal, maybe_unchanged_hyp_goal) ←
      introLNSymHyp goal st_var (gen_hyp_name st_var_str "unchanged")
        unchanged_hyp ctx simprocs (subst? := true) (simp_new_goal? := false)
    if Option.isSome maybe_unchanged_hyp_goal then
      let unchanged_hyp_goal := Option.get! maybe_unchanged_hyp_goal
      unchanged_hyp_goal.withContext do
      let (_quant_f_fvarid, unchanged_hyp_goal) ←
        unchanged_hyp_goal.intro ("tmp_quant_f".toName)
      let (_quant_h_fvarid, unchanged_hyp_goal) ←
           unchanged_hyp_goal.intro ("tmp_quant_h_antecendent".toName)
      -- logInfo m!"unchanged_hyp_goal: {unchanged_hyp_goal}"
      -- let maybe_unchanged_hyp_goal ← LNSymSimp unchanged_hyp_goal ctx simprocs
      -- TODO: Use tmp_quant_* in the local context, instead of the more
      -- heavyweight simpTargetStar.
      let (maybe_unchanged_hyp_goal, _) ← simpTargetStar unchanged_hyp_goal ctx simprocs
      let maybe_unchanged_hyp_goal :=
        match maybe_unchanged_hyp_goal with
        | TacticResultCNM.modified id => some id
        | TacticResultCNM.closed => none
        | _ => some unchanged_hyp_goal
      if Option.isSome maybe_changed_hyp_goal then
        throwError m!"Could not prove the goal: {maybe_unchanged_hyp_goal.get!}"
    goal.withContext do
    replaceMainGoal [goal]
    return true

def introChangeHypsElab (h_step : Name) (h_program : Name) (hyp_prefix : String): TacticM Unit :=
  withMainContext
  (do
    let h_step ← getFVarFromUserName h_step
    let h_program ← getFVarFromUserName h_program
    let success ← introChangeHyps (← getMainGoal) h_step h_program hyp_prefix
    if ! success then
      failure)

elab "intro_change_hyps" h_step:ident h_program:ident hyp_prefix:str : tactic =>
  introChangeHypsElab (h_step.getId) (h_program.getId) (hyp_prefix.getString)
