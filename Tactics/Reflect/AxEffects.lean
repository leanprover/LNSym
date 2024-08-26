/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/

import Arm.State
import Tactics.Common
import Tactics.Attr
import Std.Data.HashMap

open Lean Meta

/-- A reflected ArmState field -/
structure AxEffects.FieldEffect where
  value : Expr
  /-- A proof that `r <field> <currentState> = <value>` -/
  proof : Expr
  deriving Repr
open AxEffects.FieldEffect

/-- `AxEffects` is an axiomatic representation of effects,
i.e., `AxEffects` transforms a description of an `ArmState` written as
a sequence of `w` and `write_mem`s to some initial state
into a set of hypotheses that relates reading fields from the final state
to the initial state.

It stores a hashmap from `StateField` to an expression, in terms of the fixed
initial state, that describes the value of the given field *after* the
writes.
Additionally, each field carries a proof that it is indeed the right value

Furthermore, we maintain a separate expression containing only the writes to
memory. -/
structure AxEffects where
  /-- The initial state -/
  initialState : Expr
  /-- The current state, generally expressed in "exploded form".
  That is, `currentState` is usually a sequence of `w`/`write_mem`s
  to the initial state -/
  currentState : Expr
  fields : Std.HashMap StateField AxEffects.FieldEffect
  /-- An expression that contains the proof of:
    ```lean
    ∀ (f : StateField), f ≠ <f₁> → ⋯ → f ≠ <fₙ> →
      r f <currentState> = r f <initialState> `
    ```
    where `f₁, ⋯, fₙ` are the keys of `fields`
  -/
  nonEffectProof : Expr
  /-- An expression of a (potentially empty) sequence of `write_mem`s
  to the initial state, which describes the effects on memory -/
  memoryEffect : Expr
  /-- An expression that contains the proof of:
    ```lean
    ∀ n addr,
      read_mem_bytes n addr <currentState>
      = read_mem_bytes n addr <memoryEffect>
    ``` -/
  memoryEffectProof : Expr
  /-- A proof that `<currentState>.program = <initialState>.program` -/
  programProof : Expr
  deriving Repr

namespace AxEffects

/-! ## Initial Reflected State -/

def initial (state : Expr) : AxEffects where
  initialState      := state
  currentState      := state
  fields            := .empty
  nonEffectProof    :=
    mkLambda `f .default (mkConst ``StateField) <|
      let rf := mkApp2 (mkConst ``r) (.bvar 0) state
      mkApp2 (.const ``Eq.refl [1]) (.const ``ArmState []) rf
  memoryEffect      := state
  memoryEffectProof :=
    let n8 (n : Expr) : Expr :=
      let N     := mkConst ``Nat
      let inst  := mkApp2 (.const ``instHMul [1]) N (.const ``instMulNat [])
      mkAppN (.const ``HMul.hMul [1]) #[N, N, N, inst, n, toExpr 8]

    mkLambda `n .default (mkConst ``Nat) <|
      let bv64 := mkApp (mkConst ``BitVec) (toExpr 64)
      mkLambda `addr .default bv64 <|
        let rm := mkApp3 (mkConst ``read_mem_bytes) (.bvar 1) (.bvar 0) state
        mkApp2 (.const ``Eq.refl [1]) (n8 <| .bvar 1) rm
  programProof      :=
    mkAppN (.const ``Eq.refl [1]) #[
      mkConst ``Program,
      mkApp (mkConst ``ArmState.program) state]

/-! ## ToMessageData -/

instance : ToMessageData FieldEffect where
  toMessageData := fun {value, proof} =>
    m!"\{ value := {value},\n  proof := {proof} }"

instance : ToMessageData (Std.HashMap StateField FieldEffect) where
  toMessageData map :=
    toMessageData map.toList

instance : ToMessageData AxEffects where
  toMessageData eff :=
    m!"\
    \{ initialState := {eff.initialState},
      currentState := {eff.currentState},
      fields := {eff.fields},
      nonEffectProof := {eff.nonEffectProof},
      memoryEffect := {eff.memoryEffect},
      memoryEffectProof := {eff.memoryEffectProof},
      programProof := {eff.programProof}
    }"

/-! ## Helpers -/

/--
Rewrites `e` via some `eq`, producing a proof `e = e'` for some `e'`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
-- source: https://github.com/leanprover-community/mathlib4/blob/b35703fe5a80f1fa74b82a2adc22f3631316a5b3/Mathlib/Lean/Expr/Basic.lean#L476-L477
private def rewrite (e eq : Expr) : MetaM Expr := do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'

/--
Rewrites the type of `e` via some `eq`, then moves `e` into the new type via `Eq.mp`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
-- source: https://github.com/leanprover-community/mathlib4/blob/b35703fe5a80f1fa74b82a2adc22f3631316a5b3/Mathlib/Lean/Expr/Basic.lean#L476-L477
private def rewriteType (e eq : Expr) : MetaM Expr := do
  mkEqMP (← rewrite (← inferType e) eq) e

/-- Get the value for a field, if one is stored in `eff.fields`,
or assemble an instantiation of the memory non-effects proof -/
def getField (eff : AxEffects) (fld : StateField) : MetaM FieldEffect :=
  let msg := m!"getField {fld}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    withTraceNode `Tactic.sym (fun _ => pure "current state") <| do
      trace[Tactic.sym] "{eff}"

    if let some val := eff.fields.get? fld then
      return val
    else
      let value := mkApp2 (mkConst ``r) (toExpr fld) eff.initialState

      lambdaTelescope eff.nonEffectProof <| fun fvars _ => do
        let lctx ← getLCtx
        let pre ← fvars.mapM fun expr => do
          let ty := lctx.get! expr.fvarId! |>.type
          mkDecideProof ty

        pure {value, proof := mkAppN eff.nonEffectProof pre}

/-! ## Update a Reflected State -/

#check write_mem_bytes_program

/-- Execute `write_mem <n> <addr> <val>` against the state stored in `eff`
That is, `currentState` of the returned struct will be
  `write_mem <n> <addr> <val> <eff.currentState>`
and all other fields are updated accordingly.
Note that no effort is made to preserve `currentStateEq`; it is set to `none`!
-/
private def update_write_mem (eff : AxEffects) (n addr val : Expr) :
    MetaM AxEffects := do
  trace[Tactic.sym] "adding write of {n} bytes of value {val} \
    to memory address {addr}"

  -- Update each field
  let fields ← eff.fields.toList.mapM fun ⟨fld, {value, proof}⟩ => do
    let r_of_w := mkApp5 (mkConst ``r_of_write_mem_bytes)
                    (toExpr fld) n addr val eff.currentState
    let proof ← mkEqTrans r_of_w proof
    return ⟨fld, {value, proof}⟩

  -- Update the non-effects proof
  let nonEffectProof ← lambdaTelescope eff.nonEffectProof fun args proof => do
    let f := args[0]!
    let r_of_w := mkApp5 (mkConst ``r_of_write_mem_bytes)
                    f n addr val eff.currentState
    let proof ← mkEqTrans r_of_w proof
    mkLambdaFVars args proof

  -- Update the memory effects proof
  let memoryEffectProof :=
    mkAppN (mkConst ``read_mem_bytes_write_mem_bytes_of_read_mem_eq)
      #[eff.currentState, eff.memoryEffect, eff.memoryEffectProof, n, addr, val]

  -- Update the program proof
  let programProof ← mkEqTrans
    (mkAppN (mkConst ``write_mem_bytes_program) #[
      eff.currentState, n, addr, val])
    eff.programProof

  -- Assemble the result
  let addWrite (e : Expr) := mkApp4 (mkConst ``write_mem_bytes) n addr val e
  let eff := { eff with
    currentState    := addWrite eff.currentState
    fields          := .ofList fields
    nonEffectProof
    memoryEffect    := addWrite eff.memoryEffect
    memoryEffectProof
    programProof
  }
  withTraceNode `Tactic.sym (fun _ => pure "new state") <| do
      trace[Tactic.sym] "{eff}"
  return eff

/-- Execute `w <fld> <val>` against the state stored in `eff`
That is, `currentState` of the returned struct will be
  `w <fld> <val> <eff.currentState>`
and all other fields are updated accordingly.
Note that no effort is made to preserve `currentStateEq`; it is set to `none`!
-/
private def update_w (eff : AxEffects) (fld val : Expr) :
    MetaM AxEffects := do
  let rField ← reflectStateField fld
  trace[Tactic.sym] "adding write of value {val} to register {rField}"

  -- Update all other fields
  let fields ←
    eff.fields.toList.filterMapM fun ⟨fld', {value, proof}⟩ => do
      if fld' ≠ rField then
        let proof : Expr ← do
          let fld' := toExpr fld'
          let h_neq : Expr ← -- h_neq : fld' ≠ fld
            mkDecideProof (mkApp3 (.const ``Ne [1])
              (mkConst ``StateField) fld' fld)
          let newProof := mkApp5 (mkConst ``r_of_w_different)
                            fld' fld val eff.currentState h_neq
          mkEqTrans newProof proof
        return some (fld', {value, proof})
      else
        return none

  -- Update the main field
  let newField : FieldEffect := {
    value := val
    proof := mkApp3 (mkConst ``r_of_w_same) fld val eff.currentState
  }
  let fields := (rField, newField) :: fields

  -- Update the non-effects proof
  let nonEffectProof ← lambdaTelescope eff.nonEffectProof fun args proof => do
    let f := args[0]!

    let k := fun args h_neq => do
    -- ^^ monadic continuation
      let r_of_w := mkApp5 (mkConst ``r_of_w_different)
                    f fld val eff.currentState h_neq
      let proof ← mkEqTrans r_of_w proof
      mkLambdaFVars args proof

    -- Then, determine `h_neq` so that we can pass it to `k`
    let h_neq_type := mkApp3 (.const ``Ne [1]) (mkConst ``StateField) f fld
    let h_neq? ← args.findM? fun h => do
        let hTy ← inferType h
        return hTy == h_neq_type
    match h_neq? with
      | some h_neq => k args h_neq
      | none =>
        let name := Name.mkSimple s!"h_neq_{rField}"
        withLocalDeclD name h_neq_type fun h_neq =>
          k (args.push h_neq) h_neq

  -- Update the memory effect proof
  let memoryEffectProof :=
    mkAppN (mkConst ``read_mem_bytes_w_of_read_mem_eq)
      #[eff.currentState, eff.initialState, eff.memoryEffectProof, fld, val]

  -- Update the program proof
  let programProof ← mkEqTrans
    (mkAppN (mkConst ``w_program) #[fld, val, eff.currentState])
    eff.programProof

  -- Assemble the result
  let eff := { eff with
    currentState    := mkApp3 (mkConst ``w) fld val eff.currentState
    fields := Std.HashMap.ofList fields
    nonEffectProof
    -- memory effects are unchanged
    memoryEffectProof
    programProof
  }
  withTraceNode `Tactic.sym (fun _ => pure "new state") <| do
      trace[Tactic.sym] "{eff}"
  return eff

/-- Throw an error if `e` is not of type `expectedType` -/
private def assertHasType (e expectedType : Expr) : MetaM Unit := do
  let eType ← inferType e
  if !(←isDefEq eType expectedType) then
    throwError "{e} {← mkHasTypeButIsExpectedMsg eType expectedType}"

/-- Given an expression `e : ArmState`,
which is a sequence of `w`/`write_mem`s to the some state `s`,
return an `AxEffects` where `s` is the intial state, and `e` is `currentState`.
-/
partial def fromExpr (e : Expr) : MetaM AxEffects := do
  let msg := m!"Building effects with writes from: {e}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do match_expr e with
    | write_mem_bytes n addr val e =>
        let eff ← fromExpr e
        eff.update_write_mem n addr val

    | w field value e =>
        let eff ← fromExpr e
        eff.update_w field value

    | _ =>
        return initial e

/-- Given a proof `eq : s = <currentState>`,
set `s` to be the new `currentState`, and update all proofs accordingly -/
def adjustCurrentStateWithEq (eff : AxEffects) (s eq : Expr) :
    MetaM AxEffects := do
  withTraceNode `Tactic.sym (fun _ => pure "adjusting `currenstState`") do
    withTraceNode `Tactic.sym (fun _ => pure "current state") do
        trace[Tactic.sym] "{eff}"
    trace[Tactic.sym] "rewriting along {eq}"
    assertHasType eq <| mkEqArmState s eff.currentState
    let eq ← mkEqSymm eq

    let fields ← eff.fields.toList.mapM fun (field, fieldEff) => do
      withTraceNode `Tactic.sym (fun _ => pure m!"rewriting field {field}") do
        trace[Tactic.sym] "original proof: {fieldEff.proof}"
        let proof ← rewriteType fieldEff.proof eq
        trace[Tactic.sym] "new proof: {proof}"
        pure (field, {fieldEff with proof})
    let fields := .ofList fields

    let nonEffectProof ← rewriteType eff.nonEffectProof eq
    let memoryEffectProof ← rewriteType eff.memoryEffectProof eq
    -- ^^ TODO: what happens if `memoryEffect` is the same as `currentState`?
    --    Presumably, we would *not* want to encapsulate `memoryEffect` here
    let programProof ← rewriteType eff.programProof eq

    return {eff with fields, nonEffectProof, memoryEffectProof, programProof}

/-- Given a proof `eq : ?s = <sequence of w/write_mem to ?s0>`,
where `?s` and `?s0` are arbitrary `ArmState`s,
return an `AxEffect` with `?s0` as the initial state,
the rhs of the equality as the current state, and
`eq` stored as `currentStateEq`,
so that `?s` is the public-facing current state -/
def fromEq (eq : Expr) : MetaM AxEffects :=
  let msg := m!"Building effects with equality: {eq}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    let s ← mkFreshExprMVar mkArmState
    let rhs ← mkFreshExprMVar mkArmState
    assertHasType eq <| mkEqArmState s rhs

    let eff ← fromExpr (← instantiateMVars rhs)
    let eff ← eff.adjustCurrentStateWithEq s eq
    withTraceNode `Tactic.sym (fun _ => pure "new state") do
      trace[Tactic.sym] "{eff}"
    return eff

/-- Given an equality `eq : ?currentProgram = ?newProgram`,
where `currentProgram` is the rhs of `eff.programProof`,
apply transitivity to make `newProgram` the rhs of `programProof`
in the return value.

Generally used with `?currentProgram = <initialState>.program`, which is the
default rhs created by `initial`,
and `?newProgram` the constant of the concrete program. -/
def withProgramEq (eff : AxEffects) (eq : Expr) : MetaM AxEffects := do
  let programProof ← mkEqTrans eff.programProof eq
  return {eff with programProof}

/-- Given an equality `eq : r ?field <initialState> = ?value`,
record `value` in the `AxEffect`s struct as the effect for `field`,
assuming that `field` did not have an effect stored yet.

Otherwise, if there *is* an effect stored for the field, try to rewrite it
along the given equality.
If this rewrite fails, return the original effects unchanged.

Note: throws an error when `initialState = currentState` *and*
the field already has a value stored, as the rewrite might produce expressions
of unexpected types. -/
def withField (eff : AxEffects) (eq : Expr) : MetaM AxEffects := do
  let fieldE ← mkFreshExprMVar (mkConst ``StateField)
  let value ← mkFreshExprMVar none
  assertHasType eq (←mkEq (mkApp2 (mkConst ``r) fieldE eff.initialState) value)

  let field ← reflectStateField (← instantiateMVars fieldE)
  let fieldEff ← eff.getField field

  if field ∉ eff.fields then
    let proof ← mkEqTrans fieldEff.proof eq
    let fields := eff.fields.insert field { value, proof }
    return { eff with fields }
  else
    if eff.currentState == eff.initialState then
      throwError "error: {field} already has an effect associated with it, \
        and the current state
          {eff.currentState}
        is equal to the initial state
          {eff.initialState}"

    let valEq ← try rewrite fieldEff.value eq
      catch _ => return eff

    let_expr Eq _ _ value := ← inferType valEq
      | throwError "internal error: expected an equality, found {valEq}"
    let proof ← mkEqMP valEq fieldEff.proof
    let fields := eff.fields.insert field { value, proof }
    return { eff with fields }



/-! ## Composition -/

/- TODO: write a function that combines two effects `left` and `right`,
where `left.initialState = right.currentState`.
That is, compose the effect of "`left` after `right`" -/

/-! ## Tactic Environment -/
section Tactic
open Elab.Tactic

/-- Add new hypotheses to the local context:
- one for every field in `eff.fields`
- `eff.nonEffectProof`, and
- `eff.memoryEffectProof` -/
def addHypothesesToLContext (eff : AxEffects) (hypPrefix : String := "h_") :
    TacticM Unit :=
  let msg := m!"adding hypotheses to local context"
  withTraceNode `Tactic.sym (fun _ => pure msg) do
    withTraceNode `Tactic.sym (fun _ => pure "current state") <| do
      trace[Tactic.sym] "{eff}"
    let mut goal ← getMainGoal

    for ⟨field, {proof, ..}⟩ in eff.fields do
      let msg := m!"adding field {field}"
      goal ← withTraceNode `Tactic.sym (fun _ => pure msg) <| goal.withContext do
        trace[Tactic.sym] "raw proof: {proof}"
        let name := Name.mkSimple (s!"{hypPrefix}{field}")
        replaceOrNote goal name proof

    trace[Tactic.sym] "adding non-effects with {eff.nonEffectProof}"
    goal ← goal.withContext do
      let name := .mkSimple s!"{hypPrefix}non_effects"
      let proof := eff.nonEffectProof
      replaceOrNote goal name proof

    trace[Tactic.sym] "adding memory effects with {eff.memoryEffectProof}"
    goal ← goal.withContext do
      let name := .mkSimple s!"{hypPrefix}memory_effects"
      let proof := eff.memoryEffectProof
      replaceOrNote goal name proof

    trace[Tactic.sym] "adding program hypothesis with {eff.programProof}"
    goal ← goal.withContext do
      let name := .mkSimple s!"{hypPrefix}program"
      let proof := eff.programProof
      replaceOrNote goal name proof

    replaceMainGoal [goal]
where
  replaceOrNote (goal : MVarId) (h : Name) (v : Expr)
      (t? : Option Expr := none) :
      MetaM MVarId :=
    let msg := m!"adding {h} to the local context"
    withTraceNode `Tactic.sym (fun _ => pure msg) <| do
      trace[Tactic.sym] "with value {v} and type {t?}"
      if let some decl := (← getLCtx).findFromUserName? h then
        let ⟨_, goal, _⟩ ← goal.replace decl.fvarId v t?
        return goal
      else
        let ⟨_, goal⟩ ← goal.note h v t?
        return goal

-- namespace ExplodeStep



-- -- We make `explode_step` scoped, because this is not the only
-- -- implementation of this tactic
-- /-- Given an equality `h_step : s{i+1} = w ... (... (w ... s{i})...)`,
-- add hypotheses that axiomatically describe the effects in terms of
-- reads from `s{i+1}` -/
-- scoped elab "explode_step " h_step:term h_program:term pre:(str)? : tactic =>
--   withMainContext do
--     let hStep ← elabTerm h_step none
--     let hProgram ← elabTerm h_program none
--     let pre := ((·.getString) <$> pre).getD "h_"
--     explodeStep hStep hProgram pre

-- end ExplodeStep

end Tactic
