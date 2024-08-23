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

theorem foo : 1 ≠ 4 := by decide

#print foo
#check of_decide_eq_true
#synth Decidable <| (?x : StateField) ≠ _

#check @instDecidableNot (Eq ?x ?y) <| instDecidableEqStateField ?x ?y

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
  /-- An optional proof of
      `?s = <currentState>`
    Where `s` is any equivalent `ArmState`, generally a single variable.

    `currentStateEq` is used by field accessors to adjust types to
    expose `s`, rather than `currentState`. -/
  currentStateEq : Option Expr
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
  deriving Repr

namespace AxEffects

/-! ## Initial Reflected State -/

def initial (state : Expr) : AxEffects where
  initialState      := state
  currentState      := state
  currentStateEq    := none
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
      currentStateEq := {eff.currentStateEq},
      fields := {eff.fields},
      nonEffectProof := {eff.nonEffectProof},
      memoryEffect := {eff.memoryEffect},
      memoryEffectProof := {eff.memoryEffectProof}
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

/-- Rewrite the *type* of `e` via `eff.currentStateEq`, if given, to hide the
exploded `currentState`, then move`e` into the new type via `Eq.mp`.
Otherwise, if `currentStateEq` is none, return `e` unchanged -/
def hideCurrentStateType (eff : AxEffects) (e : Expr) :
    MetaM Expr := do
  match eff.currentStateEq with
    | none    => return e
    | some eq => rewriteType e (← mkEqSymm eq)

def getField (eff : AxEffects) (fld : StateField) : MetaM FieldEffect :=
  let msg := "getField _ {fld}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    withTraceNode `Tactic.sym (fun _ => pure "current state") <| do
      trace[Tactic.sym] "{eff}"

    let mut ({ value, proof } : FieldEffect) ←do
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

    trace[Tactic.sym] "found value {value} with proof {proof}"
    if eff.currentStateEq.isSome then
      proof ← eff.hideCurrentStateType proof
      trace[Tactic.sym] "`currentStateEq` is {eff.currentStateEq}, \
        so proof was adjusted to {proof}"
    return {value, proof}


/-! ## Update a Reflected State -/

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


  -- Assemble the result
  let addWrite (e : Expr) := mkApp4 (mkConst ``write_mem_bytes) n addr val e
  let eff := { eff with
    currentState    := addWrite eff.currentState
    currentStateEq  := none
    fields          := .ofList fields
    nonEffectProof
    memoryEffect    := addWrite eff.memoryEffect
    memoryEffectProof
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

  -- Assemble the result
  let eff := { eff with
    currentState    := mkApp3 (mkConst ``w) fld val eff.currentState
    currentStateEq  := none
    fields := Std.HashMap.ofList fields
    nonEffectProof
    -- memory effects are unchanged
    memoryEffectProof
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

/-- Given a proof `eq : ?s = <sequence of w/write_mem to ?s0>`,
where `?s` and `?s0` are arbitrary `ArmState`s,
return an `AxEffect` with `?s0` as the initial state,
the rhs of the equality as the current state, and
`eq` stored as `currentStateEq`,
so that `?s` is the public-facing current state -/
def fromEq (eq : Expr) : MetaM AxEffects :=
  let msg := m!"Building effects with equality: {eq}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    let A := mkConst ``ArmState
    let s ← mkFreshExprMVar A
    let rhs ← mkFreshExprMVar A

    let expectedType := mkApp3 (.const ``Eq [1]) A s rhs
    assertHasType eq expectedType

    let eff ← fromExpr (← instantiateMVars rhs)
    let eff := { eff with currentStateEq := eq }
    withTraceNode `Tactic.sym (fun _ => pure "new state") do
      trace[Tactic.sym] "{eff}"
    return eff

/-! ## Composition -/

/-- TODO: write a function that combines two effects, where
`left.currentState = right.initialState` (or the other way?) -/
def compose (left right : AxEffects) : MetaM AxEffects := do
  sorry

/-! ## Validation -/

/-- Validate that the various proofs in `eff` have the right types -/
def validate (eff : AxEffects) : MetaM Unit := do
  let armState := mkConst ``ArmState
  assertHasType eff.initialState armState
  assertHasType eff.currentState armState
  -- TODO: actually validate the proofs

/-! ## Tactic Environment -/
section Tactic
open Elab.Tactic

/-- Add new hypotheses to the local context:
- one for every field in `eff.fields`
- `eff.nonEffectProof`, and
- `eff.memoryEffectProof` -/
def addHypothesesToLContext (eff : AxEffects) : TacticM Unit :=
  let msg := m!"adding hypotheses to local context"
  withTraceNode `Tactic.sym (fun _ => pure msg) do
    withTraceNode `Tactic.sym (fun _ => pure "current state") <| do
      trace[Tactic.sym] "{eff}"
    let mut goal ← getMainGoal

    for ⟨field, {proof, ..}⟩ in eff.fields do
      let msg := m!"adding field {field}"
      goal ← withTraceNode `Tactic.sym (fun _ => pure msg) <| goal.withContext do
        trace[Tactic.sym] "raw proof: {proof}"
        let name := Name.mkSimple (s!"h_r_{field}")
        let proof ← eff.hideCurrentStateType proof
        replaceOrNote goal name proof

    trace[Tactic.sym] "adding non-effects with {eff.nonEffectProof}"
    goal ← goal.withContext do
      let proof ← eff.hideCurrentStateType eff.nonEffectProof
      replaceOrNote goal `h_non_effects proof

    trace[Tactic.sym] "adding memory effects with {eff.memoryEffectProof}"
    goal ← goal.withContext do
      let proof ← eff.hideCurrentStateType eff.memoryEffectProof
      replaceOrNote goal `h_memory_effects proof
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

end Tactic

section Test

open Lean Elab.Tactic

-- variable (s0 : Expr)

/-- given an equality `h_step : ?s = <sequence of writes to ?s0>`,
add hypotheses to the context that describe reading from `?s` -/
elab "effects_from_eq " h_step:term : tactic => withMainContext do
  let h_step ← elabTerm h_step none
  let eff ← fromEq h_step
  trace[Tactic.sym] "{eff}"

  eff.addHypothesesToLContext

set_option trace.Tactic.sym true

example (s0 s1 : ArmState)
  (h_step : s1 = (write_mem_bytes 10 0#64 0#80 <| w .PC 128#64 s0)) :
    r .PC s1 = 128#64 := by
  effects_from_eq h_step
  skip
  sorry



end Test
