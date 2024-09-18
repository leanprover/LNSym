/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/

import Arm.State
import Tactics.Common
import Tactics.Attr
import Tactics.Simp

import Std.Data.HashMap

open Lean Meta

/-- A reflected `ArmState` field, see `AxEffects.fields` for more context -/
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
Note that as soon as an unsupported expression  (e.g., an `if`) is encountered,
the whole expression is taken to be the initial state,
even if there might be more `w`/`write_mem`s in sub-expressions.

`AxEffects` contains a hashmap from `StateField` to an expression,
in terms of the fixed initial state,
that describes the value of the given field *after* the writes.
Additionally, each field carries a proof that it is indeed the right value.

Furthermore, we maintain a few other invariants,
see the docstrings on each field for more detail -/
structure AxEffects where
  /-- The initial state -/
  initialState : Expr
  /-- The current state, which may be expressed in either the "exploded form"
  (a sequence of `w`/`write_mem` to the initial state), or as just a variable
  which is (propositionally) equal to that exploded form -/
  currentState : Expr

  /-- A map from each statefield to the corresponding `FieldEffect`.
  If a field has no entry in this map, it has not been changed, and thus,
  its value can be retrieved from the `nonEffectProof` -/
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
  to the initial state, which describes the effects on memory.
  See `memoryEffectProof` for more detail -/
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
  /-- An optional proof of `CheckSPAlignment <currentState>`.

  This proof is preserved on a best-effort basis.
  That is, if we update the state with a write to memory, or a register that is
  not SP, we maintain the proof.
  However, if SP is written to, no effort is made to prove alignment of the
  new value; the field will be set to `none` -/
  stackAlignmentProof? : Option Expr
  deriving Repr

namespace AxEffects

/-! ## Initial Reflected State -/

/-- An initial `AxEffects` state which has no writes.
That is, the given `state` is assigned to be both the initial and the current
state -/
def initial (state : Expr) : AxEffects where
  initialState      := state
  currentState      := state
  fields            := .empty
  nonEffectProof    :=
    -- `fun f => rfl`
    mkLambda `f .default (mkConst ``StateField) <|
      mkEqReflArmState <| mkApp2 (mkConst ``r) (.bvar 0) state
  memoryEffect      := state
  memoryEffectProof :=
    -- `fun n addr => rfl`
    mkLambda `n .default (mkConst ``Nat) <|
      let bv64 := mkApp (mkConst ``BitVec) (toExpr 64)
      mkLambda `addr .default bv64 <|
        mkApp2 (.const ``Eq.refl [1])
          (mkApp (mkConst ``BitVec) <| mkNatMul (.bvar 1) (toExpr 8))
          (mkApp3 (mkConst ``read_mem_bytes) (.bvar 1) (.bvar 0) state)
  programProof      :=
    -- `rfl`
    mkAppN (.const ``Eq.refl [1]) #[
      mkConst ``Program,
      mkApp (mkConst ``ArmState.program) state]
  stackAlignmentProof? := none

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

private def traceCurrentState (eff : AxEffects)
    (header : MessageData := "current state") :
    MetaM Unit :=
  withTraceNode `Tactic.sym (fun _ => pure header) do
    trace[Tactic.sym] "{eff}"

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

/-- Given a `field` such that `fields ∉ eff.fields`, return a proof of
  `r field <currentState> = r field <initialState>`
by constructing an application of `eff.nonEffectProof` -/
partial def mkAppNonEffect (eff : AxEffects) (field : Expr) : MetaM Expr := do
  let msg := m!"constructing application of non-effects proof"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    trace[Tactic.sym] "nonEffectProof: {eff.nonEffectProof}"

    let nonEffectProof := mkApp eff.nonEffectProof field
    let typeOfNonEffects ← inferType nonEffectProof
    forallTelescope typeOfNonEffects <| fun fvars _ => do
      trace[Tactic.sym] "hypotheses of nonEffectProof: {fvars}"
      let lctx ← getLCtx
      let pre ← fvars.mapM fun expr => do
        let ty := lctx.get! expr.fvarId! |>.type
        mkDecideProof ty

      let nonEffectProof := mkAppN nonEffectProof pre
      trace[Tactic.sym] "constructed: {nonEffectProof}"
      return nonEffectProof

/-- Get the value for a field, if one is stored in `eff.fields`,
or assemble an instantiation of the non-effects proof -/
def getField (eff : AxEffects) (fld : StateField) : MetaM FieldEffect :=
  let msg := m!"getField {fld}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    eff.traceCurrentState

    if let some val := eff.fields.get? fld then
      trace[Tactic.sym] "returning stored value {val}"
      return val
    else
      trace[Tactic.sym] "found no stored value"
      let value := mkApp2 (mkConst ``r) (toExpr fld) eff.initialState
      let proof  ← eff.mkAppNonEffect (toExpr fld)
      pure { value, proof }

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
    -- ^^ `fun f ... => Eq.trans (@r_of_write_mem_bytes f ...) <proof>`

  -- Update the memory effects proof
  let memoryEffectProof :=
    -- `read_mem_bytes_write_mem_bytes_of_read_mem_eq <memoryEffectProof> ...`
    mkAppN (mkConst ``read_mem_bytes_write_mem_bytes_of_read_mem_eq)
      #[eff.currentState, eff.memoryEffect, eff.memoryEffectProof, n, addr, val]

  -- Update the program proof
  let programProof ←
    -- `Eq.trans (@write_mem_bytes_program <currentState> ...) <programProof>`
    mkEqTrans
      (mkAppN (mkConst ``write_mem_bytes_program)
        #[eff.currentState, n, addr, val])
      eff.programProof

  -- Assemble the result
  let addWrite (e : Expr) :=
    -- `@write_mem_bytes <n> <addr> <val> <e>`
    mkApp4 (mkConst ``write_mem_bytes) n addr val e
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
    proof :=
      -- `r_of_w_same <fld> <val> <currentState>`
      mkApp3 (mkConst ``r_of_w_same) fld val eff.currentState
  }
  let fields := (rField, newField) :: fields

  -- Update the non-effects proof
  let nonEffectProof ← lambdaTelescope eff.nonEffectProof fun args proof => do
    let f := args[0]!

    /- First, assume we have a proof `h_neq : <f> ≠ <fld>`, and use that
    to compute the new `nonEffectProof` -/
    let k := fun args h_neq => do
      let r_of_w := mkApp5 (mkConst ``r_of_w_different)
                    f fld val eff.currentState h_neq
      let proof ← mkEqTrans r_of_w proof
      mkLambdaFVars args proof
      -- ^^ `fun f ... => Eq.trans (r_of_w_different ... <h_neq>) <proof>`

    /- Then, determine `h_neq` so that we can pass it to `k`.
    Notice how we have to modify the environment, to add `h_neq` as a new local
    hypothesis if it wan't present yet, but only in some branches.
    This is why we had to define `k` as a monadic continuation,
    so we can nest `k` under a `withLocalDeclD` -/
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
    -- `read_mem_bytes_w_of_read_mem_eq ...`
    mkAppN (mkConst ``read_mem_bytes_w_of_read_mem_eq)
      #[eff.currentState, eff.memoryEffect, eff.memoryEffectProof, fld, val]

  -- Update the program proof
  let programProof ←
    -- `Eq.trans (w_program ...) <programProof>`
    mkEqTrans
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
  eff.traceCurrentState "new state"
  return eff

/-- Throw an error if `e` is not of type `expectedType` -/
private def assertHasType (e expectedType : Expr) : MetaM Unit := do
  let eType ← inferType e
  if !(←isDefEq eType expectedType) then
    throwError "{e} {← mkHasTypeButIsExpectedMsg eType expectedType}"

private def assertIsDefEq (e expected : Expr) : MetaM Unit := do
  if !(←isDefEq e expected) then
    throwError "expected:\n  {expected}\nbut found:\n  {e}"

/-- Given an expression `e : ArmState`,
which is a sequence of `w`/`write_mem`s to the some state `s`,
return an `AxEffects` where `s` is the intial state, and `e` is `currentState`.

Note that as soon as an unsupported expression (e.g., an `if`) is encountered,
the whole expression is taken to be the initial state,
even if there might be more `w`/`write_mem`s in sub-expressions. -/
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
    eff.traceCurrentState
    trace[Tactic.sym] "rewriting along {eq}"
    assertHasType eq <| mkEqArmState s eff.currentState
    let eq ← mkEqSymm eq

    let currentState := s

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

    return { eff with
      currentState, fields, nonEffectProof, memoryEffectProof, programProof
    }

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
  let msg := m!"withField {eq}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    eff.traceCurrentState
    let fieldE ← mkFreshExprMVar (mkConst ``StateField)
    let value ← mkFreshExprMVar none
    let expectedType ← mkEq (mkApp2 (mkConst ``r) fieldE eff.initialState) value
    assertHasType eq expectedType

    let field ← reflectStateField (← instantiateMVars fieldE)
    let fieldEff ← eff.getField field
    trace[Tactic.sym] "current field effect: {fieldEff}"

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

/-- Given a proof of `CheckSPAlignment <initialState>`,
attempt to transport it to a proof of `CheckSPAlignment <currentState>`
and store that proof in `stackAlignmentProof?`.

Returns `none` if the proof failed to be transported,
i.e., if SP was written to. -/
def withStackAlignment? (eff : AxEffects) (spAlignment : Expr) :
    MetaM (Option AxEffects) := do
  let msg := m!"withInitialStackAlignment? {spAlignment}"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    eff.traceCurrentState

    let { value, proof } ← eff.getField StateField.SP
    let expected :=
      mkApp2 (mkConst ``r) (toExpr <| StateField.SP) eff.initialState
    trace[Tactic.sym] "checking whether value:\n  {value}\n\
      is syntactically equal to expected value\n  {expected}"
    if value != expected then
      trace[Tactic.sym] "failed to transport proof:
        expected value to be {expected}, but found {value}"
      return none

    let stackAlignmentProof? := some <|
      mkAppN (mkConst ``CheckSPAlignment_of_r_sp_eq)
        #[eff.initialState, eff.currentState, proof, spAlignment]
    trace[Tactic.sym] "constructed stackAlignmentProof: {stackAlignmentProof?}"
    return some { eff with stackAlignmentProof? }

/-! ## Composition -/

/- TODO: write a function that combines two effects `left` and `right`,
where `left.initialState = right.currentState`.
That is, compose the effect of "`left` after `right`" -/

/-! ## Validation -/

/-- type check all expressions stored in `eff`,
throwing an error if one is not type-correct.

In principle, the various `AxEffects` definitions should return only well-formed
expressions, making `validate` a no-op.
In practice, however, running `validate` is helpful for catching bugs in those
definitions. Do note that typechecking might be a bit expensive, so we generally
only call `validate` while debugging, not during normal execution.
See also the `Tactic.sym.debug` option, which controls whether `validate` is
called for each step of the `sym_n` tactic.

NOTE: does not necessarily validate *which* type an expression has,
validation will still pass if types are different to those we claim in the
docstrings -/
def validate (eff : AxEffects) : MetaM Unit := do
  let msg := "validating that the axiomatic effects are well-formed"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    eff.traceCurrentState

    assertHasType eff.initialState mkArmState
    assertHasType eff.currentState mkArmState

    for ⟨_field, fieldEff⟩ in eff.fields do
      check fieldEff.value
      check fieldEff.proof

    check eff.nonEffectProof
    check eff.memoryEffect
    check eff.memoryEffectProof
    check eff.programProof
    if let some h := eff.stackAlignmentProof? then
      check h

/-! ## Tactic Environment -/
section Tactic
open Elab.Tactic

/-- Add new hypotheses to the local context of a given mvar (or the main goal,
by default):
- one for every field in `eff.fields`
- `eff.nonEffectProof`,
- `eff.memoryEffectProof`,
- `eff.programProof`, and
- `eff.stackAlignmentProof?` (if the field is not `none`)

Return an `AxEffect` where the expressions mentioned above have been replaced by
`Expr.fvar <fvarId>`, with `fvarId` the id of the corresponding hypothesis
that was just added to the local context -/
def addHypothesesToLContext (eff : AxEffects) (hypPrefix : String := "h_")
    (mvar : Option MVarId := none) :
    TacticM AxEffects :=
  let msg := m!"adding hypotheses to local context"
  withTraceNode `Tactic.sym (fun _ => pure msg) do
    eff.traceCurrentState
    let mut goal ← mvar.getDM getMainGoal

    let fields ← do
      let mut fields := []
      for ⟨field, {value, proof}⟩ in eff.fields do
        let msg := m!"adding field {field}"
        let ⟨fvar, goal'⟩ ← withTraceNode `Tactic.sym (fun _ => pure msg) <| goal.withContext do
            trace[Tactic.sym] "raw proof: {proof}"
            let name := Name.mkSimple s!"{hypPrefix}{field}"
            replaceOrNote goal name proof
        goal := goal'
        let fieldEff := FieldEffect.mk value (Expr.fvar fvar)
        fields := (field, fieldEff) :: fields
      pure (Std.HashMap.ofList fields)

    trace[Tactic.sym] "adding non-effects with {eff.nonEffectProof}"
    let ⟨nonEffectProof, goal'⟩ ← goal.withContext do
      let name := .mkSimple s!"{hypPrefix}non_effects"
      let proof := eff.nonEffectProof
      replaceOrNote goal name proof
    let nonEffectProof := Expr.fvar nonEffectProof
    goal := goal'

    trace[Tactic.sym] "adding memory effects with {eff.memoryEffectProof}"
    let ⟨memoryEffectProof, goal'⟩ ← goal.withContext do
      let name := .mkSimple s!"{hypPrefix}memory_effects"
      let proof := eff.memoryEffectProof
      replaceOrNote goal name proof
    let memoryEffectProof := Expr.fvar memoryEffectProof
    goal := goal'

    trace[Tactic.sym] "adding program hypothesis with {eff.programProof}"
    let ⟨programProof, goal'⟩ ← goal.withContext do
      let name := .mkSimple s!"{hypPrefix}program"
      let proof := eff.programProof
      replaceOrNote goal name proof
    let programProof := Expr.fvar programProof
    goal := goal'

    trace[Tactic.sym] "stackAlignmentProof? is {eff.stackAlignmentProof?}"
    let (stackAlignmentProof?, goal') ← do
      if let some stackAlignmentProof := eff.stackAlignmentProof? then
        trace[Tactic.sym] "adding stackAlignment hypothesis"
        let ⟨fvar, goal'⟩ ← goal.withContext do
          let name := .mkSimple s!"{hypPrefix}sp_aligned"
          replaceOrNote goal name stackAlignmentProof
        pure (some (Expr.fvar fvar), goal')
      else
        trace[Tactic.sym] "skipping stackAlignment hypothesis"
        pure (none, goal)
    goal := goal'

    replaceMainGoal [goal]
    return {eff with
      fields, nonEffectProof, memoryEffectProof, programProof,
      stackAlignmentProof?
    }
where
  replaceOrNote (goal : MVarId)
      (h : Name) (v : Expr) (t? : Option Expr := none) :
      MetaM (FVarId × MVarId) :=
    let msg := m!"adding {h} to the local context"
    withTraceNode `Tactic.sym (fun _ => pure msg) <| do
      trace[Tactic.sym] "with value {v} and type {t?}"
      if let some decl := (← getLCtx).findFromUserName? h then
        let ⟨fvar, goal, _⟩ ← goal.replace decl.fvarId v t?
        return ⟨fvar, goal⟩
      else
        let ⟨fvar, goal⟩ ← goal.note h v t?
        return ⟨fvar, goal⟩

/-- Return an array of `SimpTheorem`s of the proofs contained in
the given `AxEffects` -/
def toSimpTheorems (eff : AxEffects) : MetaM (Array SimpTheorem) := do
  let msg := m!"computing SimpTheorems for (non-)effect hypotheses"
  withTraceNode `Tactic.sym (fun _ => pure msg) <| do
    let lctx ← getLCtx
    let baseName? :=
      if eff.currentState.isFVar then
        (lctx.find? eff.currentState.fvarId!).map fun decl =>
          Name.str decl.userName "AxEffects"
      else
        none
    let baseName := baseName?.getD (Name.mkSimple "AxEffects")

    let add (thms : Array SimpTheorem) (e : Expr) (name : String)
        (prio : Nat := 1000) :=
      let msg := m!"adding {e} with name {name}"
      withTraceNode `Tactic.sym (fun _ => pure msg) <| do
        let origin : Origin :=
          if e.isFVar then
            .fvar e.fvarId!
          else
            .other <| Name.str baseName name
        let newThms ← mkSimpTheorems origin #[] e (prio := prio)
        let newThms ← newThms.mapM fixSimpTheoremKey
        pure <| thms ++ newThms

    let mut thms := #[]

    for ⟨field, {proof, ..}⟩ in eff.fields do
      /- We give the field-specific lemmas a high priority, since their
      applicability is determined entirely by discrtree matching.
      This is important for performance, because it avoids unneccesary
      (expensive!) attempts to discharge the `field ≠ otherField`
      side-conditions of the non-effect proof -/
      thms ← add thms proof s!"field_{field}" (prio := 1500)

    thms ← add thms eff.nonEffectProof "nonEffectProof"
    thms ← add thms eff.memoryEffectProof "memoryEffectProof"
    thms ← add thms eff.programProof "programProof"
    if let some stackAlignmentProof := eff.stackAlignmentProof? then
      thms ← add thms stackAlignmentProof "stackAlignmentProof"

    trace[Tactic.sym] "done"

    pure thms

end Tactic
