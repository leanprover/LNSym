import Lean
import Arm.State
import Tactics.Simp
import Tactics.Common
import Tactics.Attr

open Lean Meta Elab Command

open StateField (GPR)
def numStates : Nat := 1000
set_option maxRecDepth 1000000

example : ((1+2) = 3) = True := eq_self _

simproc StateField.reduceEq (@Eq StateField _ _) := fun e => do
  if e.hasFVar || e.hasMVar then
    return .continue

  let_expr Eq type lhsE rhsE := e
    | return .continue

  let some lhs ← reflectStateField? lhsE
    | return .continue
  let some rhs ← reflectStateField? rhsE
    | return .continue

  if lhs = rhs then
    return .done {
      expr   := mkConst ``True
      proof? := some (mkApp2 (.const ``eq_self [1]) type lhsE)
    }
  else
    -- TODO: simplify to `False`
    return .continue
attribute [bitvec_rules high] StateField.reduceEq

simproc StateField.reduceNe (@Ne StateField _ _) := fun ne => do
  trace[Tactic.sym] "Simplifying: {ne}"
  if ne.hasFVar || ne.hasMVar then
    trace[Tacitc.sym] "abort: has free variables"
    return .continue

  let_expr Ne _type lhsE rhsE := ne
    | trace[Tactic.sym] "internal error: failed to destructure"
      return .continue
  trace[Tactic.sym] "lhs = {lhsE}\nrhs = {rhsE}"

  let some lhs ← reflectStateField? lhsE
    | return .continue
  let some rhs ← reflectStateField? rhsE
    | return .continue

  if lhs = rhs then
    trace[Tactic.sym] "{lhs} = {rhs}"
    return .done {
      expr   := mkConst ``False
      proof? := some (
        mkApp (mkConst ``propext) <|
          mkApp2 (.const ``ne_self_iff_false [1]) (mkConst ``StateField) lhsE
      )
    }
  else
    trace[Tactic.sym] "{lhs} ≠ {rhs}"
    let instDecide ← synthInstance <| mkApp (mkConst ``Decidable) ne
    return .done {
      expr   := mkConst ``True
      proof? := some (
        mkAppN (mkConst ``eq_true_of_decide) #[
          ne, instDecide,
          mkApp2 (.const ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
        ]
      )
    }
attribute [bitvec_rules high] StateField.reduceNe

attribute [bitvec_rules] BitVec.reduceEq
attribute [bitvec_rules] BitVec.reduceNe
-- attribute [bitvec_rules, minimal_theory] GPR.injEq

set_option trace.Tactic.sym true

example : StateField.GPR 1#5 ≠ StateField.GPR 2#5 := by
  simp (config := { decide := false }) only [StateField.reduceNe]


elab "states" : command => do
  for i in List.range numStates do
    let si := Name.mkSimple s!"s{i}"
    let siId := mkIdent si
    elabCommand <|← `(command|
      axiom $siId : ArmState
    )
    if i > 0 then
      let sp := mkIdent <| Name.mkSimple s!"s{i-1}"
      let h_inst        := mkIdent <| Name.mkSimple s!"h_s{i}_inst"
      let h_disch       := mkIdent <| Name.mkSimple s!"h_s{i}_disch"
      let h_disch_list  := mkIdent <| Name.mkSimple s!"h_s{i}_disch_list"
      elabCommand <|← `(command|
        axiom $h_inst  : ∀ f, r f $siId = r f $sp
      )
      elabCommand <|← `(command|
        axiom $h_disch : ∀ f, f ≠ (GPR 0) → f ≠ (GPR 31) → r f $siId = r f $sp
      )
      elabCommand <|← `(command|
        axiom $h_disch_list : ∀ f, f ∉ [GPR 0, GPR 31] → r f $siId = r f $sp
      )
states

macro "finalState" : term =>
  let sf := mkIdent <| Name.mkSimple s!"s{numStates - 1}"
  `($sf)

open Tactic

def simpGoalWith (cfg : Simp.Context × Array Simprocs) :
    TacticM Unit := do
  let simpRes ← simpGoal (← getMainGoal) cfg.1 cfg.2
  replaceMainGoal <| match simpRes.1 with
    | none            => []
    | some (_, goal)  => [goal]
  logInfo s!"Used {← heartbeatsPercent}% of heartbeat budget"

/-- `simp_inst` simplifies the goal using the purely instantiation axioms
  `h_s{i}_inst : ∀ f, r f s{i} = r f s{i-1}`
-/
elab "simp_inst" : tactic => do
  let thms := Array.range (numStates-1) |>.map fun i =>
    let i := i + 1
    Name.mkSimple s!"h_s{i}_inst"
  simpGoalWith <|← LNSymSimpContext (thms := thms)


attribute [-minimal_theory] eq_self
attribute [-minimal_theory] ne_eq
attribute [-bitvec_rules] BitVec.ofNat_eq_ofNat
set_option trace.Tactic.sym true

-- set_option trace.Meta.Tactic.simp true in
-- set_option trace.Meta.Tactic.simp.all true in

-- With 400 states, `simp_inst` takes around 35ms to simplify, using
-- 0% of the heartbeat budget
-- With 1000 states, `simp_inst` takes around 80ms to simplify, using
-- 0% of the heartbeat budget
#time example : r (GPR 1) finalState = r (GPR 1) s0 := by
  simp_inst; (try rfl)



/-- `simp_disch` simplifies the goal using the axioms
  `h_s{i}_disch : ∀ f, f ≠ (GPR 0) → f ≠ (GPR 31) → r f s{i} = r f s{i-1}`
which requires two side-condition to be discharged -/
elab "simp_disch" : tactic => do
  let thms := Array.range (numStates-1) |>.map fun i =>
    let i := i + 1
    Name.mkSimple s!"h_s{i}_disch"
  simpGoalWith <|← LNSymSimpContext (config := {decide := false}) (thms := thms)

set_option trace.Meta.Tactic.simp true in
set_option trace.Meta.Tactic.simp.all true in

-- With 400 states, `simp_disch` takes around 190ms to simplify, using
-- 3% of the heartbeat budget
-- With 1000 states, `simp_disch` takes around 500ms to simplify, using
-- 9% of the heartbeat budget
#time example : r (GPR 1) finalState = r (GPR 1) s0 := by
  simp_disch; (try rfl)



/-- `simp_disch_list` simplifies the goal using the axioms
  `h_s{i}_disch_list : ∀ f, f ∉ [GPR 0, GPR 31] → r f s{i} = r f s{i-1}`
which bundles the side-conditions to be discharged -/
elab "simp_disch_list" : tactic => do
  let thms := Array.range (numStates-1) |>.map fun i =>
    let i := i + 1
    Name.mkSimple s!"h_s{i}_disch_list"
  simpGoalWith <|← LNSymSimpContext (config := {decide := true}) (thms := thms)

-- `simp_disch_list` seems to take about 20 to 50 ms longer than `simp_disch`,
-- using the exact same percentage of the heartbeat budget.
#time example : r (GPR 1) finalState = r (GPR 1) s0 := by
  simp_disch_list; (try rfl)
