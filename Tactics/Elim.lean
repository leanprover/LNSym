/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Hanno Becker
-/

/- This is a minimal attempt and providing a elimination tactic `elim`
   Elimination rules are a unified and principled way to destruct various
   kinds of premises, and ubiquituous in Isabelle. See below for some examples.

   While std and mathlib have custom destruction tactics, we try to avoid
   external dependencies as much as possible here. -/

import Lean
open Lean Meta Elab.Tactic

--
-- Almost a copy from stdlib, but remembering the fvarid
--

/-- Try to close goal by assumption. Upon succes, return fvar id of
  matching assumption. Otherwise, return none. --/
def assumptionCore' (mvarId : MVarId) : MetaM (Option FVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assumption
    match (← findLocalDeclWithType? (← mvarId.getType)) with
    | none => return none
    | some fvarId => mvarId.assign (mkFVar fvarId); return (some fvarId)

/-- Close goal `mvarId` using an assumption. Throw error message if failed. -/
def assumption' (mvarId : MVarId) : MetaM FVarId := do
  let res ← assumptionCore' mvarId
  match res with
  | none => throwTacticEx `assumption mvarId "assumption' tactic failed"
  | some fvarid => return fvarid

--
--
--

def erule (e : Expr) (mvid : MVarId) (with_intro : Bool := true) : MetaM (List MVarId) := do
  let s ← saveState
  try
    let mvids ← mvid.apply e
    match mvids with
    | [] => throwError "ill-formed elimination rule {e}"
    | main :: other =>
      -- Try to solve main goal by assumption, remember fvar of hypothesis
      let fvid ← assumption' main
      -- Remove hypothesis from all other goals
      let other' ← other.mapM (fun mvid => do
        if (← mvid.isAssignedOrDelayedAssigned) then
          return mvid
        let mvid ← mvid.clear fvid
        if with_intro then
          let (_, mvid) ← mvid.intros
          return mvid
        else
          return mvid
      )
      return other'
  catch _ =>
    restoreState s
    throwError "erule_tac failed"

-- Run erule repeatedly
def elim (e : Expr) (mvid : MVarId) : MetaM (List MVarId) := do
   Meta.repeat1' (erule e) [mvid]

elab "erule" e:term : tactic => do
   let e ← elabTermForApply e
   Elab.Tactic.liftMetaTactic (erule e)

elab "elim" e:term : tactic => do
   let e ← elabTermForApply e
   Elab.Tactic.liftMetaTactic (elim e)

-- Some examples of elimination rules
--
-- Elimination rules abound, but here are some simple examples.
-- While those can be handled by existing tactics as well, the point
-- is to show that `elim` unifies various types of deconstruction
-- in a single tactic, parametrized by a suitable elimination rule.

-- 1/ Disjunction elimination
example {A B C D E : Prop} (h : E): A ∨ B → C ∨ D → E := by
  intros
  elim Or.elim /- Now we have 4 goals -/
  <;> exact h
  done

-- 2/ Conjunction elimination
theorem conjE {P Q R: Prop}: P ∧ Q → (P → Q → R) → R := by
  intros h g; cases h; apply g <;> assumption

example {A B C D E} (h : E) (t : A ∧ B) (t' : C ∧ D) : E := by
  intros
  elim conjE -- Separate hypothesis A, B, C, D
  exact h
  done

-- 3/ Destructing existentials

theorem exE' {R : Prop} {α : Type} {P : α → Prop}:
   (∃x:α, P x) → (∀x:α, (P x → R)) → R := by
   intro f g
   cases f
   apply g
   assumption

example {R : Prop} (h : R) (a: ∃x:Nat, x > 42 ∧ x < 100) (b: ∃y:Nat, y > 100 ∧ y < 128) : R := by
  elim exE'
  exact h
  done

-- 3/ Destructing compound definitions

structure dummyStruct :=
  mkDummy :: (f0: Nat) (f1: Nat)

def isValidDummy (x : dummyStruct) : Prop :=
   (x.f0 * x.f1) > 42 ∧
   (∃d:Nat, d > 5 ∧ d ∣ x.f0 ∧ d ∣ x.f1)

def isValidDummyE {x : dummyStruct} (v: isValidDummy x):
   (∀d:Nat, d > 5 → d ∣ x.f0 → d ∣ x.f1 → x.f0 * x.f1 > 42 → R) → R := by
  intro h
  simp [isValidDummy] at v
  elim conjE
  elim exE'
  elim conjE
  apply h <;> assumption
  done

example {x y : dummyStruct} (vx : isValidDummy x) (vy : isValidDummy y) : true := by
  elim isValidDummyE -- Breaks up both validity assumptions
  simp
  done

-- 4/ Case-splitting on natural numbers

theorem bound_nat_succ {i n : Nat} (lt: i < n) : i = n-1 ∨ i < n-1 := by omega
theorem bound_nat_succE {R : Prop} {i n : Nat} (lt: i < n) (t0 : i = n-1 → R) (t1 : i < n-1 → R) : R :=
  by
     cases (bound_nat_succ lt)
     apply t0
     assumption
     apply t1
     assumption

-- Syntax directed version of bound_nat_succE
theorem bound_nat_succE' {R : Prop} {i n : Nat} (lt: i < Nat.succ n) (t0 : i = n → R) (t1 : i < n → R) : R := by
  apply (bound_nat_succE lt) <;> simp <;> assumption

example {P : Nat → Prop} {i : Nat} (h : P i /- just to avoid sorry-/)
  (lt: i < Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) : P i := by
  elim bound_nat_succE' /- Now we have 4 goals for i=0,1,2,3 -/
  <;> exact h
  done
