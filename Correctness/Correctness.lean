/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Leonardo de Moura
-/

/-
Lean4 Formalization of the ACL2 paper
"Verification Condition Generation via Theorem Proving"
(https://link.springer.com/chapter/10.1007/11916277_25)
-/

import Correctness.Iterate
import Correctness.Basic

namespace Correctness

open Sys (next run)
open Spec (pre post exit)
open Spec' (cut assert)
open Iterate (iterate iterate_eq)
open Classical

theorem not_forall_eq_exists_not (p : α → Prop) : (¬ ∀ x, p x) = ∃ x, ¬ p x := by
  apply propext
  constructor
  · intro h₁
    apply byContradiction
    intro h₂
    have := Iff.mp not_exists h₂
    simp at this
    contradiction
  · intro h₁ h₂
    have ⟨a, ha⟩ := h₁
    have := h₂ a
    contradiction

/- Result from page 2: I1,I2,I3 implies Partial Correctness. -/
theorem by_inv [Sys σ] [Spec σ] (inv : σ → Prop)
    (ini  : ∀ s, pre s → inv s)  -- I1
    (step : ∀ s, inv s → ¬ exit s → inv (next s)) -- I2
    (stop : ∀ s, inv s → exit s → post s)  -- I3
    : PartialCorrectness σ :=
  fun s n hp he =>
    let rec find (i : Nat) (h : inv (run s i)) (hle : i ≤ n) : ∃ m : Nat, m ≤ n ∧ exit (run s m) ∧ post (run s m) :=
      if hn : i < n then
        if he : exit (run s i) then
          ⟨i, Nat.le_of_lt hn, he, stop _ h he⟩
        else
          have : inv (run s (i+1)) := by
            rw [← next_run]; exact step _ h he
          find (i+1) this hn
      else
        have := Nat.ge_of_not_lt hn
        have := Nat.le_antisymm this hle
        have hinv : inv (run s n) := by subst this; assumption
        have hpost : post (run s n) := stop _ hinv he
        ⟨n, Nat.le_refl _, he, hpost⟩
    find 0 (ini _ hp) (Nat.zero_le _)

noncomputable def csteps [Sys σ] [Spec' σ] (s : σ) (i : Nat) : Nat :=
  iterate (fun (s, i) => if cut s then .inl i else .inr (next s, i + 1)) (s, i)

theorem csteps_eq [Sys σ] [Spec' σ] (s : σ) (i : Nat)
        : csteps s i = if cut s then i
                       else csteps (next s) (i + 1) := by
  unfold csteps
  conv => lhs; rw [iterate_eq]
  by_cases cut s <;> simp [*]

/--
Helper theorem for defining `d` described in the paper.
-/
theorem d_ex [Sys σ] [Spec' σ] : ∃ d : σ, cut d ↔ ∀ s : σ, cut s := by
  by_cases ∀ s : σ, cut s
  next h =>
    exists Sys.some
    constructor
    · intro; assumption
    · intro; exact h Sys.some
  next h =>
    have ⟨d, hd⟩ := Eq.mp (not_forall_eq_exists_not ..) h
    exists d
    constructor
    · intro; contradiction
    · intro h'; have := h' d; contradiction

noncomputable def d [Sys σ] [Spec' σ] : σ :=
  choose d_ex

theorem d_spec [Sys σ] [Spec' σ] : cut (d : σ) ↔ ∀ s : σ, cut s :=
  choose_spec d_ex

noncomputable def nextc [Sys σ] [Spec' σ] (s : σ) : σ :=
  if cut (run s (csteps s 0)) then
    run s (csteps s 0)
  else
    d

theorem csteps_cut [Sys σ] [Spec' σ] {s : σ} (h : cut s) (i : Nat) : csteps s i = i := by
  rw [csteps_eq]
  simp [*]

theorem csteps_not_cut [Sys σ] [Spec' σ] {s : σ} (h₁ : ¬ cut s) (h₂ : csteps (next s) (i+1) = j) : csteps s i = j := by
  rw [csteps_eq]
  simp [h₁]
  assumption

/--
Helper theorem. Given a state `s` and `cut (run s n)` for `n`, then there is
`k` such that `csteps s 0 = k` and `k ≤ n`.
Note that `cut (run s n)` ensures `csteps s 0` terminates because we will find a `cut` in at most `n` steps.
-/
theorem find_next_cut [Sys σ] [Spec' σ] (s : σ) (hc : cut (run s n)) :
  ∃ k : Nat, csteps s 0 = k ∧ k ≤ n ∧ cut (run s k) :=
  let rec loop (s' : σ) (i : Nat) (hle : i ≤ n) (heq : s' = run s i) :
    ∃ k : Nat, csteps s' i = k ∧ k ≤ n ∧ cut (run s k) :=
     if hn : i < n then
       if hc : cut s' then
         have := csteps_cut hc i
         ⟨i, this, hle, by subst s'; assumption⟩
       else
         have ⟨k, hs, hkn, hck⟩ := loop (next s') (i+1) hn (by simp [heq, run_succ'])
         ⟨k, csteps_not_cut hc hs, hkn, hck⟩
     else
       have hin : i = n := by omega
       have := csteps_cut hc i
       ⟨n, by subst s' i; assumption, Nat.le_refl .., by assumption⟩
  loop s 0 (Nat.zero_le ..) rfl

/--
Theorem 1 from page 5. It shows that if V1-V4 hold, then we have partial
correctness.
-/
theorem partial_correctness_from_verification_conditions [Sys σ] [Spec' σ]
    (v1 : ∀ s : σ, pre s → assert s)
    (v2 : ∀ s : σ, exit s → cut s)
    (v3 : ∀ s : σ, assert s → exit s → post s)
    (v4 : ∀ s : σ, assert s → ¬ exit s → assert (nextc (next s)))
    : PartialCorrectness σ :=
  fun s n hp hexit =>
    let rec find (i : Nat) (h : assert (run s i)) (hle : i ≤ n) : ∃ m : Nat, m ≤ n ∧ exit (run s m) ∧ post (run s m) :=
      if hn : i < n then
        if he : exit (run s i) then
          ⟨i, Nat.le_of_lt hn, he, v3 _ h he⟩
        else
          have : cut (run (run s (i + 1)) (n - Nat.succ i)) := by
            rw [run_run, Nat.add_one, Nat.add_sub_cancel' hn]
            exact v2 _ hexit
          have ⟨k, hk, hlek, hck⟩ := find_next_cut (run s (i+1)) this
          have hle' : i + 1 + k ≤ n := by
            exact (Nat.le_sub_iff_add_le' hn).mp hlek
          have : assert (nextc (next (run s i))) := v4 _ h he
          have h' : assert (run s (i + 1 + k)) := by
            rw [run_run] at hck
            rw [nextc, next_run, hk, run_run] at this
            simp [hck] at this
            assumption
          have : n - (i + 1 + k) < n - i := by
            apply Nat.sub_lt_sub_left; assumption; simp_arith
          find (i + 1 + k) h' hle'
      else
        have := Nat.ge_of_not_lt hn
        have := Nat.le_antisymm this hle
        have ha : assert (run s n) := by subst this; assumption
        have hpost : post (run s n) := v3 _ ha hexit
        ⟨n, Nat.le_refl _, hexit, hpost⟩
    find 0 (v1 _ hp) (Nat.zero_le ..)

end Correctness
