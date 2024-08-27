/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Leonardo de Moura, Shilpi Goel
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

----------------------------------------------------------------------

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

----------------------------------------------------------------------

/--
Prove partial correctness using stepwise invariants.

We use `s0`, `si`, and `sf` to refer to initial, intermediate, and
final (exit) states respectively.

This is the result from page 2 of the paper. Note that the `inv`
function must specify an invariant for _each_ machine instruction,
which makes this proof method tedious to use for larger programs.

Also see `partial_correctness_from_verification_conditions` and
`partial_correctness_from_assertions`.
-/
theorem partial_correctness_by_stepwise_invariants [Sys σ] [Spec σ] (inv : σ → σ → Prop)
    (ini  : ∀ s0, pre s0 → inv s0 s0)  -- I1
    (step : ∀ s0 si, inv s0 si → ¬ exit si → inv s0 (next si)) -- I2
    (stop : ∀ s0 sf, inv s0 sf → exit sf → post s0 sf)  -- I3
    : PartialCorrectness σ :=
  fun s0 n hp he =>
    let rec find (i : Nat) (h : inv s0 (run s0 i)) (hle : i ≤ n)
            : ∃ m : Nat, m ≤ n ∧ exit (run s0 m) ∧ post s0 (run s0 m) :=
      if hn : i < n then
        if he : exit (run s0 i) then
          ⟨i, Nat.le_of_lt hn, he, stop _ _ h he⟩
        else
          have : inv s0 (run s0 (i+1)) := by
            rw [← next_run]; exact step _ _ h he
          find (i+1) this hn
      else
        have := Nat.ge_of_not_lt hn
        have := Nat.le_antisymm this hle
        have hinv : inv s0 (run s0 n) := by subst this; assumption
        have hpost : post s0 (run s0 n) := stop _ _ hinv he
        ⟨n, Nat.le_refl _, he, hpost⟩
    find 0 (ini _ hp) (Nat.zero_le _)

----------------------------------------------------------------------

-- Prove partial correctness using inductive assertions using the
-- functions `csteps` (to characterize the number of steps to reach
-- the next cutpoint) and `nextc` (to characterize the next cutpoint
-- state). Note that the function `csteps` is partial: if no cutpoint
-- is reachable from `s`, then the recursion does not terminate.

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

theorem csteps_cut [Sys σ] [Spec' σ] {s : σ} (h : cut s) (i : Nat) :
  csteps s i = i := by
  rw [csteps_eq]
  simp [*]

theorem csteps_not_cut [Sys σ] [Spec' σ] {s : σ} (h₁ : ¬ cut s)
  (h₂ : csteps (next s) (i+1) = j) : csteps s i = j := by
  rw [csteps_eq]
  simp [h₁]
  assumption

/--
Helper theorem. Given a state `s` and `cut (run s n)` for `n`, then
there is `k` such that `csteps s 0 = k` and `k ≤ n`.
Note that `cut (run s n)` ensures `csteps s 0` terminates because we
will find a `cut` in at most `n` steps.
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
Prove partial correctness using inductive assertions and functions
`csteps` and `nextc`.

We use `s0`, `si`, and `sf` to refer to initial, intermediate, and
final (exit) states respectively.

This is Theorem 1 from page 5 of the paper. This proof method is more
convenient to use than `partial_correctness_by_stepwise_invariants`
because we need only attach assertions at certain cutpoints. However,
it may still be tedious to use from the point of view of automation
because it is difficult to both symbolically simulate an instruction
and unwind `csteps` in tandem. So far, we have found that it is
easiest to determine what concrete value `csteps` yields (via symbolic
simulation), and then perform symbolic simulation -- however, then we
end up doing simulation twice, which is expensive.

Also see `partial_correctness_from_assertions`.
-/
theorem partial_correctness_from_verification_conditions [Sys σ] [Spec' σ]
    (v1 : ∀ s0 : σ, pre s0 → assert s0 s0)
    (v2 : ∀ sf : σ, exit sf → cut sf)
    (v3 : ∀ s0 sf : σ, assert s0 sf → exit sf → post s0 sf)
    -- We prefer to use `run` instead of `step`.
    (v4 : ∀ s0 si : σ, assert s0 si → ¬ exit si → assert s0 (nextc (run si 1)))
    : PartialCorrectness σ :=
  fun s0 n hp hexit =>
    let rec find (i : Nat) (h : assert s0 (run s0 i)) (hle : i ≤ n) :
                 ∃ m : Nat, m ≤ n ∧ exit (run s0 m) ∧ post s0 (run s0 m) :=
      if hn : i < n then
        if he : exit (run s0 i) then
          ⟨i, Nat.le_of_lt hn, he, v3 _ _ h he⟩
        else
          have : cut (run (run s0 (i + 1)) (n - Nat.succ i)) := by
            rw [run_run, Nat.add_one, Nat.add_sub_cancel' hn]
            exact v2 _ hexit
          have ⟨k, hk, hlek, hck⟩ := find_next_cut (run s0 (i+1)) this
          have hle' : i + 1 + k ≤ n := by
            exact (Nat.le_sub_iff_add_le' hn).mp hlek
          have : assert s0 (nextc (next (run s0 i))) := v4 _ _ h he
          have h' : assert s0 (run s0 (i + 1 + k)) := by
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
        have ha : assert s0 (run s0 n) := by subst this; assumption
        have hpost : post s0 (run s0 n) := v3 _ _ ha hexit
        ⟨n, Nat.le_refl _, hexit, hpost⟩
    find 0 (v1 s0 hp) (Nat.zero_le ..)

----------------------------------------------------------------------

-- Prove partial correctness using inductive assertions using the
-- function `cassert` that checks if `assert` holds if at a cutpoint
-- state, or else recurs until it hits one. This function is also
-- partial: if no cutpoint is reachable, the recursion doesn't
-- terminate.

/--
`cassert s0 si i`: if this function terminates, it returns a pair,
whose first element is a `Nat = (i + the number of steps simulated
from `si` to reach the next cutpoint)`, and the second element is a
`Prop` that checks whether `assert` holds at that cutpoint state.
-/
noncomputable def cassert [Sys σ] [Spec' σ] (s0 si : σ) (i : Nat) : Nat × Prop :=
  iterate (fun (si, i) => if cut si then .inl (i, assert s0 si) else .inr (next si, i + 1)) (si, i)

theorem cassert_eq [Sys σ] [Spec' σ] (s0 si : σ) (i : Nat)
        : cassert s0 si i = if cut si then (i, assert s0 si)
                       else cassert s0 (next si) (i + 1) := by
  unfold cassert
  conv => lhs; rw [iterate_eq]
  by_cases cut si <;> simp [*]
  done

theorem cassert_cut [Sys σ] [Spec' σ] {s0 si : σ} (h : cut si) (i : Nat) :
  (cassert s0 si i).fst = i ∧
  (cassert s0 si i).snd = assert s0 si := by
  rw [cassert_eq]
  simp [*]
  done

theorem cassert_not_cut [Sys σ] [Spec' σ] {s0 si : σ} (h₁ : ¬ cut si)
  (h₂ : (cassert s0 (next si) (i+1)).fst = j) :
  (cassert s0 si i).fst = j ∧
  (cassert s0 si i).snd = (cassert s0 (next si) (i + 1)).snd := by
  rw [cassert_eq]
  simp [h₁]
  assumption
  done

theorem cassert_lower_bound [Sys σ] [Spec' σ] {s0 si : σ} (n : Nat)
  (h0 : cut (run si n))
  (h1 : (cassert s0 si i).fst = j) :
  i <= j := by
  induction n generalizing i si
  case zero =>
    unfold run at h0
    rw [cassert_eq] at h1
    simp_all only [ite_true, Nat.le_refl]
  case succ =>
    rename_i _ _ n' h_inv
    rw [run_succ] at h0
    rw [cassert_eq] at h1
    split at h1
    · omega
    · have h_inv' := @h_inv (i + 1) (next si) h0 h1
      omega
  done

theorem find_next_cut_for_cassert [Sys σ] [Spec' σ] (s0 si : σ) (hc : cut (run si n)) :
  ∃ k : Nat, (cassert s0 si 0).fst = k ∧
             (cassert s0 si 0).snd = assert s0 (run si k) ∧
             k ≤ n ∧
             cut (run si k) :=
  let rec loop (s' : σ) (i : Nat) (hle : i ≤ n) (heq : s' = run si i) :
    ∃ k : Nat, (cassert s0 s' i).fst = k ∧
               (cassert s0 s' i).snd = assert s0 (run s' (k - i)) ∧
                k ≤ n ∧ cut (run si k) :=
     if hn : i < n then
       if hc : cut s' then
         have := cassert_cut hc i
         have h_i_i : i - i = 0 := by simp only [Nat.sub_self]
         ⟨i, this.left, h_i_i ▸ this.right, hle, by subst s'; assumption⟩
       else
         have ⟨k, hs, hkn, hck⟩ := loop (next s') (i+1) hn (by simp [heq, run_succ'])
         have h_not_cut := (cassert_not_cut hc hs).right
         have : (cassert s0 s' i).snd = assert s0 (run s' (k - i)) := by
          simp only [h_not_cut, hkn]
          have h_next_cut : cut (run (next s') (n - i - 1)) := by
            rw [heq]
            have : (next (run si i)) = run (run si i) 1 := by
              simp only [run]
            simp only [this]
            have : (run (run (run si i) 1) (n - i - 1)) = run si n := by
              repeat (rw [run_run])
              have : (i + (1 + (n - i - 1))) = n := by omega
              rw [this]
              done
            simpa only [this]
          have h_lb := @cassert_lower_bound _ (i + 1) k _ _ s0
                        (next s') (n - i - 1) h_next_cut hs
          conv =>
            rhs
            unfold run
          have h_k_i : ¬ k - i = 0 := by omega
          split
          · contradiction
          · rename_i x y h_k_i_y
            simp at h_k_i_y
            have : (k - (i + 1)) = k - i - 1 := by omega
            simp [this, h_k_i_y]
          done
         ⟨k, (cassert_not_cut hc hs).left, this, hck.left, hck.right⟩
     else
       have hin : i = n := by omega
       have h_left : (cassert s0 s' i).fst = n := by
          have := @cassert_cut _ _ _ s0 _ hc n
          subst hin
          rw [heq]
          simp only [this]
       have h_right : (cassert s0 s' i).snd = assert s0 (run s' (n - i)) := by
        simp only [Nat.sub_self, eq_iff_iff]
        have := @cassert_cut _ _ _ s0 _ hc
        subst hin
        rw [heq]
        simp only [this, Nat.sub_self, eq_iff_iff, run]
        done
       ⟨n, h_left, h_right, Nat.le_refl .., by assumption⟩
  loop si 0 (Nat.zero_le ..) rfl


/--
Prove partial correctness from inductive assertions using `cassert`
function.

We use `s0`, `si`, and `sf` to refer to initial, intermediate, and
final (exit) states respectively.

This is more convenient to use that
`partial_correctness_from_inductive_assertions` because we can do
symbolic simulation and open `cassert` in tandem.
-/
theorem partial_correctness_from_assertions [Sys σ] [Spec' σ]
    (v1 : ∀ s0 : σ, pre s0 → assert s0 s0)
    (v2 : ∀ sf : σ, exit sf → cut sf)
    (v3 : ∀ s0 sf : σ, assert s0 sf → exit sf → post s0 sf)
    (v4 : ∀ s0 si : σ, assert s0 si → ¬ exit si → (cassert s0 (run si 1) 0).snd)
    : PartialCorrectness σ :=
    fun s0 n hp hexit =>
    let rec find (i : Nat) (h : assert s0 (run s0 i)) (hle : i ≤ n) :
                 ∃ m : Nat, m ≤ n ∧ exit (run s0 m) ∧ post s0 (run s0 m) :=
      if hn : i < n then
        if he : exit (run s0 i) then
          ⟨i, Nat.le_of_lt hn, he, v3 _ _ h he⟩
        else
          have : cut (run (run s0 (i + 1)) (n - Nat.succ i)) := by
            rw [run_run, Nat.add_one, Nat.add_sub_cancel' hn]
            exact v2 _ hexit

          have ⟨k, _hk, hlek, hck⟩ := find_next_cut_for_cassert s0 (run s0 (i+1)) this
          have hle' : i + 1 + k ≤ n := by
            omega
          have : (cassert s0 (next (run s0 i)) 0).snd := v4 _ _ h he
          have h' : assert s0 (run s0 (i + 1 + k)) := by
            rw [run_run] at hck
            rw [next_run] at this
            rw [run_run] at hlek
            simp_all only [Nat.succ_eq_add_one, eq_iff_iff, true_iff]
            done
          have : n - (i + 1 + k) < n - i := by
            apply Nat.sub_lt_sub_left; assumption; simp_arith
          find (i + 1 + k) h' hle'
      else
        have := Nat.ge_of_not_lt hn
        have := Nat.le_antisymm this hle
        have ha : assert s0 (run s0 n) := by subst this; assumption
        have hpost : post s0 (run s0 n) := v3 _ _ ha hexit
        ⟨n, Nat.le_refl _, hexit, hpost⟩
    find 0 (v1 s0 hp) (Nat.zero_le ..)

----------------------------------------------------------------------

noncomputable def rank_decreases [Sys σ] [Spec' σ] (rank : σ → Nat) (si sn : σ) (i : Nat) : Nat × Prop :=
  iterate (fun (sn, i) =>
    if cut sn then
      .inl (i, rank sn < rank si)
    else
      .inr (next sn, i + 1))
  (sn, i)

theorem rank_decreases_eq [Sys σ] [Spec' σ] (rank : σ → Nat) (si sn : σ) (i : Nat) :
  rank_decreases rank si sn i =
    if cut sn then (i, rank sn < rank si)
              else rank_decreases rank si (next sn) (i + 1) := by
  unfold rank_decreases
  conv => lhs; rw [iterate_eq]
  by_cases cut sn <;> simp [*]
  done

-- TODO: add condition that rank of exit state is zero.
theorem termination_from_decreasing_rank [Sys σ] [Spec' σ] (rank : σ → Nat)
    (v1 : ∀ s0 : σ, pre s0 → assert s0 s0)
    (v2 : ∀ s0 si : σ, assert s0 si → ¬ exit si → (rank_decreases rank si (run si 1) 0).snd)
    : Termination σ := by
    sorry

end Correctness
