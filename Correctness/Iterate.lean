/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Leonardo de Moura
-/

namespace Iterate
/-
The purpose of Iterate is to implement partial tail recursion that is
available in ACL2 using `defpun`; see
https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/?topic=ACL2____DEFPUN.

We define the `def iterate (f : α → Sum β α) (a : α) : β`, and prove
the equation:
```
     iterate f a = match f a with
                  | .inl b => b
                  | .inr a => iterate f a
```
-/

def test (f : α → Sum β α) (a : α) : Bool :=
  match f a with
  | .inl _ => true
  | .inr _ => false

def base [Inhabited β] (f : α → Sum β α) (a : α) : β :=
  match f a with
  | .inl b => b
  | .inr _ => default

def next (f : α → Sum β α) (a : α) (h : ¬ test f a) : α :=
  match he : f a with
  | .inl _ => by unfold test at h; simp [he] at h
  | .inr a => a

def iterate' [Inhabited β] (f : α → Sum β α) (a : α) (fuel : Nat) : Option β :=
  if fuel = 0 then
    none
  else if h : test f a then
    some (base f a)
  else
    iterate' f (next f a h) (fuel - 1)

theorem iterate'_eq [Inhabited β] (f : α → Sum β α) (a : α) (h : fuel ≠ 0)
        : iterate' f a fuel = if ht : test f a then some (base f a) else iterate' f (next f a ht) (fuel - 1) := by
  conv => lhs; unfold iterate'; simp [*]

theorem iterate'_succ_eq [Inhabited β] (f : α → Sum β α) (a : α) (fuel : Nat) :
    iterate' f a (fuel + 1) = if ht : test f a then some (base f a) else iterate' f (next f a ht) fuel := by
  conv => lhs; unfold iterate';
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_one_sub_one]

variable [Inhabited β] {f : α → Sum β α}

theorem fuel_ne_zero (h : iterate' f a fuel ≠ none) : fuel ≠ 0 := by
  intro hn; simp [hn] at h; unfold iterate' at h; simp_arith at h

theorem iterate'_next_ne_none (h : iterate' f a fuel ≠ none) (ht : ¬ test f a) : iterate' f (next f a ht) (fuel - 1) ≠ none := by
  have : fuel ≠ 0 := fuel_ne_zero h
  unfold iterate' at h
  simp [*] at h
  assumption

theorem fuel_extra (h : iterate' f a fuel ≠ none) : iterate' f a (fuel + 1) = iterate' f a fuel := by
  have : fuel ≠ 0 := fuel_ne_zero h
  have := iterate'_eq f a this
  have := iterate'_succ_eq f a fuel
  by_cases test f a <;> simp [*]
  next ht =>
    have := iterate'_next_ne_none h ht
    have ih := fuel_extra this
    have : 1 ≤ fuel := by cases fuel <;> simp [*]; contradiction
    have hf₁ : fuel - 1 + 1 = fuel := Nat.sub_add_cancel this
    simp [hf₁] at ih
    simp [ih]

theorem fuel_extra' (h : iterate' f a fuel ≠ none) :  iterate' f a (fuel + 1) ≠ none := by
  have : fuel ≠ 0 := fuel_ne_zero h
  have := iterate'_eq f a this
  have := iterate'_succ_eq f a fuel
  by_cases test f a
  next => simp_arith [*]
  next ht =>
    have := iterate'_next_ne_none h ht
    have ih := fuel_extra' this
    have : 1 ≤ fuel := by cases fuel <;> simp [*]; contradiction
    have hf₁ : fuel - 1 + 1 = fuel := Nat.sub_add_cancel this
    have : fuel + 1 - 1 = fuel := Nat.pred_succ _
    simp [hf₁] at ih
    unfold iterate'
    have : fuel + 1 ≠ 0 := by simp_arith
    simp [*]

theorem fuel_extra_ge (h₁ : fuel₁ ≤ fuel₂) (h₂ : iterate' f a fuel₁ ≠ none) : iterate' f a fuel₂ = iterate' f a fuel₁ :=
  if h : fuel₁ = fuel₂ then
    by simp [h] at h₂; simp [*]
  else
    have : fuel₁ ≠ 0 := fuel_ne_zero h₂
    have h₁' : fuel₁ + 1 ≤ fuel₂ := Nat.lt_of_le_of_ne h₁ h
    have h₂' : iterate' f a (fuel₁ + 1) ≠ none := fuel_extra' h₂
    have he := fuel_extra h₂
    have ih := fuel_extra_ge h₁' h₂'
    by simp [he] at ih; assumption
termination_by (fuel₂ - fuel₁)

theorem iterate'_det (h₁ : iterate' f a fuel₁ ≠ none) (h₂ : iterate' f a fuel₂ ≠ none) : iterate' f a fuel₁ = iterate' f a fuel₂ :=
  if h : fuel₁ ≤ fuel₂ then
    fuel_extra_ge h h₁ |>.symm
  else
    fuel_extra_ge (Nat.le_of_lt (Nat.gt_of_not_le h)) h₂

partial def iterate_impl [Inhabited β] (f : α → Sum β α) (a : α) : β :=
  match f a with
  | .inl b => b
  | .inr a => iterate_impl f a

open Classical in
@[implemented_by iterate_impl]
def iterate (f : α → Sum β α) (init : α) : β :=
  if h : ∃ fuel, iterate' f init fuel ≠ none then
    match iterate' f init (choose h) with
    | some b => b
    | none => default
  else
    default

theorem iterate_eq₁ (h : ¬ ∃ fuel, iterate' f a fuel ≠ none) : iterate f a = default := by
  simp [iterate, h]

open Classical in
theorem iterate_eq₂ (h : ∃ fuel, iterate' f a fuel ≠ none) : some (iterate f a) = iterate' f a (choose h) := by
  simp [iterate, h]
  split
  next h' => rw [←h']
  next h' =>
    have hspec := choose_spec h
    have : iterate' f a (choose h) = none := h'
    rw [this] at hspec
    contradiction

theorem fuel_ex (ht : ¬ test f a) : (∃ fuel, iterate' f (next f a ht) fuel ≠ none) → ∃ fuel, iterate' f a fuel ≠ none := by
  intro ⟨fuel, h⟩
  exists fuel+1
  unfold iterate'
  have : fuel + 1 ≠ 0 := by simp_arith
  have : fuel + 1 - 1 = fuel := Nat.pred_succ _
  simp [*]

theorem fuel_nex (ht : ¬ test f a) : (¬ ∃ fuel, iterate' f a fuel ≠ none) → (¬ ∃ fuel, iterate' f (next f a ht) fuel ≠ none) := by
  intro h h₁
  have := fuel_ex ht h₁
  contradiction

theorem fuel_ex₂' (h₁ : ¬ test f a) (h₂ : iterate' f a fuel ≠ none) : iterate' f (next f a h₁) (fuel - 1) ≠ none := by
  unfold iterate' at h₂
  by_cases fuel = 0 <;> simp [*] at h₂
  assumption

theorem fuel_ex₂ (h₁ : ¬ test f a) (h₂ : ∃ fuel, iterate' f a fuel ≠ none) : ∃ fuel, iterate' f (next f a h₁) fuel ≠ none := by
  have ⟨fuel, h₂⟩ := h₂
  unfold iterate' at h₂
  by_cases fuel = 0 <;> simp [*] at h₂
  exists fuel - 1

theorem ex_fuel_of_test (h : test f a = true) : ∃ fuel, iterate' f a fuel ≠ none := by
  exists 1
  unfold iterate'
  simp_arith [*]

open Classical in
theorem iterate_eq' (a : α) : iterate f a = if ht : test f a then base f a else iterate f (next f a ht) := by
  split
  next h =>
    have hex := ex_fuel_of_test h
    have he₁ := iterate_eq₂ hex
    have hspec := choose_spec hex
    have := fuel_ne_zero hspec
    unfold iterate' at he₁
    simp [*] at he₁
    assumption
  next h =>
    by_cases ∃ fuel, iterate' f a fuel ≠ none
    next hex =>
      have hex₂ := fuel_ex₂ h hex
      have heq₁ := iterate_eq₂ hex
      have heq₂ := iterate_eq₂ hex₂
      have : iterate' f a (choose hex) = iterate' f (next f a h) (choose hex₂) := by
        have hspec₁ := choose_spec hex
        have hne_zero := fuel_ne_zero hspec₁
        have hgt₂ := choose_spec hex₂
        conv => lhs; unfold iterate'
        simp [*]
        have hgt₁ := fuel_ex₂' h hspec₁
        exact iterate'_det hgt₁ hgt₂
      simp [← heq₁, ← heq₂] at this
      assumption
      done;
    next hex =>
      have := iterate_eq₁ hex
      have := fuel_nex h hex
      have := iterate_eq₁ this
      simp [*]

theorem iterate_eq (a : α) :
     iterate f a = match f a with
                  | .inl b => b
                  | .inr a => iterate f a := by
  split
  next b h =>
    rw [iterate_eq']
    simp [*, test, base]
  next b h =>
    rw [iterate_eq']
    simp [*, test, next]
    split
    next b he => rw [he] at h; simp at h
    next b he => rw [he] at h; simp at h; simp [h]

end Iterate
