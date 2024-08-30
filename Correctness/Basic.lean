/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Leonardo de Moura, Shilpi Goel
-/

/--
A system with state `σ` is defined by a step relation `next`.
-/
class Sys (σ : Type) where
  some : σ -- σ is not the empty type
  next : σ → σ

instance [Sys σ]: Inhabited σ where
  default := Sys.some

def Sys.run [Sys σ] (s : σ) (n : Nat) : σ :=
  match n with
  | 0 => s
  | n+1 => run (next s) n

open Sys

theorem run_succ [Sys σ] (s : σ) (n : Nat) : run s (n+1) = run (next s) n :=
  rfl

theorem run_succ' [Sys σ] (s : σ) (n : Nat) : run s (n+1) = next (run s n) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => rw [run, ih, run_succ]

theorem next_run [Sys σ] (s : σ) (i : Nat) : next (run s i) = run s (i + 1) := by
  induction i generalizing s with
  | zero => simp [run]
  | succ i ih => rw [run, run, ← ih]

theorem run_run [Sys σ] (s : σ) (i j : Nat) : run (run s i) j = run s (i+j) := by
  induction i generalizing s with
  | zero => simp [run]
  | succ i ih => rw [run, ih, Nat.succ_add, run]

/--
A program's specification can be characterized by the following three predicates:
- `pre`:  pre-condition
- `post`: post-condition
- `exit`: exit states
-/
class Spec (σ : Type) where
  pre  : σ → Prop
  post : σ → σ → Prop
  exit : σ → Prop

/--
In assertional methods, we specify interesting "cutpoints" of a program using
`cut` and assertions that must hold at those cutpoints using `assert`.
-/
class Spec' (σ : Type) extends Spec σ where
  cut    : σ → Bool
  assert : σ → σ → Prop

/--
Partial correctness: involves showing that for any state `s` satisfying `pre`,
the predicate `post` holds at the first `exit` state reachable from `s` (if some
such state exists).
-/
def PartialCorrectness (σ : Type) [Sys σ] [Spec σ] : Prop :=
  open Spec in
  ∀ (s : σ) n, pre s → exit (run s n) → ∃ m, m ≤ n ∧ exit (run s m) ∧ post s (run s m)

/--
Termination: the machine starting from a state `s` satisfying `pre` eventually
reaches an `exit` state.
-/
def Termination (σ : Type) [Sys σ] [Spec σ] : Prop :=
  open Spec in
  ∀ (s : σ), pre s → ∃ n, exit (run s n)

/--
Correctness: refers to total correctness, i.e., both `PartialCorrectness` and
`Termination` hold.
-/
def Correctness (σ : Type) [Sys σ] [Spec σ] : Prop :=
  PartialCorrectness σ ∧ Termination σ
