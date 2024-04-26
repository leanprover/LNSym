import Lean
import Tactics.Elim
import Init.Data.List.Lemmas

open Lean Meta Elab.Tactic

/- Ad-hoc definitions and lemmas about fixed-length lists

MathLib has `Vec` which could be used instead; for now, we use our own
version to keep dependencies down.

-/

abbrev Vec α (n : Nat) := { v : List α // v.length = n }

@[simp]
theorem Vec_eq_transport {k l : Nat} (h : k = l) (x : Vec α k) : (h▸x).val = x.val := by cases h; simp

@[simp] def Vec.inBounds (_ : Vec α n) (i : Nat) : Prop := i < n

@[simp] def Vec.get {n : Nat} (v : Vec α n) (i : Nat) (ok : v.inBounds i) : α :=
  let hi: i < v.val.length := by simpa [v.property] using ok
  v.val[i]'hi

def Vec.empty : Vec α 0 := ⟨[], by simp⟩

def Vec.cons {n : Nat} (x : α) (v : Vec α n) : Vec α (n+1) :=
  ⟨List.cons x v.val, by simp [v.property]⟩

theorem Vec.ext'' (x y : Vec α n) (h: x.val = y.val) : x = y := by
   cases x <;> cases y; simp_all

@[simp] def Vec.append {n m : Nat} (v : Vec α n) (w : Vec α m) : Vec α (n + m) :=
  ⟨v.val ++ w.val, by simp [v.property, w.property]⟩

instance : HAppend (Vec α n) (Vec α m) (Vec α (n+m)) where
   hAppend xs ys := Vec.append xs ys

@[simp] def Vec.push {n : Nat} (v : Vec α n) (x : α): Vec α (n+1) :=
  ⟨v.val ++ [x], by simp [v.property]⟩

-- Support array-like access st[i]
@[simp] instance GetElem_Vec : GetElem (Vec α n) Nat α Vec.inBounds where
  getElem := Vec.get

-- Extensionality for fixed-length lists
@[ext] def Vec.ext {n : Nat} (v w : Vec α n) (h: ∀(i : Nat), (h : i < n) → v[i] = w[i]) : v = w := by
  apply Subtype.eq
  apply List.ext_get <;> simp [v.property, w.property]
  intros
  simp_all [getElem, GetElem_Vec, Vec.get]
  done

def Vec.ext' {n : Nat} (v w : Vec α n) : (v=w) <-> (∀(i : Nat), (h : i < n) → v[i] = w[i]) := by
  apply Iff.intro
  · simp_all
  · intros
    ext
    simp_all
  done
