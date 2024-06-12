/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Leonardo de Moura
-/

import Lean

/-!
A simple Map-like type based on lists
-/

def Map (α : Type u) (β : Type v) := List (α × β)

instance [x : Repr (List (α × β))] : Repr (Map α β) where
  reprPrec := x.reprPrec

def Map.empty : Map α β := []

def Map.find? [DecidableEq α] (m : Map α β) (a' : α) : Option β :=
  match m with
  | [] => none
  | (a, b) :: m => if a = a' then some b else find? m a'

def Map.contains [DecidableEq α] (m : Map α β) (a : α) : Bool :=
  m.find? a |>.isSome

def Map.insert [DecidableEq α] (m : Map α β) (a' : α) (b' : β) : Map α β :=
  match m with
  | [] => [(a', b')]
  | (a, b) :: m => if a = a' then (a', b') :: m else (a, b) :: insert m a' b'

def Map.erase [DecidableEq α] (m : Map α β) (a' : α) : Map α β :=
  match m with
  | [] => []
  | (a, b) :: m => if a = a' then erase m a' else (a, b) :: erase m a'

def Map.isEmpty (m : Map α β) : Bool :=
  match m with
  | [] => true
  | _ => false

def Map.size (m : Map α β) : Nat :=
  m.length

@[simp] theorem Map.find?_empty [DecidableEq α] (a : α) : (Map.empty (β := β)).find? a = none := rfl

@[simp] theorem Map.find?_insert [DecidableEq α] (m : Map α β) (a : α) (b : β) : (m.insert a b).find? a = some b := by
  induction m <;> simp [find?, insert] <;> split <;> simp [find?, *]

@[simp] theorem Map.find?_insert_of_ne [DecidableEq α] (m : Map α β) {a a' : α} (b : β) : a ≠ a' → (m.insert a b).find? a' = m.find? a' := by
  intro h; induction m <;> simp [find?, insert, *] <;> split <;> simp [find?, *]

@[simp] theorem Map.contains_empty [DecidableEq α] (a : α) : (Map.empty (β := β)).contains a = false := rfl

@[simp] theorem Map.contains_insert [DecidableEq α] (m : Map α β) (a : α) (b : β) : (m.insert a b).contains a = true := by
  simp [contains]

@[simp] theorem Map.contains_insert_of_ne [DecidableEq α] (m : Map α β) {a a' : α} (b : β) : a ≠ a' → (m.insert a b).contains a' = m.contains a' := by
  intro; simp [contains, *]

@[simp] theorem Map.isEmpty_empty : (Map.empty (α := α) (β := β)).isEmpty = true := rfl

@[simp] theorem Map.isEmpty_insert_eq_false [DecidableEq α] (m : Map α β) (a : α) (b : β) : (m.insert a b).isEmpty = false := by
  induction m <;> simp [insert]
  next => rfl
  next => split <;> simp [isEmpty]

@[simp] theorem Map.size_empty_eq : (Map.empty (α := α) (β := β)).size = 0 := rfl

@[simp] theorem Map.size_insert_eq_of_contains [DecidableEq α] (m : Map α β) (a : α) (b : β) : m.contains a = true → (m.insert a b).size = m.size := by
  induction m <;> simp [insert, size]
  case nil => simp only [contains, find?, Option.isSome_none]
  case cons head tail ih =>
    intro h; split
    next => simp
    next heq =>
      simp [contains, find?, heq] at h
      simp [contains, h, size] at ih
      simp [*]

@[simp] theorem Map.size_insert_eq_of_not_contains [DecidableEq α] (m : Map α β) (a : α) (b : β) : m.contains a = false → (m.insert a b).size = m.size + 1 := by
  induction m <;> simp [insert, size]
  case cons head tail ih =>
    intro h; split
    next heq => simp [contains, find?, heq] at h
    next heq =>
      simp [contains, find?, heq] at h
      simp [contains, h, size] at ih
      simp [*]

@[simp] theorem Map.erase_empty [DecidableEq α] (a : α) : (Map.empty (β := β)).erase a = Map.empty := rfl

@[simp] theorem Map.find?_erase [DecidableEq α] (m : Map α β) (a : α) : (m.erase a).find? a = none := by
  induction m <;> simp [erase, find?]
  split <;> simp [*, find?]

@[simp] theorem Map.find?_erase_of_ne [DecidableEq α] (m : Map α β) {a a' : α} : a ≠ a' → (m.erase a).find? a' = m.find? a' := by
  intro h
  induction m <;> simp [erase, find?]
  split <;> simp [*, find?]

@[simp] theorem Map.contains_erase [DecidableEq α] (m : Map α β) (a : α) : (m.erase a).contains a = false := by
  simp [contains]

@[simp] theorem Map.contains_erase_of_ne [DecidableEq α] (m : Map α β) {a a' : α} : a ≠ a' → (m.erase a).contains a' = m.contains a' := by
  intro; simp [contains, *]

@[simp] theorem Map.erase_insert [DecidableEq α] (m : Map α β) (a : α) (b : β) : m.contains a = false → (m.insert a b).erase a = m := by
  induction m <;> simp [insert, erase]
  next head tail ih =>
    intro h
    split
    next he => simp [contains, find?, he] at h
    next he =>
     simp [contains, find?, he] at h
     simp [contains, find?, he, h] at ih
     simp [erase, ih, he]

@[simp] theorem Map.size_erase_le [DecidableEq α] (m : Map α β) (a : α) : (m.erase a).size ≤ m.size := by
  induction m <;> simp [erase, size] at *
  split
  next => omega
  next => simp; omega

@[simp] theorem Map.size_erase_eq [DecidableEq α] (m : Map α β) (a : α) : m.contains a = false → (m.erase a).size = m.size := by
  induction m <;> simp [erase, size] at *
  split <;> simp [contains, find?, *] at *; assumption

@[simp] theorem Map.size_erase_lt [DecidableEq α] (m : Map α β) (a : α) : m.contains a = true → (m.erase a).size < m.size := by
  intro h
  induction m <;> simp [erase, size, contains, find?] at *
  next head tail ih =>
  split
  next => have := Map.size_erase_le tail a;
          -- (FIXME) This could be discharged by omega in
          -- leanprover/lean4:nightly-2024-02-24, but not in
          -- leanprover/lean4:nightly-2024-03-01.
          exact Nat.lt_succ_of_le this
  next he => simp [he] at h; simp [h] at ih; simp;
          -- (FIXME) This could be discharged by omega in
          -- leanprover/lean4:nightly-2024-02-24, but not in
          -- leanprover/lean4:nightly-2024-03-01.
             exact Nat.succ_lt_succ ih

-------------------------------------------------------------------------------

-- Programs are defined as an Map of 64-bit addresses to 32-bit
-- instructions. Map has nice lemmas that allow us to smoothly fetch
-- an instruction from the map during proofs (see
-- fetch_inst_from_program below).
abbrev Program := Map (BitVec 64) (BitVec 32)

-- Custom simplification procedure for concrete evaluation of Map.find? terms,
-- where the first argument is of type Program.

open Lean.ToExpr Lean Meta Simp

-- TODO: Can we cache the result of Map.fromExpr? somewhere? We expect to call
-- this function quite a bit for the same program map during symbolic simulation.
partial def Map.fromExpr? (e : Expr) : SimpM (Option Program) :=
  do
  match_expr e with
  | List.nil _ => return some List.nil
  | List.cons _ hd tl =>
    -- dbg_trace f!"Map.fromExpr? cons: hd {hd} \n \ntl {tl}"
    let_expr Prod.mk _ _ key_lit val_lit ← hd | return none
    -- dbg_trace f!"Map.fromExpr? cons: key_lit {key_lit} \n \nval_lit {val_lit}"
    let some key_lit_val ← BitVec.fromExpr? key_lit | return none
    let some val_lit_val ← BitVec.fromExpr? val_lit | return none
    let some tl_val ← Map.fromExpr? tl | return none
    if h₁ : key_lit_val.n = 64 then
      if h₂ : val_lit_val.n = 32 then
        return (some
                (List.cons
                  (h₁ ▸ key_lit_val.value, h₂ ▸ val_lit_val.value)
                  tl_val))
      else
        return none
    else
        return none
  | _ =>
    -- dbg_trace f!"Map.fromExpr? e: {e}"
    return none

-- TODO: Add to [simp, seval] or [state_simp_rules]?
simproc reduceMapFind? ((Map.find? _ _ : Option _)) :=
  fun e => do
  -- dbg_trace "e: {e}"
  let_expr Map.find? _ _ _ map key ← e | return .continue
  -- dbg_trace "map: {map}"
  let some map_lit ← Map.fromExpr? map | return .continue
  -- dbg_trace "e: {e}"
  let some key_lit ← BitVec.fromExpr? key | return .continue
  if h : key_lit.n = 64 then
    let new_expr := toExpr (Map.find? map_lit (h ▸ key_lit.value))
    let proof := (mkAppN (mkConst ``Eq.refl) #[(mkConst ``Bool), (mkConst ``Bool.true)])
    return .done { expr := new_expr, proof? := proof }
  else
    return .continue

example : Map.find? [(3#64, 1#32)] 3#64 = some 1#32 := by
  simp only [reduceMapFind?]
