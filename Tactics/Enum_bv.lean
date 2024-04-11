/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Lean.Elab
import Lean.Expr

open BitVec

theorem le_and_ne_implies_lt (x : Nat) (y : Nat) (h0 : x ≠ y) (h1 : x ≤ y): x < y := by
  have h : x < y ∨ x = y := by apply Nat.lt_or_eq_of_le h1
  cases h
  · assumption
  · contradiction

-- An example
-- def carry_less_add (x : BitVec 2) : BitVec 2 := x ^^^ 0b1#2
-- def lookup_cla (x : BitVec 2) : BitVec 2 :=
--   BitVec.cast (by omega) $
--   if x.toNat == 0 then 0b01#2
--   else if x.toNat == 1 then 0b0#2
--   else if x.toNat == 2 then 0b11#2
--   else 0b10#2

-- theorem example_lemma_expanded : carry_less_add = lookup_cla := by
--   funext x
--   by_cases h₀ : x = BitVec.ofNat 2 0
--   case pos =>
--     simp only [h₀]
--     decide
--   case neg =>
--     by_cases h₁ : x = BitVec.ofNat 2 1
--     case pos =>
--       simp only [h₁]
--       decide
--     case neg =>
--       by_cases h₂ : x = BitVec.ofNat 2 2
--       case pos =>
--         simp [h₂]
--         decide
--       case neg =>
--         by_cases h₃ : x = BitVec.ofNat 2 3
--         case pos =>
--           simp [h₃]
--           decide
--         case neg =>
--           rw [← ne_eq, toNat_ne] at *
--           have p4 : x.toNat < 4 := by
--             exact isLt x
--           have p3' : x.toNat ≤ 3 := by
--             apply Nat.le_of_lt_succ
--             simp only [Nat.succ_eq_add_one, Nat.reduceAdd, p4]
--           have p3 : x.toNat < 3 := by
--             apply le_and_ne_implies_lt
--             · exact h₃
--             · simp only [p3']
--           have p2' : x.toNat ≤ 2 := by
--             apply Nat.le_of_lt_succ
--             simp only [Nat.succ_eq_add_one, Nat.reduceAdd, p3]
--           have p2 : x.toNat < 2 := by
--             apply le_and_ne_implies_lt
--             · exact h₂
--             · simp only [p2']
--           have p1' : x.toNat ≤ 1 := by
--             apply Nat.le_of_lt_succ
--             simp only [Nat.succ_eq_add_one, Nat.reduceAdd, p2]
--           have p1 : x.toNat < 1 := by
--             apply le_and_ne_implies_lt
--             · exact h₁
--             · simp only [p1']
--           have p0' : x.toNat ≤ 0 := by
--             apply Nat.le_of_lt_succ
--             simp only [Nat.succ_eq_add_one, Nat.reduceAdd, p1]
--           have p0 : x.toNat = 0 := by
--             exact Nat.eq_zero_of_le_zero p0'
--           contradiction

partial def shrink (i : Nat) (N : Nat) (var : Lean.Ident)
  : Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic) := do
  let i_str := toString i
  let i_num := Lean.Syntax.mkNumLit i_str
  if i = N then
    let p_name :=
      Lean.mkIdent $ Lean.Name.mkStr Lean.Name.anonymous ("p" ++ i_str)
    let rest ← shrink (i - 1) N var
    `(tactic|
      (have $p_name:ident : BitVec.toNat $var:ident < $i_num:num := by
         exact isLt $var:ident
       $rest:tactic))
  else
    let i_pre := toString (i + 1)
    let p_pre :=
      Lean.mkIdent $ Lean.Name.mkStr Lean.Name.anonymous ("p" ++ i_pre)
    let p_name1 :=
      Lean.mkIdent $ Lean.Name.mkStr Lean.Name.anonymous ("p" ++ i_str ++ "'")
    let p_name2 :=
      Lean.mkIdent $ Lean.Name.mkStr Lean.Name.anonymous ("p" ++ i_str)
    if i ≤ 0 then
      `(tactic|
         (have $p_name1:ident : BitVec.toNat $var:ident ≤ $i_num:num := by
            apply Nat.le_of_lt_succ
            simp only [Nat.succ_eq_add_one, Nat.reduceAdd, $p_pre:ident]
          clear $p_pre:ident
          have $p_name2:ident : BitVec.toNat $var:ident = $i_num:num := by
            exact Nat.eq_zero_of_le_zero $p_name1:ident
          clear $p_name1:ident))
    else
      let h_name :=
        Lean.mkIdent $ Lean.Name.mkStr Lean.Name.anonymous ("h" ++ i_str)
      let rest ← shrink (i - 1) N var
      `(tactic|
         (have $p_name1:ident : BitVec.toNat $var:ident ≤ $i_num:num := by
            apply Nat.le_of_lt_succ
            simp only [Nat.succ_eq_add_one, Nat.reduceAdd, $p_pre:ident]
          clear $p_pre:ident
          have $p_name2:ident : BitVec.toNat $var:ident < $i_num:num := by
            apply le_and_ne_implies_lt
            · exact $h_name:ident
            · simp only [$p_name1:ident]
          clear $p_name1:ident
          $rest:tactic))

def enum_last_case (n : Nat) (var : Lean.Ident)
  : Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic) := do
  let shrink_tac ← shrink (2 ^ n) (2 ^ n) var
  `(tactic|
    (rw [← ne_eq, toNat_ne] at *
     $shrink_tac:tactic
     contradiction)
    )

partial def enum_cases_syntax (i : Nat) (n : Nat) (var : Lean.Ident)
  : Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic) := do
  if 2 ^ n ≤ i
  then let last ← enum_last_case n var
       `(tactic| $last:tactic)
  else
    let i_str := toString i
    let h_name := Lean.mkIdent $ Lean.Name.mkStr Lean.Name.anonymous ("h" ++ i_str)
    let i_num := Lean.Syntax.mkNumLit i_str
    let n_num := Lean.Syntax.mkNumLit $ toString n
    let rest ← enum_cases_syntax (i + 1) n var
    `(tactic|
       (by_cases $h_name:ident : $var:ident = (BitVec.ofNat $n_num:num $i_num:num)
        · simp only [$h_name:ident]; decide
        · $rest:tactic
        done
       )
     )

def enum_bv_fn (n : Lean.Syntax.NumLit) (var : Lean.Ident):
  Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    Lean.Elab.Tactic.evalTactic (←
      enum_cases_syntax 0 n.getNat var
    )

-- Establishing a theorem through enumeration of all values of a bit-vector
-- Assumption: the theorem has only one free variable of type `BitVec n`
elab "enum_bv" n:num var:ident : tactic => do
  enum_bv_fn n var

-- theorem example_lemma : carry_less_add = lookup_cla := by
--   funext x
--   enum_bv 2 x
