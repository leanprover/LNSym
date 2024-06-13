/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.FromMathlib

def revflat (x : List (BitVec n)) : BitVec (n * x.length) := 
  have h : x.reverse.length = x.length := by simp only [List.length_reverse]
  h ▸ BitVec.flatten (List.reverse x)

def list_create_helper (x : BitVec n) (len : Nat) (acc : List (BitVec n)) : List (BitVec n) :=
  if len <= 0 then acc
  else list_create_helper x (len - 1) (List.cons x acc)

def List.create (x : BitVec n) (len : Nat) : List (BitVec n) :=
  list_create_helper x len []

-- Functional induction: https://lean-lang.org/blog/2024-5-17-functional-induction/
theorem length_of_list_create_helper (x : BitVec n) : (list_create_helper x len acc).length = len + acc.length := by
  -- induction len, acc using list_create_helper.induct x <;> (unfold list_create_helper; simp [*]; omega)
  induction len, acc using list_create_helper.induct x
  case case1 len acc hlen =>
    unfold list_create_helper
    simp only [Nat.le_zero_eq] at *
    simp only [hlen, ↓reduceIte, Nat.zero_add]
  case case2 len acc hlen ih =>
    unfold list_create_helper
    simp only [Nat.le_zero_eq, hlen, ↓reduceIte, ih, List.length_cons]
    omega

theorem length_of_list_create (x : BitVec n) : (List.create x len).length = len := by
  unfold List.create
  apply length_of_list_create_helper

