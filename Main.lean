/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import «Arm»

def verbose_option (args : List String) : Bool :=
  "--verbose" ∈ args

def find_index (e : String) (xs : List String) : Option Nat :=
  let rec find_index_aux (e : String) (xs : List String) (acc : Nat) : Option Nat :=
    match xs with
    | [] => none
    | x :: rest =>
      if x == e then
        acc
      else
        find_index_aux e rest (acc + 1)
  find_index_aux e xs 0

-- Default number of tests/instruction
def default_numTests : Nat := 3

def numTests_option (args : List String) : IO Nat :=
  let maybe_idx := find_index "--num-tests" args
  match maybe_idx with
   | none => pure default_numTests
   | some idx =>
     let n_idx := idx + 1
     -- We expect the number of tests to immmediately follow
     -- "--num-tests".
     let n_str := args.get! n_idx
     let maybe_n := n_str.toNat?
     match maybe_n with
     | some n => pure n
     | none => throw (IO.userError
                      ("Expected --num-tests to be followed by " ++
                       s!"a natural number, but found '{n_str}' instead!"))

def main (args : List String) : IO UInt32 := do
  let verbose := verbose_option args
  let num_tests ← numTests_option args
  Cosim.run_all_tests verbose num_tests
