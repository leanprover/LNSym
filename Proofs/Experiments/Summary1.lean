/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

This example demonstrates proof states involving unfolding program state,
and shows the neeed for effects aggregation we anticipate we'd need to do to reason about the net result of a program's effects.
-/
import Arm

theorem resolve_state_equations_reg_shadow (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 sf : ArmState)
  (h_s1 : (r (StateField.SFP 0#5) s1 = r (StateField.SFP 31#5) s0) ∧
          (r StateField.PC s1 = 0#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 0#5) → r f s1 = r f s0) ∧
          (s1.program = s0.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s1 = read_mem_bytes n addr s0)
  (h_s2 : (r (StateField.SFP 0#5) s2 = r (StateField.SFP 30#5) s1) ∧
          (r StateField.PC s2 = 4#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 0#5) → r f s2 = r f s1) ∧
          (s2.program = s1.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s2 = read_mem_bytes n addr s1)
  (h_s3 : (r (StateField.SFP 2#5) s3 = r (StateField.SFP 29#5) s2) ∧
          (r StateField.PC s3 = 8#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 2#5) → r f s3 = r f s2) ∧
          (s3.program = s2.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s3 = read_mem_bytes n addr s2)
  (h_s4 : (r (StateField.SFP 3#5) s4 = r (StateField.SFP 28#5) s3) ∧
          (r StateField.PC s4 = 12#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 3#5) → r f s4 = r f s3) ∧
          (s4.program = s3.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s4 = read_mem_bytes n addr s3)
  (h_s5 : (r (StateField.SFP 4#5) s5 = r (StateField.SFP 27#5) s4) ∧
          (r StateField.PC s5 = 16#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 4#5) → r f s5 = r f s4) ∧
          (s5.program = s4.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s5 = read_mem_bytes n addr s4)
  (h_s6 : (r (StateField.SFP 5#5) s6 = r (StateField.SFP 26#5) s5) ∧
          (r StateField.PC s6 = 20#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 5#5) → r f s6 = r f s5) ∧
          (s6.program = s5.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s6 = read_mem_bytes n addr s5)
  (h_s7 : (r (StateField.SFP 6#5) s7 = r (StateField.SFP 25#5) s6) ∧
          (r StateField.PC s7 = 24#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 6#5) → r f s7 = r f s6) ∧
          (s7.program = s6.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s7 = read_mem_bytes n addr s6)
  (h_s8 : (r (StateField.SFP 7#5) s8 = r (StateField.SFP 24#5) s7) ∧
          (r StateField.PC s8 = 28#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 7#5) → r f s8 = r f s7) ∧
          (s8.program = s7.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s8 = read_mem_bytes n addr s7)
  (h_s9 : (r (StateField.SFP 8#5) s9 = r (StateField.SFP 23#5) s8) ∧
          (r StateField.PC s9 = 32#64) ∧
          (∀ (f : StateField), (f ≠ StateField.PC ∧ f ≠ StateField.SFP 8#5) → r f s9 = r f s8) ∧
          (s9.program = s8.program) ∧
        ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr s9 = read_mem_bytes n addr s8)
  (h_run : sf = run 0 s9) :
  ((r StateField.PC sf = 32#64) ∧
   (r (StateField.SFP 0#5) sf = r (StateField.SFP 30#5) s0) ∧
   (r (StateField.SFP 2#5) sf = r (StateField.SFP 29#5) s0) ∧
   (r (StateField.SFP 3#5) sf = r (StateField.SFP 28#5) s0) ∧
   (r (StateField.SFP 4#5) sf = r (StateField.SFP 27#5) s0) ∧
   (r (StateField.SFP 5#5) sf = r (StateField.SFP 26#5) s0) ∧
   (r (StateField.SFP 6#5) sf = r (StateField.SFP 25#5) s0) ∧
   (r (StateField.SFP 7#5) sf = r (StateField.SFP 24#5) s0) ∧
   (r (StateField.SFP 8#5) sf = r (StateField.SFP 23#5) s0) ∧
   (∀ (f : StateField), (f ≠ StateField.PC ∧
                         f ≠ StateField.SFP 0#5 ∧
                         f ≠ StateField.SFP 2#5 ∧
                         f ≠ StateField.SFP 3#5 ∧
                         f ≠ StateField.SFP 4#5 ∧
                         f ≠ StateField.SFP 5#5 ∧
                         f ≠ StateField.SFP 6#5 ∧
                         f ≠ StateField.SFP 7#5 ∧
                         f ≠ StateField.SFP 8#5) →
      r f sf = r f s0) ∧
   (sf.program = s0.program) ∧
   ∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr sf = read_mem_bytes n addr s0) := by
  unfold run at h_run; subst sf
  simp_all (config := {decide := true}) only [minimal_theory]
  done

/-- info: 'resolve_state_equations_reg_shadow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolve_state_equations_reg_shadow
