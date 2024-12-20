/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Nathan Wetzler, Shilpi Goel, Alex Keizer
-/
import Arm.Exec
import Arm.Util
import Arm.Syntax
import Arm.Memory.SeparateAutomation
import Tactics.Sym
import Tactics.Aggregate
import Tactics.StepThms

section popcount32

open BitVec
open ArmState

/-!
Source: https://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel

int popcount_32 (unsigned int v) {
  v = v - ((v >> 1) & 0x55555555);
  v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
  v = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
  return(v);
}
-/

def popcount32_spec_rec (i : Nat) (x : BitVec 32) : BitVec 32 :=
  match i with
  | 0 => 0#32
  | i' + 1 =>
    let bit_idx := BitVec.getLsbD x i'
    (BitVec.ofBool bit_idx).zeroExtend 32 +
     popcount32_spec_rec i' x

def popcount32_spec (x : BitVec 32) : BitVec 32 :=
  popcount32_spec_rec 32 x

def popcount32_program : Program :=
  def_program
  [(0x4005b4#64 , 0xd10043ff#32), -- sub sp, sp, #0x10
   (0x4005b8#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x4005bc#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005c0#64 , 0x53017c00#32), -- lsr w0, w0, #1
   (0x4005c4#64 , 0x1200f000#32), -- and w0, w0, #0x55555555
   (0x4005c8#64 , 0xb9400fe1#32), -- ldr w1, [sp, #12]
   (0x4005cc#64 , 0x4b000020#32), -- sub w0, w1, w0
   (0x4005d0#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x4005d4#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005d8#64 , 0x1200e401#32), -- and w1, w0, #0x33333333
   (0x4005dc#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005e0#64 , 0x53027c00#32), -- lsr w0, w0, #2
   (0x4005e4#64 , 0x1200e400#32), -- and w0, w0, #0x33333333
   (0x4005e8#64 , 0x0b000020#32), -- add w0, w1, w0
   (0x4005ec#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x4005f0#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005f4#64 , 0x53047c01#32), -- lsr w1, w0, #4
   (0x4005f8#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005fc#64 , 0x0b000020#32), -- add w0, w1, w0
   (0x400600#64 , 0x1200cc01#32), -- and w1, w0, #0xf0f0f0f
   (0x400604#64 , 0x3200c3e0#32), -- mov w0, #0x1010101
   (0x400608#64 , 0x1b007c20#32), -- mul w0, w1, w0
   (0x40060c#64 , 0x53187c00#32), -- lsr w0, w0, #24
   (0x400610#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x400614#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x400618#64 , 0x910043ff#32), -- add sp, sp, #0x10
   (0x40061c#64 , 0xd65f03c0#32)] -- ret

#genStepEqTheorems popcount32_program

-- set_option trace.simp_mem.info true in
theorem popcount32_sym_meets_spec (s0 sf : ArmState)
  (h_s0_pc         : read_pc s0 = 0x4005b4#64)
  (h_s0_program    : s0.program = popcount32_program)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_s0_err        : read_err s0 = StateError.None)
  (h_run           : sf = run 27 s0) :
  -- The final state `sf` is error-free.
  read_err sf = StateError.None ∧
  -- Register `w0` in `sf` contains the correct value.
  w0 sf = popcount32_spec (w0 s0) ∧
  -- The frame condition describes which state components are not affected by
  -- this program's execution.
  REGS_UNCHANGED_EXCEPT [(.GPR 0), (.GPR 1), .SP, .PC] (sf, s0) ∧
  MEM_UNCHANGED_EXCEPT  [((r .SP s0 - 16#64), 16)]     (sf, s0) := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic simulation
  sym_n 27
   -- TODO(@bollu): automation for SP alignment
  case h_s1_sp_aligned =>
    apply Aligned_BitVecSub_64_4 (by assumption) (by decide)
  case h_s26_sp_aligned =>
    apply Aligned_BitVecAdd_64_4 (by assumption) (by decide)
  -- Split the conclusion
  repeat' apply And.intro
  · -- Functional Correctness
    simp only [popcount32_spec, popcount32_spec_rec]
    bv_decide
  · -- Register Frame Condition
    simp only [List.mem_cons, List.mem_singleton, not_or, and_imp,
      List.not_mem_nil, not_false_eq_true, true_implies] at *
    sym_aggregate
  · -- Memory Frame Condition
    intro n addr h_separate
    simp only [memory_rules] at *
    repeat (simp_mem; sym_aggregate)
  done

/--
info: 'popcount32_sym_meets_spec' depends on axioms:
[propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms popcount32_sym_meets_spec

-------------------------------------------------------------------------------

end popcount32
