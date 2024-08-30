/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

The goal is to prove that this program implements absolute value correctly.
-/
import Arm
import Tactics.StepThms
import Tactics.Sym
import Tactics.CSE
namespace Abs

def program : Program :=
  def_program
   [(0x4005d0#64, 0x2a0003e1#32), --  mov w1, w0
    (0x4005d4#64, 0x131f7c00#32), --  asr w0, w0, #31
    (0x4005d8#64, 0x0b000021#32), --  add w1, w1, w0
    (0x4005dc#64, 0x4a000020#32), --  eor w0, w1, w0
    (0x4005e0#64, 0xd65f03c0#32)] --  ret

def spec (x : BitVec 32) : BitVec 32 :=
  -- We prefer the current definition as opposed to:
  -- BitVec.ofNat 32 x.toInt.natAbs
  -- because the above has functions like `toInt` that do not play well with
  -- bitblasting/LeanSAT.
  let msb := BitVec.extractLsb 31 31 x
  if msb == 0#1 then
    x
  else
    (0#32 - x)

#genStepEqTheorems program

theorem correct
  {s0 sf : ArmState}
  (h_s0_pc : read_pc s0 = 0x4005d0#64)
  (h_s0_program : s0.program = program)
  (h_s0_err : read_err s0 = StateError.None)
  (h_s0_sp : CheckSPAlignment s0)
  (h_run : sf = run (program.length - 1) s0) :
  read_gpr 32 0 sf = spec (read_gpr 32 0 s0) ∧
  read_err sf = StateError.None := by
  simp (config := {ground := true}) only at h_run

  sym_n 4

  simp only [spec, AddWithCarry]
  split <;> bv_decide

/--
info: 'Abs.correct' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms correct

end Abs
