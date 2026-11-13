/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tactics.StepThms

/-! `#genStepEqTheorems` with `genStepEqTheorems.vcgenSpecs` also emits `vcgen` specs. -/

open Std.WP ArmVCGen
set_option experimental.vcgen true

namespace VCGenTest

def prog : Program :=
  def_program
  [(0x1000#64, 0xd2800540#32),  -- movz x0, #42
   (0x1004#64, 0x91000400#32)]  -- add  x0, x0, #1

set_option genStepEqTheorems.vcgenSpecs true in
#genStepEqTheorems prog

/--
info: VCGenTest.prog.vcgen_spec_0x1000 (Q : Unit → Assn) (e : EStack⟨⟩) (inst : BitVec 32) :
  ⦃
    Lean.Order.meet (fun s => Side prog (4096#64) s) fun s =>
      ∀ (s' : ArmState),
        Next (fun {s} => w StateField.PC (4100#64) (w (StateField.GPR 0#5) (BitVec.partInstall 0 16 42#16 0#64) s)) s
            s' →
          Side prog (4100#64) s' → Q () s' ⦄
    ArmCmd.stepAt (4096#64) inst ⦃ Q; e ⦄
-/
#guard_msgs in #check prog.vcgen_spec_0x1000

#genVCGenSegment cmd := buildSeg prog (fun _ => false) 10 0x1000#64

example : cmd = trace prog := rfl

example :
    ⦃ fun s => s.program = prog ∧ r StateField.PC s = 0x1000#64 ∧
               r StateField.ERR s = StateError.None ∧ CheckSPAlignment s ⦄
    cmd
    ⦃ fun _ s => r (StateField.GPR 0#5) s = 43#64 ∧ r StateField.PC s = 0x1008#64 ⦄ := by
  unfold cmd
  vcgen
  all_goals arm_vc

end VCGenTest
