/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel

Experimental: Use the Correctness module to prove that this program implements
absolute value correctly. The objective of this exercise is to determine the
"shape" of the lemmas that are needed for automation and/or to modify the
definitions in Correctness, if needed.
-/
import Arm
import Tactics.StepThms
import Tactics.Sym
import Correctness.ArmSpec

namespace AbsVCG

def program : Program :=
  def_program
   [
    (0x4005d0#64, 0x2a0003e1#32), --  mov w1, w0
    (0x4005d4#64, 0x131f7c00#32), --  asr w0, w0, #31
    (0x4005d8#64, 0x0b000021#32), --  add w1, w1, w0
    (0x4005dc#64, 0x4a000020#32), --  eor w0, w1, w0
    (0x4005e0#64, 0xd65f03c0#32)] --  ret

/-- Precondition for the correctness of the `Abs` program. -/
def abs_pre (s : ArmState) : Prop :=
  read_pc s = 0x4005d0#64 ∧
  s.program = program ∧
  read_err s = StateError.None ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment s

/-- Specification of the absolute value computation for a 32-bit bitvector. -/
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

/-- Postcondition for the correctness of the `Abs` program. -/
def abs_post (s0 sf : ArmState) : Prop :=
  read_gpr 32 0#5 sf = spec (read_gpr 32 0#5 s0) ∧
  read_pc sf = 0x4005e0#64 ∧
  read_err sf = StateError.None ∧
  CheckSPAlignment sf

/-- Function identifying the exit state(s) of the program. -/
def abs_exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = 0x4005e0#64

/-- Function identifying the cutpoints of the program. -/
def abs_cut (s : ArmState) : Bool :=
  read_pc s = 0x4005d0#64 -- First instruction
  ||
  read_pc s = 0x4005e0#64 -- Last instruction

/-- Function that attaches assertions at the cutpoints of this program. -/
def abs_assert (s0 si : ArmState) : Prop :=
  abs_pre s0 ∧
  if read_pc si = 0x4005d0#64 then
    si = s0
  else if read_pc si = 0x4005e0#64 then
    abs_post s0 si
  else
    False

instance : Spec' ArmState where
  pre    := abs_pre
  post   := abs_post
  exit   := abs_exit
  cut    := abs_cut
  assert := abs_assert

theorem Abs.csteps_eq (s : ArmState) (i : Nat) :
  Correctness.csteps s i = if abs_cut s then i
                           else Correctness.csteps (run 1 s) (i + 1) := by
  rw [Correctness.csteps_eq]
  simp only [Sys.next, Spec'.cut, run]
  done

-------------------------------------------------------------------------------
-- Generating the program effects and non-effects

-- set_option trace.gen_step.print_names true in
#genStepEqTheorems program

-- (FIXME) Obtain *_cut theorems for each instruction automatically.

theorem program.stepi_0x4005d0_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d0#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  abs_cut sn = false ∧
  r StateField.PC sn = 0x4005d4#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005d0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005d4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  abs_cut sn = false  ∧
  r StateField.PC sn = 0x4005d8#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005d4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005d8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  abs_cut sn = false  ∧
  r StateField.PC sn = 0x4005dc#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005d8 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005dc_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005dc#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  abs_cut sn = true  ∧
  r StateField.PC sn = 0x4005e0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005dc h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem nextc_to_run_from_0x4005d0 (h : abs_pre s0) :
  (Correctness.nextc (Sys.run s0 1)) = run 4 s0 := by
  simp only [abs_pre, state_simp_rules] at h
  obtain ⟨h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned⟩ := h
  simp only
    [Correctness.nextc, Correctness.arm_run,
     Spec'.cut, minimal_theory]

  rw [Abs.csteps_eq]
  have h_step_1 := program.stepi_0x4005d0_cut s0 (run 1 s0)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s1 : run 1 s0 = s1 at h_step_1

  rw [Abs.csteps_eq]
  have h_step_2 := program.stepi_0x4005d4_cut s1 (run 1 s1)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s2 : run 1 s1 = s2 at h_step_2

  rw [Abs.csteps_eq]
  have h_step_3 := program.stepi_0x4005d8_cut s2 (run 1 s2)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s3 : run 1 s2 = s3 at h_step_3

  rw [Abs.csteps_eq]
  have h_step_4 := program.stepi_0x4005dc_cut s3 (run 1 s3)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s4 : run 1 s3 = s4 at h_step_4

  have h_s4_s1 : s4 = run 3 s1 := by
    simp only [←h_s4, ←h_s3, ←h_s2, ←run_plus]
  simp only [←h_s4_s1, h_step_4, minimal_theory]
  simp only [h_s4_s1, ←h_s1, ←run_plus]
  done

theorem effects_of_nextc_from_0x4005d0 (h_pre : abs_pre s0)
  (_h_pc : read_pc s0 = 0x4005d0#64)
  (h_run : sn = Correctness.nextc (Sys.run s0 1)) :
  r StateField.PC sn = 0x4005e0#64 ∧
  r (StateField.GPR 0#5) sn =
    BitVec.zeroExtend 64
      (AddWithCarry (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s0))
          (BitVec.replicate 32 (BitVec.extractLsb 31 31 (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s0))) &&&
              0xfffffffe#32 |||
            (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s0)).rotateRight 31 &&& 0xffffffff#32 &&& 0x1#32)
          0x0#1).fst ^^^
    (BitVec.zeroExtend 64
          (BitVec.replicate 32 (BitVec.extractLsb 31 31 (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s0)))) &&&
        0xfffffffe#64 |||
      BitVec.zeroExtend 64 ((BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s0)).rotateRight 31) &&& 0xffffffff#64 &&&
        0x1#64) ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  rw [nextc_to_run_from_0x4005d0 h_pre] at h_run
  obtain ⟨h_pc, h_program, h_err, h_sp_aligned⟩ := h_pre
  simp only [state_simp_rules] at *
  -- Symbolic simulation
  -- (FIXME) Why do we need `try assumption` below?
  sym_n 4 at s0 <;> try assumption
  -- Aggregate the effects
  simp only [run] at h_run
  subst sn
  simp only [abs_cut,
            h_s4_err, h_s4_pc, h_s4_program, h_s4_sp_aligned,
            state_simp_rules, minimal_theory]
  simp only [h_step_4, h_step_3, h_step_2, h_step_1,
             state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_verification_conditions
  case v1 =>
    intros s0 h_pre
    simp only [Spec'.assert, abs_assert]
    simp only [Spec.pre] at h_pre
    simp_all only [abs_pre, minimal_theory]
  case v2 =>
    intro sf h_exit
    simp only [Spec.exit, abs_exit] at h_exit
    simp only [Spec'.cut, abs_cut]
    simp_all only [minimal_theory]
  case v3 =>
    intro s0 sf
    simp only [Spec'.assert, Spec.exit, Spec.post, abs_assert, abs_exit]
    intros h1 h2
    simp_all (config := {decide := true}) only [minimal_theory]
  case v4 =>
    intro s0 si h_assert h_exit
    simp [Spec.exit, abs_exit] at h_exit
    simp only [Spec'.assert, abs_assert, h_exit, minimal_theory] at h_assert
    have ⟨h_assert1, h_assert2, h_assert3⟩ := h_assert
    subst si
    clear h_exit h_assert
    generalize h_run : (Correctness.nextc (Sys.run s0 1)) = sf
    have h_effects := @effects_of_nextc_from_0x4005d0 s0 sf
    simp only [*, minimal_theory] at h_effects
    simp only [*, Spec'.assert, abs_assert, abs_post,
               state_simp_rules, bitvec_rules, minimal_theory]
    simp only [spec, AddWithCarry, bitvec_rules]
    generalize h_x0 : (r (StateField.GPR 0x0#5) s0) = x0
    simp only [state_value] at x0
    clear h_effects h_run h_assert1 h_assert2 sf h_x0 s0
    split
    case isTrue => bv_decide
    case isFalse => bv_decide
    done

theorem termination :
  Termination ArmState := by
  simp [Termination, Spec.pre, Spec.exit, abs_exit,
        state_simp_rules, bitvec_rules, minimal_theory]
  intro s h_pre
  have h_clock := @nextc_to_run_from_0x4005d0 s h_pre
  have h_effects := @effects_of_nextc_from_0x4005d0
                    s (run 4 s) h_pre
  simp only [abs_pre, state_simp_rules] at h_pre
  simp only [h_pre, h_clock, state_simp_rules, minimal_theory]
    at h_effects
  obtain ⟨h_effects_pc, h_effects⟩ := h_effects
  -- Clearing h_effects for readability.
  clear h_effects
  apply Exists.intro 4
  simp only [Correctness.arm_run, h_effects_pc]
  done

end AbsVCG
