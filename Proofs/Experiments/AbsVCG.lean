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
import Correctness.Correctness

namespace AbsVCG

def program : Program :=
  def_program
   [
    (0x4005d0#64, 0x2a0003e1#32), --  mov w1, w0
    (0x4005d4#64, 0x131f7c00#32), --  asr w0, w0, #31
    (0x4005d8#64, 0x0b000021#32), --  add w1, w1, w0
    (0x4005dc#64, 0x4a000020#32), --  eor w0, w1, w0
    (0x4005e0#64, 0xd65f03c0#32)] --  ret

/--
`Abs` structure: Field `w0` refers to the 32-bit input to the program that
is expected to be in register `w0` in the initial state, and `state` refers
to the Arm machine state.

We club the input and the state together so that we can express the
post-condition of the program only in terms of this structure `Abs`; see
`abs_post`.
-/
structure Abs where
  w0      : BitVec 32
  state   : ArmState

/--
State Machine for the `Abs` program: the `next` function only steps the
`state` and leaves `w0` unmodified.
-/
instance : Sys Abs where
  some := { w0 := 0#32, state := ArmState.default }
  next := fun abs => { w0 := abs.w0,
                       state := stepi abs.state }

/-- Precondition for the correctness of the `Abs` program. -/
def abs_pre (a : Abs) : Prop :=
  read_gpr 32 0#5 a.state = a.w0 ∧
  read_pc a.state = 0x4005d0#64 ∧
  a.state.program = program ∧
  read_err a.state = StateError.None


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
def abs_post (a : Abs) : Prop :=
  read_gpr 32 0#5 a.state = spec a.w0 ∧
  read_err a.state = StateError.None

/-- Function identifying the exit state(s) of the program. -/
def abs_exit (a : Abs) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc a.state = 0x4005e0#64

/-- Function identifying the cutpoints of the program. -/
def abs_cut (a : Abs) : Prop :=
  read_pc a.state = 0x4005d0#64 -- First instruction
  ∨
  read_pc a.state = 0x4005e0#64 -- Last instruction

/-- Function that attaches assertions at the cutpoints of this program. -/
def abs_assert (a : Abs) : Prop :=
  if read_pc a.state = 0x4005d0#64 then
    abs_pre a
  else if (read_pc a.state = 0x4005e0#64) then
    abs_post a
  else
    False

instance : Spec' Abs where
  pre    := abs_pre
  post   := abs_post
  exit   := abs_exit
  cut    := abs_cut
  assert := abs_assert

-------------------------------------------------------------------------------
-- Generating the program effects and non-effects

-- (FIXME) Obtaining the axiomatic descriptions of each instruction in the
-- program will be automated in the near future.

-- set_option trace.gen_step.print_names true in
#genStepTheorems program namePrefix:="abs_" thmType:="fetch"
-- set_option trace.gen_step.print_names true in
#genStepTheorems program namePrefix:="abs_" thmType:="decodeExec"
-- set_option trace.gen_step.print_names true in
#genStepTheorems program namePrefix:="abs_" thmType:="step" `state_simp_rules

theorem abs_stepi_0x4005d0_axiomatic (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d0#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = stepi s) :
  r StateField.PC sn = 4195796#64 ∧
  sn.program = program ∧
  r (StateField.GPR 1#5) sn = BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s)) ∧
  ∀ (f : StateField), f ≠ StateField.PC ∧ f ≠ StateField.GPR 1#5 → r f sn = r f s := by
  rw [abs_stepi_0x4005d0 s sn h_program h_pc h_err] at h_step
  intro_change_hyps h_step h_program "h_"
  clear h_step
  simp_all only [minimal_theory]
  done

theorem abs_stepi_0x4005d4_axiomatic (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = stepi s) :
  r StateField.PC sn = 4195800#64 ∧
  sn.program = program ∧
  r (StateField.GPR 0#5) sn =
  BitVec.truncate 64
            (BitVec.replicate 32 (BitVec.extractLsb 31 31 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s)))) &&&
          BitVec.truncate 64 4294967294#32 |||
        (BitVec.truncate 64 0#32 &&& BitVec.truncate 64 0#32 |||
            BitVec.truncate 64 ((BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s)).rotateRight 31) &&&
              BitVec.truncate 64 4294967295#32) &&&
          BitVec.truncate 64 1#32 ∧
  ∀ (f : StateField), f ≠ StateField.PC ∧ f ≠ StateField.GPR 0#5 → r f sn = r f s := by
  rw [abs_stepi_0x4005d4 s sn h_program h_pc h_err] at h_step
  dsimp [reduceDecodeBitMasks] at h_step
  intro_change_hyps h_step h_program "h_"
  clear h_step
  simp_all only [minimal_theory]
  done

theorem abs_stepi_0x4005d8_axiomatic (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = stepi s) :
  r StateField.PC sn = 0x4005dc#64 ∧
  sn.program = program ∧
  r (StateField.GPR 1#5) sn =
    (BitVec.zeroExtend 64
      (AddWithCarry (BitVec.zeroExtend 32 (r (StateField.GPR 1#5) s)) (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s))
          0#1).fst) ∧
  ∀ (f : StateField), f ≠ StateField.GPR 1#5 ∧ f ≠ StateField.PC → r f sn = r f s := by
  rw [abs_stepi_0x4005d8 s sn h_program h_pc h_err] at h_step
  intro_change_hyps h_step h_program "h_"
  clear h_step
  simp_all only [minimal_theory]
  done

theorem abs_stepi_0x4005dc_axiomatic (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005dc#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = stepi s) :
  r StateField.PC sn = 0x4005e0#64 ∧
  sn.program = program ∧
  r (StateField.GPR 0#5) sn =
    (BitVec.truncate 64 (BitVec.zeroExtend 32 (r (StateField.GPR 1#5) s)) ^^^
      BitVec.truncate 64 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s))) ∧
  ∀ (f : StateField), f ≠ StateField.GPR 0#5 ∧ f ≠ StateField.PC → r f sn = r f s := by
  rw [abs_stepi_0x4005dc s sn h_program h_pc h_err] at h_step
  intro_change_hyps h_step h_program "h_"
  clear h_step
  simp_all only [minimal_theory]
  done

/-- (FIXME) This was tedious: we need to prove helper lemmas/build automation to
      generate these effects theorems, but the good news is that we see a
      pattern here to exploit. Our main workhorse here is symbolic
    simulation, but the interesting part is that we are symbolically simulating
    as well as determining the number of steps to simulate in tandem. -/
theorem program_effects_lemma (h_pre : abs_pre a)
  (h_run : af = Sys.run (Sys.next a)
                        (Correctness.csteps (Sys.next a) 0)) :
  r StateField.PC af.state = 0x4005e0#64 ∧
  af.w0 = a.w0 ∧
  r (StateField.GPR 0#5) af.state =
    BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.zeroExtend 64
          (AddWithCarry (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 a.w0))
              (BitVec.zeroExtend 32
                (BitVec.truncate 64 (BitVec.replicate 32 (BitVec.extractLsb 31 31 a.w0)) &&&
                    BitVec.truncate 64 4294967294#32 |||
                  (BitVec.truncate 64 0#32 &&& BitVec.truncate 64 0#32 |||
                      BitVec.truncate 64 (a.w0.rotateRight 31) &&& BitVec.truncate 64 4294967295#32) &&&
                    BitVec.truncate 64 1#32))
              0#1).fst)) ^^^
    BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.truncate 64 (BitVec.replicate 32 (BitVec.extractLsb 31 31 a.w0)) &&&
            BitVec.truncate 64 4294967294#32 |||
          (BitVec.truncate 64 0#32 &&& BitVec.truncate 64 0#32 |||
              BitVec.truncate 64 (a.w0.rotateRight 31) &&& BitVec.truncate 64 4294967295#32) &&&
            BitVec.truncate 64 1#32)) ∧
    r StateField.ERR af.state = StateError.None := by

  simp only [←run_succ] at h_run
  simp only [abs_pre, state_simp_rules] at h_pre
  have ⟨h_s0_x0, h_s0_pc, h_s0_program, h_s0_err⟩ := h_pre; clear h_pre

  rw [Correctness.csteps_eq] at h_run
  generalize h_step_1a : Sys.next a = a1 at h_run
  have h_a1 : a1 = Sys.run a 1 := by
    simp only [Sys.run, ←h_step_1a]
  simp only [Sys.next] at h_step_1a
  have h_a1_state : a1.state = stepi a.state := by simp only [← h_step_1a]
  have h_a1_w0 : a1.w0 = a.w0 := by simp only [← h_step_1a]
  have h1 := abs_stepi_0x4005d0_axiomatic
              a.state a1.state h_s0_program h_s0_pc h_s0_err h_a1_state
  simp only
    [Spec'.cut, abs_cut, h1,
     state_simp_rules, minimal_theory, bitvec_rules] at h_run
  have h_s1_program : a1.state.program = program := by
    simp only [h1]
  have h_s1_err : r StateField.ERR a1.state = StateError.None := by
    simp  (config := {decide := true}) only [h1, h_s0_err]
  have h_s1_pc : r StateField.PC a1.state = 0x4005d4#64 := by
    simp only [h1]

  rw [Correctness.csteps_eq] at h_run
  generalize h_step_2a : Sys.next a1 = a2 at h_run
  have h_a2 : a2 = Sys.run a 2 := by
    simp only [Sys.run, ←h_step_2a, h_a1]
  simp only [Sys.next] at h_step_2a
  have h_a2_state : a2.state = stepi a1.state := by simp only [← h_step_2a]
  have h_a2_w0 : a2.w0 = a.w0 := by simp only [← h_step_2a, h_a1_w0]
  have h2 := abs_stepi_0x4005d4_axiomatic
              a1.state a2.state h_s1_program h_s1_pc h_s1_err h_a2_state
  simp only
    [Spec'.cut, abs_cut, h2,
     state_simp_rules, minimal_theory, bitvec_rules] at h_run
  have h_s2_program : a2.state.program = program := by
    simp only [h2]
  have h_s2_err : r StateField.ERR a2.state = StateError.None := by
    simp (config := {decide := true}) only [h2, h_s1_err]
  have h_s2_pc : r StateField.PC a2.state = 0x4005d8#64 := by
    simp only [h2]

  rw [Correctness.csteps_eq] at h_run
  generalize h_step_3a : Sys.next a2 = a3 at h_run
  have h_a3 : a3 = Sys.run a 3 := by
    simp only [Sys.run, ←h_step_3a, h_a2]
  simp only [Sys.next] at h_step_3a
  have h_a3_state : a3.state = stepi a2.state := by simp only [← h_step_3a]
  have h_a3_w0 : a3.w0 = a.w0 := by simp only [← h_step_3a, h_a2_w0]
  have h3 := abs_stepi_0x4005d8_axiomatic
              a2.state a3.state h_s2_program h_s2_pc h_s2_err h_a3_state
  simp only
    [Spec'.cut, abs_cut, h3,
     state_simp_rules, minimal_theory, bitvec_rules] at h_run
  have h_s3_program : a3.state.program = program := by
    simp only [h3]
  have h_s3_err : r StateField.ERR a3.state = StateError.None := by
    simp (config := {decide := true}) only [h3, h_s2_err]
  have h_s3_pc : r StateField.PC a3.state = 0x4005dc#64 := by
    simp only [h3]

  rw [Correctness.csteps_eq] at h_run
  generalize h_step_4a : Sys.next a3 = a4 at h_run
  have h_a4 : a4 = Sys.run a 4 := by
    simp only [Sys.run, ←h_step_4a, h_a3]
  simp only [Sys.next] at h_step_4a
  have h_a4_state : a4.state = stepi a3.state := by simp only [← h_step_4a]
  have h_a4_w0 : a4.w0 = a.w0 := by simp only [← h_step_4a, h_a3_w0]
  have h4 := abs_stepi_0x4005dc_axiomatic
              a3.state a4.state h_s3_program h_s3_pc h_s3_err h_a4_state
  simp only
    [Spec'.cut, abs_cut, h4,
     state_simp_rules, minimal_theory, bitvec_rules] at h_run
  have _h_s4_program : a4.state.program = program := by
    simp only [h4]
  have h_s4_err : r StateField.ERR a4.state = StateError.None := by
    simp (config := {decide := true}) only [h4, h_s3_err]
  have h_s4_pc : r StateField.PC a4.state = 0x4005e0#64 := by
    simp only [h4]

  have h_af_a4 : af = a4 := by simp only [h_a4, h_run]

  have h_s4_gpr0 :
    r (StateField.GPR 0#5) a4.state =
      BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.zeroExtend 64
          (AddWithCarry (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 a.w0))
              (BitVec.zeroExtend 32
                (BitVec.truncate 64 (BitVec.replicate 32 (BitVec.extractLsb 31 31 a.w0)) &&&
                    BitVec.truncate 64 4294967294#32 |||
                  (BitVec.truncate 64 0#32 &&& BitVec.truncate 64 0#32 |||
                      BitVec.truncate 64 (a.w0.rotateRight 31) &&& BitVec.truncate 64 4294967295#32) &&&
                    BitVec.truncate 64 1#32))
              0#1).fst)) ^^^
    BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.truncate 64 (BitVec.replicate 32 (BitVec.extractLsb 31 31 a.w0)) &&&
            BitVec.truncate 64 4294967294#32 |||
          (BitVec.truncate 64 0#32 &&& BitVec.truncate 64 0#32 |||
              BitVec.truncate 64 (a.w0.rotateRight 31) &&& BitVec.truncate 64 4294967295#32) &&&
            BitVec.truncate 64 1#32)) := by
    simp only [← h_a4_state] at h4
    simp (config := {decide := true}) only [h4]
    simp only [← h_a3_state] at h3
    simp (config := {decide := true}) only [h3]
    simp only [← h_a2_state] at h2
    simp (config := {decide := true}) only [h2]
    simp only [← h_a1_state] at h1
    simp (config := {decide := true}) only [h1]
    simp only [h_s0_x0]
    done

  simp only [h_s4_pc, h_s4_err, h_s4_gpr0,
             h_af_a4, h_a4_w0,
             minimal_theory, bitvec_rules]
  done

-------------------------------------------------------------------------------

theorem partial_correctness :
  PartialCorrectness Abs := by
  refine Correctness.partial_correctness_from_verification_conditions
    ?v1 ?v2 ?v3 ?v4
  case v1 =>
    intro a
    simp only [Spec'.assert, abs_assert, Spec.pre, abs_pre]
    intros
    simp_all only [and_self, if_false_right, ite_true]
  case v2 =>
    intro a
    simp only [Spec.exit, Spec'.cut, abs_exit, abs_cut]
    intros
    simp_all only [or_true]
  case v3 =>
    intro a
    simp only [Spec'.assert, Spec.exit, Spec.post, abs_assert, abs_exit]
    intros
    simp_all
  case v4 =>
    intro a h_assert h_exit
    simp [Spec.exit, abs_exit] at h_exit
    simp only [Spec'.assert, abs_assert] at h_assert
    simp [h_exit] at h_assert
    clear h_exit
    simp_all only [state_simp_rules]
    simp only [Correctness.nextc]
    generalize h_run : (Sys.run (Sys.next a) (Correctness.csteps (Sys.next a) 0)) = af
    have effects := @program_effects_lemma a af h_assert.right h_run.symm
    simp only [Spec'.cut, abs_cut,
                Spec'.assert, abs_assert, abs_post,
                effects,
                state_simp_rules, bitvec_rules, minimal_theory]
    simp only [AddWithCarry, spec]
    split <;> bv_decide
    done

theorem termination :
  Termination Abs := by
  simp [Termination, Spec.pre, Spec.exit, abs_exit,
        state_simp_rules, bitvec_rules, minimal_theory]
  intro a h_pre
  have h_effects := @program_effects_lemma a
  simp only [h_pre, minimal_theory] at h_effects
  apply Exists.intro ((Correctness.csteps (Sys.next a) 0) + 1)
  simp only [run_succ, h_effects]
  done

end AbsVCG
