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
import Lean

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
  read_err s = StateError.None

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
  read_err sf = StateError.None

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
                           else Correctness.csteps (stepi s) (i + 1) := by
  rw [Correctness.csteps_eq]
  simp only [Sys.next, Spec'.cut]
  done

-------------------------------------------------------------------------------
-- Generating the program effects and non-effects

-- set_option trace.gen_step.print_names true in
#genStepTheorems program thmType:="fetch"
-- set_option trace.gen_step.print_names true in
#genStepTheorems program thmType:="decodeExec"
-- set_option trace.gen_step.print_names true in
#genStepTheorems program thmType:="step" `state_simp_rules

-- (FIXME) Obtain *_cut theorems for each instruction automatically.

theorem abs_stepi_0x4005d0_cut (s : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  abs_cut (stepi s) = false := by
  have := program.stepi_0x4005d0 s (stepi s) h_program h_pc h_err
  simp only [minimal_theory] at this
  simp only [abs_cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem abs_stepi_0x4005d4_cut (s : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d4#64)
  (h_err : r StateField.ERR s = StateError.None) :
  abs_cut (stepi s) = false := by
  have := program.stepi_0x4005d4 s (stepi s) h_program h_pc h_err
  simp only [minimal_theory] at this
  simp only [abs_cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem abs_stepi_0x4005d8_cut (s : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d8#64)
  (h_err : r StateField.ERR s = StateError.None) :
  abs_cut (stepi s) = false := by
  have := program.stepi_0x4005d8 s (stepi s) h_program h_pc h_err
  simp only [minimal_theory] at this
  simp only [abs_cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem abs_stepi_0x4005dc_cut (s : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005dc#64)
  (h_err : r StateField.ERR s = StateError.None) :
  abs_cut (stepi s) = true := by
  have := program.stepi_0x4005dc s (stepi s) h_program h_pc h_err
  simp only [minimal_theory] at this
  simp only [abs_cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

/--
(FIXME) This was tedious: we need to prove helper lemmas/build automation to
generate these effects theorems, but the good news is that we see a
pattern here to exploit. Our main workhorse here is symbolic
simulation, but the interesting part is that we are symbolically simulating
as well as determining the number of steps to simulate in tandem.
-/
theorem program_effects_lemma (h_pre : abs_pre s0)
  (h_run : sf = run (Correctness.csteps (stepi s0) 0) (stepi s0)) :
  r (StateField.GPR 0#5) sf = BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.zeroExtend 64
          (AddWithCarry (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0))))
              (BitVec.zeroExtend 32
                (BitVec.truncate 64
                      (BitVec.replicate 32
                        (BitVec.extractLsb 31 31 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)))) &&&
                    BitVec.truncate 64 (~~~1#32) |||
                  (BitVec.truncate 64 (BitVec.zero 32) &&& BitVec.truncate 64 (~~~4294967295#32) |||
                      BitVec.truncate 64 ((BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)).rotateRight 31) &&&
                        BitVec.truncate 64 4294967295#32) &&&
                    BitVec.truncate 64 1#32))
              0#1).fst)) ^^^
    BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.truncate 64
              (BitVec.replicate 32 (BitVec.extractLsb 31 31 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)))) &&&
            BitVec.truncate 64 (~~~1#32) |||
          (BitVec.truncate 64 (BitVec.zero 32) &&& BitVec.truncate 64 (~~~4294967295#32) |||
              BitVec.truncate 64 ((BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)).rotateRight 31) &&&
                BitVec.truncate 64 4294967295#32) &&&
            BitVec.truncate 64 1#32)) ∧
  r StateField.PC sf = 0x4005e0#64 ∧
  r StateField.ERR sf = StateError.None := by

  simp only [abs_pre, state_simp_rules] at h_pre
  have ⟨h_s0_pc, h_s0_program, h_s0_err⟩ := h_pre; clear h_pre

  -- Instruction 1
  rw [Abs.csteps_eq, abs_stepi_0x4005d0_cut s0 h_s0_program h_s0_pc h_s0_err] at h_run
  simp only [minimal_theory, Nat.reduceAdd] at h_run
  generalize h_step_1 : stepi s0 = s1 at h_run
  have h_s1 : s1 = run 1 s0 := by
    simp only [run, h_step_1]
  replace h_step_1 : s1 = stepi s0 := h_step_1.symm
  rw [program.stepi_0x4005d0 s0 s1 h_s0_program h_s0_pc h_s0_err] at h_step_1
  have h_s1_program : s1.program = program := by
    simp only [h_step_1, h_s0_program,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s1_err : r StateField.ERR s1 = StateError.None := by
    simp only [h_step_1, h_s0_err,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s1_pc : r StateField.PC s1 = 0x4005d4#64 := by
    simp only [h_step_1, h_s0_pc,
               state_simp_rules, minimal_theory, bitvec_rules]

  -- Instruction 2
  rw [Abs.csteps_eq, abs_stepi_0x4005d4_cut s1 h_s1_program h_s1_pc h_s1_err] at h_run
  simp only [minimal_theory, Nat.reduceAdd] at h_run
  generalize h_step_2 : stepi s1 = s2 at h_run
  have h_s2 : s2 = run 1 s1 := by
    simp only [run, h_step_2]
  replace h_step_2 : s2 = stepi s1 := h_step_2.symm
  rw [program.stepi_0x4005d4 s1 s2 h_s1_program h_s1_pc h_s1_err] at h_step_2
  -- (FIXME) abs_stepi_0x4005d4 should have reduced `decode_bit_masks`.
  simp only [reduceDecodeBitMasks] at h_step_2
  have h_s2_program : s2.program = program := by
    simp only [h_step_2, h_s1_program,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s2_err : r StateField.ERR s2 = StateError.None := by
    simp only [h_step_2, h_s1_err,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s2_pc : r StateField.PC s2 = 0x4005d8#64 := by
    simp only [h_step_2, h_s1_pc,
               state_simp_rules, minimal_theory, bitvec_rules]

  -- Instruction 3
  rw [Abs.csteps_eq, abs_stepi_0x4005d8_cut s2 h_s2_program h_s2_pc h_s2_err] at h_run
  simp only [minimal_theory, Nat.reduceAdd] at h_run
  generalize h_step_3 : stepi s2 = s3 at h_run
  have h_s3 : s3 = run 1 s2 := by
    simp only [run, h_step_3]
  replace h_step_3 : s3 = stepi s2 := h_step_3.symm
  rw [program.stepi_0x4005d8 s2 s3 h_s2_program h_s2_pc h_s2_err] at h_step_3
  have h_s3_program : s3.program = program := by
    simp only [h_step_3, h_s2_program,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s3_err : r StateField.ERR s3 = StateError.None := by
    simp only [h_step_3, h_s2_err,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s3_pc : r StateField.PC s3 = 0x4005dc#64 := by
    simp only [h_step_3, h_s2_pc,
               state_simp_rules, minimal_theory, bitvec_rules]

  -- Instruction 4
  rw [Abs.csteps_eq, abs_stepi_0x4005dc_cut s3 h_s3_program h_s3_pc h_s3_err] at h_run
  simp only [minimal_theory, Nat.reduceAdd] at h_run
  generalize h_step_4 : stepi s3 = s4 at h_run
  have h_s4 : s4 = run 1 s3 := by
    simp only [run, h_step_4]
  replace h_step_4 : s4 = stepi s3 := h_step_4.symm
  rw [program.stepi_0x4005dc s3 s4 h_s3_program h_s3_pc h_s3_err] at h_step_4
  have _h_s4_program : s4.program = program := by
    simp only [h_step_4, h_s3_program,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s4_err : r StateField.ERR s4 = StateError.None := by
    simp only [h_step_4, h_s3_err,
               state_simp_rules, minimal_theory, bitvec_rules]
  have h_s4_pc : r StateField.PC s4 = 0x4005e0#64 := by
    simp only [h_step_4, h_s3_pc,
               state_simp_rules, minimal_theory, bitvec_rules]

  have h_s4_gpr0 : r (StateField.GPR 0#5) s4 =
    BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.zeroExtend 64
          (AddWithCarry (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0))))
              (BitVec.zeroExtend 32
                (BitVec.truncate 64
                      (BitVec.replicate 32
                        (BitVec.extractLsb 31 31 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)))) &&&
                    BitVec.truncate 64 (~~~1#32) |||
                  (BitVec.truncate 64 (BitVec.zero 32) &&& BitVec.truncate 64 (~~~4294967295#32) |||
                      BitVec.truncate 64 ((BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)).rotateRight 31) &&&
                        BitVec.truncate 64 4294967295#32) &&&
                    BitVec.truncate 64 1#32))
              0#1).fst)) ^^^
    BitVec.truncate 64
      (BitVec.zeroExtend 32
        (BitVec.truncate 64
              (BitVec.replicate 32 (BitVec.extractLsb 31 31 (BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)))) &&&
            BitVec.truncate 64 (~~~1#32) |||
          (BitVec.truncate 64 (BitVec.zero 32) &&& BitVec.truncate 64 (~~~4294967295#32) |||
              BitVec.truncate 64 ((BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s0)).rotateRight 31) &&&
                BitVec.truncate 64 4294967295#32) &&&
            BitVec.truncate 64 1#32)) := by
    simp (config := {decide := true}) only [h_step_4, h_step_3, h_step_2, h_step_1,
                                            state_simp_rules]

  have h_sf_s4 : sf = s4 := by
    simp only [h_run, h_s4, h_s3, h_s2, h_s1, run]

  simp only [h_sf_s4, h_s4_gpr0, h_s4_pc, h_s4_err, minimal_theory]
  done

-------------------------------------------------------------------------------

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
    generalize h_run : (run (Correctness.csteps (stepi s0) 0) (stepi s0)) = sf
    have effects := @program_effects_lemma s0 sf h_assert1 h_run.symm
    simp only [Sys.next, Spec'.assert, abs_assert, h_assert1,
               Correctness.nextc, Correctness.arm_run,
               h_run, effects, Spec'.cut, abs_cut,
               Spec'.assert, abs_assert, abs_post,
               AddWithCarry, spec,
               state_simp_rules, bitvec_rules, minimal_theory]
    split <;> bv_decide
    done

theorem termination :
  Termination ArmState := by
  simp [Termination, Spec.pre, Spec.exit, abs_exit,
        state_simp_rules, bitvec_rules, minimal_theory]
  intro s h_pre
  have h_effects := @program_effects_lemma s
  simp only [h_pre, minimal_theory] at h_effects
  apply Exists.intro ((Correctness.csteps (Sys.next s) 0) + 1)
  simp only [Correctness.arm_run, Sys.next, run_succ, h_effects]
  done

end AbsVCG
