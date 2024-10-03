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
import Tactics.Aggregate
import Correctness.ArmSpec

namespace AbsVCGTandem

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
  let msb := BitVec.extractLsb' 31 1 x
  if msb == 0#1 then
    x
  else
    (0#32 - x)

/-- Postcondition for the correctness of the `Abs` program. -/
def abs_post (s0 sf : ArmState) : Prop :=
  read_gpr 32 0#5 sf = spec (read_gpr 32 0#5 s0) ∧
  read_pc sf = 0x4005e0#64 ∧
  read_err sf = StateError.None

/-- Function identifying the exit state(s) of the program. -/
def abs_exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = 0x4005e0#64

/-- Function identifying the cutpoints of the program. -/
def abs_cut (s : ArmState) : Bool :=
  match (read_pc s) with
  -- First instruction
  | 0x4005d0#64 => true
  -- Last instruction
  | 0x4005e0#64 => true
  | _ => false

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

theorem Abs.cassert_eq (s0 si : ArmState) (i : Nat) :
  Correctness.cassert s0 si i = if abs_cut si then (i, abs_assert s0 si)
                       else Correctness.cassert s0 (run 1 si) (i + 1) := by
  rw [Correctness.cassert_eq]
  simp only [Sys.next, Spec'.cut, Spec'.assert, run]
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
  (h_step : sn = run 1 s) :
  abs_cut sn = false ∧
  r (StateField.GPR 1#5) sn =
    (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s))) ∧
  (∀ (f : StateField), f ≠ StateField.PC → f ≠ (StateField.GPR 1#5) →
                        r f sn = r f s) ∧
  r StateField.PC sn = 0x4005d4#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005d0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005d4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  abs_cut sn = false  ∧
  r (StateField.GPR 0#5) sn =
    (BitVec.zeroExtend 64
            (BitVec.replicate 32 (BitVec.extractLsb' 31 1 (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s)))) &&&
          0xfffffffe#64 |||
        BitVec.zeroExtend 64 ((BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s)).rotateRight 31) &&& 0xffffffff#64 &&&
          0x1#64) ∧
  (∀ (f : StateField), f ≠ StateField.PC → f ≠ (StateField.GPR 0#5) →
                        r f sn = r f s) ∧
  r StateField.PC sn = 0x4005d8#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005d4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005d8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005d8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  abs_cut sn = false  ∧
  r (StateField.GPR 1#5) sn =
    (BitVec.zeroExtend 64
      (AddWithCarry (BitVec.zeroExtend 32 (r (StateField.GPR 0x1#5) s))
          (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s)) 0x0#1).fst) ∧
  (∀ (f : StateField), f ≠ StateField.PC → f ≠ (StateField.GPR 1#5) →
                        r f sn = r f s) ∧
  r StateField.PC sn = 0x4005dc#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005d8 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005dc_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005dc#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  abs_cut sn = true  ∧
  r (StateField.GPR 0#5) sn =
    (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (r (StateField.GPR 0x1#5) s)) ^^^
      BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (r (StateField.GPR 0x0#5) s))) ∧
  (∀ (f : StateField), f ≠ StateField.PC → f ≠ (StateField.GPR 0#5) →
                        r f sn = r f s) ∧
  r StateField.PC sn = 0x4005e0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005dc h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, abs_cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

-------------------------------------------------------------------------------

def rank (s : ArmState) : Nat :=
  match (read_pc s) with
  -- First instruction
  | 0x4005d0#64 => 1
  -- Last instruction
  | _ => 0

theorem correctness :
  Correctness ArmState := by
  apply Correctness.by_the_method rank
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
    simp only [Correctness.arm_run]
    simp [Spec.exit, abs_exit] at h_exit
    simp only [Spec'.assert, abs_assert, h_exit, minimal_theory] at h_assert
    obtain ⟨h_pre, h_assert_pc, h_assert_si_s0⟩ := h_assert
    have ⟨h_s0_pc, h_s0_program, h_s0_err⟩ := h_pre
    simp only [state_simp_rules] at *
    subst si
    clear h_exit

    -- Begin: Symbolic Simulation

    -- Instruction 1
    -- The first instruction is a little special because we know we will a step
    -- from the initial state: `assert` holds for the first cutpoint _after_
    -- this state.
    -- However, the same tactic pattern works for simulating each of these
    -- instructions.
    rw [Abs.cassert_eq]
    --
    -- Note: The `.fst` element of the conclusion tells us the number of steps
    -- that have been simulated _after_ the first one; add one to this number to
    -- get the total number of steps simulated from the initial state to reach
    -- the next cutpoint.
    --
    -- Introduce the next state variable `s1'` to avoid name clashes with the
    -- state variable `s1` that `sym_n` introduces.
    generalize h_s0_run : run 1 s0 = s1'
    replace h_s0_run := h_s0_run.symm
    sym_n 1 at s0
    have h_s1_cut := @program.stepi_0x4005d0_cut s0 s1
                      h_s0_program h_s0_pc h_s0_err
                      (by simp only [run, stepi_s0])
    -- Simplify the conclusion.
    simp only [h_s1_cut, Nat.reduceAdd, minimal_theory]
    clear h_s0_run h_s1_cut

    -- Instruction 2
    rw [Abs.cassert_eq]
    -- We again use `s2'` to avoid name clashes with `s2` introduces by `sym_n`.
    generalize h_s1_run : run 1 s1 = s2'
    replace h_s1_run := h_s1_run.symm
    sym_n 1 at s1
    have h_s2_cut := @program.stepi_0x4005d4_cut s1 s2
                     h_s1_program h_s1_pc h_s1_err
                     (by simp only [run, stepi_s1])
    -- Simplify the conclusion.
    simp only [h_s2_cut, Nat.reduceAdd, minimal_theory]
    clear h_s1_run h_s2_cut

    -- Instruction 3
    rw [Abs.cassert_eq]
    generalize h_s2_run : run 1 s2 = s3'
    replace h_s2_run := h_s2_run.symm
    sym_n 1 at s2
    have h_s3_cut := @program.stepi_0x4005d8_cut s2 s3
                     h_s2_program h_s2_pc h_s2_err
                     (by simp only [run, stepi_s2])

    simp only [h_s3_cut, Nat.reduceAdd, minimal_theory]
    clear h_s2_run h_s3_cut

    -- Instruction 4
    rw [Abs.cassert_eq]
    generalize h_s3_run : run 1 s3 = s4'
    replace h_s3_run := h_s3_run.symm
    sym_n 1 at s3
    have h_s4_cut := @program.stepi_0x4005dc_cut s3 s4
                      h_s3_program h_s3_pc h_s3_err
                      (by simp only [run, stepi_s3])
    -- Note: from the conclusion, we see that we simulated 3 steps from s1 (or 4
    -- steps from s0) to reach the next cutpoint. We can use this to help
    -- us come up with a clock in the termination proof.
    simp only [h_s4_cut, Nat.reduceAdd, minimal_theory]
    clear h_s3_run h_s4_cut

    simp only [abs_assert, abs_post, h_pre, minimal_theory]
    -- Aggregate program effects here to obtain the value of x0(s4).
    sym_aggregate
    -- End: Symbolic Simulation

    simp (config := {ground := true}) only [AddWithCarry, spec]
    constructor
    · -- Partial Correctness Proof
      split <;> bv_decide
    · -- Termination Proof
      apply Exists.intro 4
      simp only [Spec'.cut, abs_cut, rank,
                 state_simp_rules]
      have h_run : run 4 s0 = s4 := by
        simp only [run, stepi_s0, stepi_s1, stepi_s2, stepi_s3]
      simp only [h_run, h_s4_pc, h_s0_pc, minimal_theory]
      decide
    done

end AbsVCGTandem
