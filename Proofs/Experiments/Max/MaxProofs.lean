import Proofs.Experiments.Max.MaxProgram
import Correctness.Correctness
import Correctness.ArmSpec

open Iterate Classical in
noncomputable def runUntilSteps (P : ArmState → Prop) (s : ArmState) : Nat :=
  iterate (fun (s, i) => if P s then .inl i else .inr (stepi s, i + 1)) (s, 0)

noncomputable def runUntil (P : ArmState → Prop) (s : ArmState) : ArmState :=
  run (runUntilSteps P s) s

-- Adapted from `Proofs/Experiments/AbsVCG.lean`

/-- Precondition for the correctness of the `Abs` program. -/
def abs_pre (s : ArmState) : Prop :=
  read_pc s = Max.program.min ∧
  s.program = Max.program ∧
  read_err s = StateError.None ∧
  -- (FIXME) We don't really need the stack poißnter to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment s

/-- Specification of the absolute value computation for a 32-bit bitvector. -/
def spec (x y : BitVec 32) : BitVec 32 :=
  if x < y then y else x

/-- Postcondition for the correctness of the `Abs` program. -/
def abs_post (s0 sf : ArmState) : Prop :=
  -- TODO: actually involve the max spec here
  -- read_gpr 32 0#5 sf = spec (read_gpr 32 0#5 s0) ∧
  read_pc sf = Max.program.max ∧
  read_err sf = StateError.None ∧
  CheckSPAlignment sf

/-- Function identifying the exit state(s) of the program. -/
def abs_exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = Max.program.max

/-- Function identifying the cutpoints of the program. -/
def abs_cut (s : ArmState) : Bool :=
  read_pc s = Max.program.min -- First instruction
  ||
  read_pc s = Max.program.max -- Last instruction

/-- Function that attaches assertions at the cutpoints of this program. -/
def abs_assert (s0 si : ArmState) : Prop :=
  abs_pre s0 ∧
  if read_pc si = Max.program.max then
    abs_post s0 si
  else
    False

instance : Spec' ArmState where
  pre    := abs_pre
  post   := abs_post
  exit   := abs_exit
  cut    := abs_cut
  assert := abs_assert

-- TODO(@alexkeizer): change `Program.max` to `Program.maxAddr`

theorem correct' : ∃ (n : Nat),
  {s0 sf : ArmState} →
  (h_s0_pc : read_pc s0 = 0x894#64)  →
  (h_s0_program : s0.program = Max.program)  →
  (h_s0_sp_aligned : CheckSPAlignment s0)  →
  (h_s0_err : read_err s0 = StateError.None)  →
  (h_run : sf = run n s0) →
  read_gpr 32 0 sf = Max.spec (read_gpr 32 0 s0) (read_gpr 32 1 s0) ∧
  read_err sf = StateError.None := by
  apply Exists.intro ?n
  intros s0 sf h_s0_pc h_s0_program h_s0_sp_aligned h_s0_err h_run

  have : ?n = (?m : Nat) + 1 := ?h; simp [this] at h_run
  sym_n (while := skip) 1 at s0
  sorry

set_option trace.Tactic.sym true in
theorem correct
  {s0 sf : ArmState}
  (h_s0_pc : read_pc s0 = 0x894#64)
  (h_s0_program : s0.program = Max.program)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_s0_err : read_err s0 = StateError.None)
  (h_run : sf = Correctness.nextc (stepi s0)) :
  read_gpr 32 0 sf = Max.spec (read_gpr 32 0 s0) (read_gpr 32 1 s0) ∧
  read_err sf = StateError.None := by

  generalize h_run1 : stepi s0 = sf1 at *
  replace h_run1 : _ = run 1 _ := h_run1.symm
  sym_n 1 at s0
  subst sf1
  -- clear stepi_s0

  simp [Correctness.nextc, Correctness.arm_run,
    show run 0 s1 = s1 from rfl] at h_run

  let sf' := run 6 s1
  have h_run' : sf' = run 6 s1 := rfl

  -- generalize h_run_sf' : run (Correctness.csteps s1 0) s1 = sf'
  -- replace h_run_sf' : _ = run _ _ := h_run_sf'.symm

  sym_n 5
  · sorry
  · simp [Correctness.csteps]

  stop

  -- sym_n 2
  -- by_cases hflag : r (StateField.FLAG PFlag.Z) s6 = 0#1
  · init_next_step h_run stepi_s7 s7
    have h_step_7 :=  Eq.trans (Eq.symm stepi_s7) (Max.program.stepi_eq_0x8ac h_s6_program h_s6_pc h_s6_err)
    clear stepi_s7
    split at h_step_7
    case isTrue h =>
      intro_fetch_decode_lemmas h_step_7 h_s6_program "h_s6"
      -- sym_n 5
      sym_n 5
      sorry
    case isFalse h =>
      intro_fetch_decode_lemmas h_step_7 h_s6_program "h_s6"
      sym_n 3
      init_next_step h_run stepi_s11 s11
      sorry
  · sorry
  · sorry

#eval (2220#64).toHex

/-- info: 'Max.correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correct
