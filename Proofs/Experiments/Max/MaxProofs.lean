import Proofs.Experiments.Max.MaxProgram
import Correctness.iterate

open Iterate Classical in
noncomputable def runUntilSteps (P : ArmState → Prop) (s : ArmState) : Nat :=
  iterate (fun (s, i) => if P s then .inl i else .inr (stepi s, i + 1)) (s, 0)

noncomputable def runUntil (P : ArmState → Prop) (s : ArmState) : ArmState :=
  run (runUntilSteps P s) s

set_option trace.Tactic.sym true in
theorem correct
  {s0 sf : ArmState}
  (h_s0_pc : read_pc s0 = 0x894#64)
  (h_s0_program : s0.program = Max.program)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_s0_err : read_err s0 = StateError.None)
  (h_run : sf = run Max.program.length s0) :
  read_gpr 32 0 sf = Max.spec (read_gpr 32 0 s0) (read_gpr 32 1 s0) ∧
  read_err sf = StateError.None := by
  -- simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 6
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

#eval (2220#64).toHex

/-- info: 'Max.correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correct
