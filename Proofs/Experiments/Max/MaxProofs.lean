import Proofs.Experiments.Max.MaxProgram



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
  sym_n 1
  sym_n 1
  simp [h_s1_sp_aligned] at h_step_2
  sym_n 1
  simp [h_s2_sp_aligned] at h_step_3
  sym_n 1
  simp [h_s3_sp_aligned] at h_step_4
  sym_n 1
  simp [h_s4_sp_aligned] at h_step_5
  sym_n 1
  simp [h_s5_sp_aligned] at h_step_6
  by_cases hflag : r (StateField.FLAG PFlag.Z) s6 = 0#1
  · -- TODO: how do I proceed here?
    sorry
  · -- TODO: how do I proceed here?
    sorry

/-- info: 'Max.correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correct
