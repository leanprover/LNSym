import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.StepThms

namespace GCMGmultV8Program

#genStepTheorems gcm_gmult_v8_program thmType:="fetch" `state_simp_rules
#genStepTheorems gcm_gmult_v8_program thmType:="decodeExec" `state_simp_rules
#genStepTheorems gcm_gmult_v8_program thmType:="step" `state_simp_rules

theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    read_err sf = .None := by
  simp (config := {ground := true}) only [Option.some.injEq] at h_s0_pc h_run
  sym1_n 27
  subst h_run
  assumption
  done
