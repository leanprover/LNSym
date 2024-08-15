import Proofs.SHA512.Sha512FetchLemmas
import Proofs.SHA512.Sha512DecodeExecLemmas
import Proofs.SHA512.Sha512Program
-- import Tests.SHA2.SHA512ProgramTest

-- set_option trace.gen_step.debug.heartBeats true in
-- set_option trace.gen_step.print_names true in
set_option maxHeartbeats 2000000 in
#genStepTheorems sha512_program thmType:="step" `state_simp_rules

/--
info: sha512_program.stepi_0x126c90 (s sn : ArmState) (h_program : s.program = sha512_program)
  (h_pc : r StateField.PC s = 1207440#64) (h_err : r StateField.ERR s = StateError.None) :
  (sn = stepi s) = (sn = w StateField.PC (if ¬r (StateField.GPR 2#5) s = 0#64 then 1205504#64 else 1207444#64) s)
-/
#guard_msgs in
#check sha512_program.stepi_0x126c90
