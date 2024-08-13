import Tactics.StepThms
import Proofs.SHA512.Sha512Program
-- import Tests.SHA2.SHA512ProgramTest

-- set_option trace.gen_step.debug.heartBeats true in
-- set_option trace.gen_step.print_names true in
set_option maxHeartbeats 1000000 in
#genStepTheorems sha512_program thmType:="fetch"

/--
info: sha512_program.fetch_0x1264e8 (s : ArmState) (h : s.program = sha512_program) :
  fetch_inst (1205480#64) s = some 1310722675#32
-/
#guard_msgs in
#check sha512_program.fetch_0x1264e8
