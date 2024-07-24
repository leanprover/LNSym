import Tactics.StepThms
import Proofs.SHA512.Sha512Program
-- import Tests.SHA2.SHA512ProgramTest

-- set_option trace.gen_step.debug.heartBeats true in
set_option trace.gen_step.print_names true in
set_option maxHeartbeats 1000000 in
#genStepTheorems sha512_program namePrefix:="sha512_" thmType:="decodeExec"

#check sha512_decode_0x1264e8
#check sha512_exec_0x1264e8
