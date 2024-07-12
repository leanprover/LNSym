import Tactics.StepThms
import Proofs.SHA512.Sha512Program
-- import Tests.SHA2.SHA512ProgramTest

-- set_option trace.gen_step.debug.heartBeats true in
set_option trace.gen_step.print_names true in
set_option maxHeartbeats 1000000 in
#genStepTheorems sha512_program namePrefix:="sha512_" thmType:="fetch" simpExt:=`state_simp_rules

#check sha512_fetch_0x1264e8
