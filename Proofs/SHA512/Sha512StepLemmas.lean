import Proofs.SHA512.Sha512FetchLemmas
import Proofs.SHA512.Sha512DecodeExecLemmas
import Proofs.SHA512.Sha512Program
-- import Tests.SHA2.SHA512ProgramTest

-- set_option trace.gen_step.debug.heartBeats true in
set_option trace.gen_step.print_names true in
set_option maxHeartbeats 2000000 in
#genStepTheorems sha512_program namePrefix:="sha512_" thmType:="step" `state_simp_rules

#check sha512_stepi_0x1264e8
