import Tactics.DecodeThms
import Tests.SHA2.SHA512ProgramTest

-- set_option trace.gen_decode.debug.heartBeats true in
-- set_option trace.gen_decode.print_names true in
set_option maxHeartbeats 1000000 in
#genDecodeTheorems sha512_program_map namePrefix:="sha512_" simpExt:=`state_simp_rules

-- #check sha512_fetch_0x1264e8
-- #check sha512_decode_0x1264e8
-- #check sha512_fetch_0x126c9c
-- #check sha512_decode_0x126c9c
