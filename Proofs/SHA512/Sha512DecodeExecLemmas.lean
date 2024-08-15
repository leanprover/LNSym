import Tactics.StepThms
import Proofs.SHA512.Sha512Program
-- import Tests.SHA2.SHA512ProgramTest

-- set_option trace.gen_step.debug.heartBeats true in
-- set_option trace.gen_step.print_names true in
set_option maxHeartbeats 1002500 in
#genStepTheorems sha512_program thmType:="decodeExec"

/--
info: sha512_program.decode_0x1264e8 :
  decode_raw_inst 1310722675#32 =
    some
      (ArmInst.DPSFP
        (DataProcSFPInst.Advanced_simd_two_reg_misc
          { _fixed1 := 0#1, Q := 1#1, U := 0#1, _fixed2 := 14#5, size := 0#2, _fixed3 := 16#5, opcode := 0#5,
            _fixed4 := 2#2, Rn := 19#5, Rd := 19#5 }))
-/
#guard_msgs in
#check sha512_program.decode_0x1264e8

/--
info: sha512_program.exec_0x126c90 (s : ArmState) :
  exec_inst
      (ArmInst.BR (BranchInst.Compare_branch { sf := 1#1, _fixed := 26#5, op := 1#1, imm19 := 523804#19, Rt := 2#5 }))
      s =
    w StateField.PC
      (if decide (r (StateField.GPR 2#5) s = BitVec.zero 64) = false then r StateField.PC s + 18446744073709549680#64
      else r StateField.PC s + 4#64)
      s
-/
#guard_msgs in
#check sha512_program.exec_0x126c90
