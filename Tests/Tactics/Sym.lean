/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Proofs.«AES-GCM».GCMGmultV8Sym

set_option Tactic.sym.debug true

namespace GCMGmultV8Program

-- Test the behaviour of `sym_n` when `h_err` and `h_sp` are not present
/-- warning: declaration uses 'sorry' -/ -- `guard_msgs` silences the warning
#guard_msgs in example (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    read_err sf = .None := by
  simp (config := {ground := true}) only [Option.some.injEq] at h_s0_pc h_run
  sym_n 1
  · sorry
  · exact (sorry : read_err s0 = .None)
  done


namespace SimpleMemory

def program := def_program [
    (0x4005b8#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
  ]

#genStepEqTheorems program

example
    (sf s0 : ArmState)
    (h_program : s0.program = program)
    (h_run : sf = run 1 s0)
    (h_err : read_err s0 = .None)
    (h_pc : read_pc s0 = 0x4005b8#64)
    (h_sp : CheckSPAlignment s0)
    (h_s0_x0 : r (.GPR 0#5) s0 = x)
    (h_s0_x31 : r (.GPR 31#5) s0 = y) :
    read_mem_bytes 4 (y + 12#64) s0 = (x.zeroExtend 32) := by
  sym_n 1
  sorry

end SimpleMemory
