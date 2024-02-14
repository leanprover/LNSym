/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.State
import Tactics.Sym
import Tests.SHA512ProgramTest

section SHA512_proof

open Std.BitVec

/-
The `sym1` tactic, defined in ../Tactics/Sym.lean, attempts to
symbolically simulate a single instruction -- it is pretty
straightforward right now and we expect it to radically change in the
near future.

It unfolds the `run` function once, then
unfolds the `stepi` function, reduces
`fetch_inst <address> <state>`
to a term like:
`Std.RBMap.find?  <program> <address>`
where `<program>` and `<address>` are expected to be concrete.
We hope that `simp` is able to "evaluate" such ground terms during
proof so that the above gives us instruction <i> located at
`<address>` in `<program>`. Moreover, we also hope that `simp`
evaluates `decode_raw_inst <i>` to produce a concrete
`<decoded_inst>` and return an `exec_inst <decoded_inst> <state>`
term.

`sym1` then applies some lemmas in its simpset, and finally we
capture the behavior of the instruction in terms of writes made to
the machine state (denoted by function `w`).
-/

----------------------------------------------------------------------

-- Test 1: We have a 4 instruction program, and we attempt to simulate
-- all of them.

def sha512_program_test_1 : program :=
  def_program
   #[(0x126538#64 , 0xcec08230#32),      --  sha512su0       v16.2d, v17.2d
     (0x12653c#64 , 0x6e154287#32),      --  ext     v7.16b, v20.16b, v21.16b, #8
     (0x126540#64 , 0xce6680a3#32),      --  sha512h q3, q5, v6.2d
     (0x126544#64 , 0xce678af0#32)       --  sha512su1       v16.2d, v23.2d, v7.2d
     ]

-- set_option profiler true in
theorem sha512_program_test_1_sym (s : ArmState)
  (h_pc : read_pc s = 0x126538#64)
  (h_program : s.program = sha512_program_test_1.find?)
  (h_s_ok : read_err s = StateError.None)
  (h_s' : s' = run 4 s) :
  read_err s' = StateError.None := by
  iterate 4 (sym1 [h_program])
  done

----------------------------------------------------------------------

-- Test 2: We have a 5 instruction program, and we attempt to simulate
-- only 4 of them.

def sha512_program_test_2 : program :=
  def_program
   #[(0x126538#64 , 0xcec08230#32),      --  sha512su0       v16.2d, v17.2d
     (0x12653c#64 , 0x6e154287#32),      --  ext     v7.16b, v20.16b, v21.16b, #8
     (0x126540#64 , 0xce6680a3#32),      --  sha512h q3, q5, v6.2d
     (0x126544#64 , 0xce678af0#32),      --  sha512su1       v16.2d, v23.2d, v7.2d
     (0x126548#64 , 0x4ee38424#32),      --  add     v4.2d, v1.2d, v3.2d
     (0x12654c#64 , 0xce608423#32)       --  sha512h2        q3, q1, v0
     ]

-- set_option profiler true in
theorem sha512_program_test_2_sym (s : ArmState)
  (h_pc : read_pc s = 0x126538#64)
  (h_program : s.program = sha512_program_test_2.find?)
  (h_s_ok : read_err s = StateError.None)
  (h_s' : s' = run 4 s) :
  read_err s' = StateError.None := by
  iterate 4 (sym1 [h_program])

----------------------------------------------------------------------

-- Test 3:

def sha512_program_test_3 : program :=
  def_program
  #[(0x1264c0#64 , 0xa9bf7bfd#32),      --  stp     x29, x30, [sp, #-16]!
    (0x1264c4#64 , 0x910003fd#32),      --  mov     x29, sp
    (0x1264c8#64 , 0x4cdf2030#32),      --  ld1     {v16.16b-v19.16b}, [x1], #64
    (0x1264cc#64 , 0x4cdf2034#32)       --  ld1     {v20.16b-v23.16b}, [x1], #64
  ]

theorem sha512_block_armv8_test_3_sym (s0 s_final : ArmState)
  (h_s0_ok : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0 = true)
  (h_s0_pc : read_pc s0 = 0x1264c0#64)
  (h_s0_program : s0.program = sha512_program_test_3.find?)
  (h_run : s_final = run 4 s0) :
  read_err s_final = StateError.None := by

  unfold read_pc at h_s0_pc

  -- Unroll one step from 'run (n+1)'
  init_next_step h_run
  rename_i s1 h_step h_run
  -- Simulate one instruction
  fetch_and_decode_inst h_step h_s0_ok h_s0_pc h_s0_program
  exec_inst h_step h_s0_sp_aligned s1

  -- Update invariants
  update_invariants s1 sha512_program_test_3
                    h_s1_ok h_s0_pc h_s1_pc
                    h_s0_sp_aligned h_s1_sp_aligned
                    h_s1_program h_step 1205444#64
  clear h_s0_ok h_s0_sp_aligned h_s0_pc h_step h_s0_program

  init_next_step h_run
  rename_i s2 h_step h_run
  -- Simulate one instruction
  fetch_and_decode_inst h_step h_s1_ok h_s1_pc h_s1_program
  exec_inst h_step h_s1_sp_aligned s2
  -- Update invariants
  update_invariants s2 sha512_program_test_3
                    h_s2_ok h_s1_pc h_s2_pc
                    h_s1_sp_aligned h_s2_sp_aligned
                    h_s2_program h_step 1205448#64
  clear h_s1_ok h_s1_sp_aligned h_s1_pc h_step h_s1_program

  init_next_step h_run
  rename_i s3 h_step h_run
  -- Simulate one instruction
  fetch_and_decode_inst h_step h_s2_ok h_s2_pc h_s2_program
  exec_inst h_step h_s2_sp_aligned s3
  -- Update invariants
  update_invariants s3 sha512_program_test_3
                    h_s3_ok h_s2_pc h_s3_pc
                    h_s2_sp_aligned h_s3_sp_aligned
                    h_s3_program h_step 1205452#64
  clear h_s2_ok h_s2_sp_aligned h_s2_pc h_step h_s2_program

  init_next_step h_run
  rename_i s4 h_step h_run
  -- Simulate one instruction
  fetch_and_decode_inst h_step h_s3_ok h_s3_pc h_s3_program
  exec_inst h_step h_s3_sp_aligned s4
  -- Update invariants
  update_invariants s4 sha512_program_test_3
                    h_s4_ok h_s3_pc h_s4_pc
                    h_s3_sp_aligned h_s4_sp_aligned
                    h_s4_program h_step 1205456#64
  clear h_s3_ok h_s3_sp_aligned h_s3_pc h_step h_s3_program

  rw [h_run,h_s4_ok]


----------------------------------------------------------------------

-- Test 4: sha512_block_armv8_test_4_sym --- this is a symbolic
-- simulation test for the AWS-LC production SHA512 code (the program
-- we'd like to verify).

-- set_option profiler true in
theorem sha512_block_armv8_test_4_sym (s : ArmState)
  (h_s_ok : read_err s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s = true)
  (h_pc : read_pc s = 0x1264c0#64)
  (h_program : s.program = sha512_program_map.find?)
  (h_s' : s' = run 32 s) :
  read_err s' = StateError.None := by
  sorry

end SHA512_proof
