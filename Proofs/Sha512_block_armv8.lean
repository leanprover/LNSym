/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Tactics.Sym
import Tests.SHA512ProgramTest

section SHA512_proof

open Std.BitVec

----------------------------------------------------------------------

-- Symbolic Simulation Test 1:

-- In theorems sha512_program_snippet1_sym and
-- sha512_program_snippet2_sym below, we attempt to symbolically
-- simulate programs sha512_program_snippet1 and
-- sha512_program_snippet2 (respectively). Note that the first four
-- instructions in sha512_program_snippet2 are identical to
-- sha512_program_snippet1.

-- The `sym1` tactic, defined in ../Tactics/Sym.lean, attempts to
-- symbolically simulate a single instruction -- it is pretty
-- straightforward right now. It unfolds the `run` function once, then
-- unfolds the `stepi` function, reduces
-- `fetch_inst <address> <state>`
-- to a term like:
-- `Std.RBMap.find?  <program> <address>`
-- where `<program>` and `<address>` are expected to be concrete.
-- We hope that `simp` is able to "evaluate" such ground terms during
-- proof so that the above gives us instruction <i> located at
-- `<address>` in `<program>`. Moreover, we also hope that `simp`
-- evaluates `decode_raw_inst <i>` to produce a concrete
-- `<decoded_inst>` and return an `exec_inst <decoded_inst> <state>`
-- term.
--
-- `sym1` then applies some lemmas in its simpset, and finally we
-- capture the behavior of the instruction in terms of writes made to
-- the machine state (denoted by function `w`).

-- However, sha512_program_snippet1_sym is proved by following this
-- strategy, but sha512_program_snippet2_sym times out because `simp
-- ground` times out.

def sha512_program_snippet1 : program :=
  def_program
   #[(0x126538#64 , 0xcec08230#32),      --  sha512su0       v16.2d, v17.2d
     (0x12653c#64 , 0x6e154287#32),      --  ext     v7.16b, v20.16b, v21.16b, #8
     (0x126540#64 , 0xce6680a3#32),      --  sha512h q3, q5, v6.2d
     (0x126544#64 , 0xce678af0#32)       --  sha512su1       v16.2d, v23.2d, v7.2d
     ]

-- WORKING
-- set_option profiler true in
theorem sha512_program_snippet1_sym (s : ArmState)
  (h_pc : read_pc s = 0x126538#64)
  (h_program : s.program = sha512_program_snippet1.find?)
  (h_s_ok : read_err s = StateError.None)
  (h_s' : s' = run 4 s) :
  read_err s' = StateError.None := by
  iterate 4 (sym1 [h_program])
  done

def sha512_program_snippet2 : program :=
  def_program
   #[(0x126538#64 , 0xcec08230#32),      --  sha512su0       v16.2d, v17.2d
     (0x12653c#64 , 0x6e154287#32),      --  ext     v7.16b, v20.16b, v21.16b, #8
     (0x126540#64 , 0xce6680a3#32),      --  sha512h q3, q5, v6.2d
     (0x126544#64 , 0xce678af0#32),      --  sha512su1       v16.2d, v23.2d, v7.2d
     (0x126548#64 , 0x4ee38424#32),      --  add     v4.2d, v1.2d, v3.2d
     (0x12654c#64 , 0xce608423#32)       --  sha512h2        q3, q1, v0
     ]

-- TIMES OUT: (deterministic) timeout at 'simp' when `sym1
-- [h_program]` is uncommented.
-- set_option profiler true in
theorem sha512_program_snippet2_sym (s : ArmState)
  (h_pc : read_pc s = 0x126538#64)
  (h_program : s.program = sha512_program_snippet2.find?)
  (h_s_ok : read_err s = StateError.None)
  (h_s' : s' = run 4 s) :
  read_err s' = StateError.None := by
  -- sym1 [h_program]
  sorry

----------------------------------------------------------------------

-- Symbolic Simulation Test 2: sha512_block_armv8_one_iteration ---
-- this is the same symbolic simulation test for a longer program. I
-- leave it here as a test to stress-test `simp`.

-- @[simp]
-- theorem fetch_inst_at_0x1264c0
--   (h_program : s.program = sha512_program_map.find?) :
--   fetch_inst 0x1264c0#64 s = 0xa9bf7bfd#32 := by
--   rw [fetch_inst_from_rbmap_program h_program]
--   native_decide
-- @[simp]
-- theorem fetch_inst_at_0x1264c4
--   (h_program : s.program = sha512_program_map.find?) :
--   fetch_inst 0x1264c4#64 s = 0x910003fd#32 := by
--   rw [fetch_inst_from_rbmap_program h_program]
--   native_decide
-- @[simp]
-- theorem fetch_inst_at_0x1264c8
--   (h_program : s.program = sha512_program_map.find?) :
--   fetch_inst 0x1264c8#64 s = 0x4cdf2030#32 := by
--   rw [fetch_inst_from_rbmap_program h_program]
--   native_decide
-- @[simp]
-- theorem fetch_inst_at_0x1264cc
--   (h_program : s.program = sha512_program_map.find?) :
--   fetch_inst 0x1264cc#64 s = 0x4cdf2034#32 := by
--   rw [fetch_inst_from_rbmap_program h_program]
--   native_decide
-- @[simp]
-- theorem fetch_inst_at_0x1264d0
--   (h_program : s.program = sha512_program_map.find?) :
--   fetch_inst 0x1264d0#64 s = 0x4c402c00#32 := by
--   rw [fetch_inst_from_rbmap_program h_program]
--   native_decide
-- @[simp]
-- theorem fetch_inst_at_0x1264d4
--   (h_program : s.program = sha512_program_map.find?) :
--   fetch_inst 0x1264d4#64 s = 0xd0000463#32 := by
--   rw [fetch_inst_from_rbmap_program h_program]
--   native_decide

-- set_option profiler true in
theorem sha512_block_armv8_one_iteration (s : ArmState)
  (h_s_ok : read_err s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s = true)
  (h_pc : read_pc s = 0x1264c0#64)
  (h_program : s.program = sha512_program_map.find?)
  (h_s' : s' = run 32 s) :
  read_err s' = StateError.None := by
  -- sym1 [h_program];
    -- sym1 [h_program];
    -- save;
    -- -- sym1 [h_program];
    -- (try simp_all); unfold run; simp_all [stepi];
    -- (try rw [fetch_inst_from_rbmap_program $h_program]);
    -- conv =>
    --   pattern fetch_inst _ _
    --   simp (config := { ground := true }) only
    --   -- tactic => simp_all! [fetch_inst_at_0x1264c4, -run]
    --   apply fetch_inst_at_0x1264c4 h_program
    -- simp (config := { ground := true }) only;
    -- simp [exec_inst];
    -- try (simp (config := { ground := true }) only);
    -- (try simp_all);
    sorry

def sha512_program_snippet3 : program :=
  def_program
  #[(0x1264c0#64 , 0xa9bf7bfd#32),      --  stp     x29, x30, [sp, #-16]!
    (0x1264c4#64 , 0x910003fd#32),      --  mov     x29, sp
    (0x1264c8#64 , 0x4cdf2030#32),      --  ld1     {v16.16b-v19.16b}, [x1], #64
    (0x1264cc#64 , 0x4cdf2034#32)       --  ld1     {v20.16b-v23.16b}, [x1], #64
  ]

theorem sha512_block_armv8_test3 (s : ArmState)
  (h_s_ok : read_err s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s = true)
  (h_pc : read_pc s = 0x1264c0#64)
  (h_program : s.program = sha512_program_snippet3.find?)
  (h_s' : s' = run 4 s) :
  read_err s' = StateError.None := by
  -- sym1 [h_program]
  sorry

end SHA512_proof
