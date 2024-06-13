/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Util
import Tactics.Sym
import Tests.SHA2.SHA512ProgramTest

section SHA512_proof

open BitVec

----------------------------------------------------------------------

-- Test 1: We have a 4 instruction program, and we attempt to simulate
-- all of them.

def sha512_program_test_1 : program :=
  def_program
    [(0x126538#64 , 0xcec08230#32),      --  sha512su0       v16.2d, v17.2d
     (0x12653c#64 , 0x6e154287#32),      --  ext     v7.16b, v20.16b, v21.16b, #8
     (0x126540#64 , 0xce6680a3#32),      --  sha512h q3, q5, v6.2d
     (0x126544#64 , 0xce678af0#32)       --  sha512su1       v16.2d, v23.2d, v7.2d
     ]

-- set_option profiler true in
-- set_option pp.deepTerms true in
theorem sha512_program_test_1_sym (s0 s_final : ArmState)
  (h_s0_pc : read_pc s0 = 0x126538#64)
  (h_s0_sp_aligned : CheckSPAlignment s0 = true)
  (h_s0_program : s0.program = sha512_program_test_1)
  (h_s0_ok : read_err s0 = StateError.None)
  (h_run : s_final = run 4 s0) :
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic simulation
  sym_n 4 h_s0_program
  -- Final steps
  unfold run at h_run
  subst s_final s_4
  simp_all only [state_simp_rules, minimal_theory, bitvec_rules]
  done

----------------------------------------------------------------------

-- Test 2: A 6 instruction program.

def sha512_program_test_2 : program :=
  def_program
    [(0x126538#64 , 0xcec08230#32),      --  sha512su0       v16.2d, v17.2d
     (0x12653c#64 , 0x6e154287#32),      --  ext     v7.16b, v20.16b, v21.16b, #8
     (0x126540#64 , 0xce6680a3#32),      --  sha512h q3, q5, v6.2d
     (0x126544#64 , 0xce678af0#32),      --  sha512su1       v16.2d, v23.2d, v7.2d
     (0x126548#64 , 0x4ee38424#32),      --  add     v4.2d, v1.2d, v3.2d
     (0x12654c#64 , 0xce608423#32)       --  sha512h2        q3, q1, v0
     ]

-- set_option profiler true in
theorem sha512_program_test_2_sym (s0 s_final : ArmState)
  (h_s0_pc : read_pc s0 = 0x126538#64)
  (h_s0_program : s0.program = sha512_program_test_2)
  (h_s0_ok : read_err s0 = StateError.None)
  (h_run : s_final = run 6 s0) :
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic simulation
  sym_n 6 h_s0_program
  -- Final steps
  unfold run at h_run
  subst s_final s_6
  simp_all only [state_simp_rules, minimal_theory, bitvec_rules]
  done

----------------------------------------------------------------------

-- Test 3:

def sha512_program_test_3 : program :=
  def_program
   [(0x1264c0#64 , 0xa9bf7bfd#32),      --  stp     x29, x30, [sp, #-16]!
    (0x1264c4#64 , 0x910003fd#32),      --  mov     x29, sp
    (0x1264c8#64 , 0x4cdf2030#32),      --  ld1     {v16.16b-v19.16b}, [x1], #64
    (0x1264cc#64 , 0x4cdf2034#32)       --  ld1     {v20.16b-v23.16b}, [x1], #64
  ]

-- set_option profiler true in
-- set_option maxRecDepth 10000 in
set_option pp.deepTerms false in
set_option pp.deepTerms.threshold 10 in
theorem sha512_block_armv8_test_3_sym (s0 s_final : ArmState)
  (h_s0_ok : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0 = true)
  (h_s0_pc : read_pc s0 = 0x1264c0#64)
  (h_s0_program : s0.program = sha512_program_test_3)
  (h_run : s_final = run 4 s0) :
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic simulation
  sym_n 4 h_s0_program
  -- Final steps
  unfold run at h_run
  subst s_final s_4
  simp_all only [state_simp_rules, minimal_theory, bitvec_rules]
  done

-- example: ofBool ((2#2).getLsb 1) = 1 := by
--   simp only [reduceGetLsb, ofBool_true, ofNat_eq_ofNat]

-- theorem test4 (s0 : ArmState) :
-- read_mem_bytes 16 (read_gpr 64 31#5 s0 + 18446744073709551600#64)
--  (w StateField.PC (1205444#64)
--     (w (StateField.GPR 31#5) (read_gpr 64 31#5 s0 + 18446744073709551600#64)
--       (write_mem_bytes (2 * ((8 <<< if (!0#1 == 1#1) = true then 2 + ((2#2).lsb 1).toNat else 2 + (2#2).toNat) / 8))
--         (read_gpr 64 31#5 s0 + 18446744073709551600#64)
--         (zeroExtend (8 <<< if (!0#1 == 1#1) = true then 2 + ((2#2).lsb 1).toNat else 2 + (2#2).toNat)
--             (r (StateField.GPR 30#5) s0) ++
--           zeroExtend (8 <<< if (!0#1 == 1#1) = true then 2 + ((2#2).lsb 1).toNat else 2 + (2#2).toNat)
--             (r (StateField.GPR 29#5) s0))
--         s0))) ==
--   (zeroExtend (8 <<< if (!0#1 == 1#1) = true then 2 + ((2#2).lsb 1).toNat else 2 + (2#2).toNat)
--             (r (StateField.GPR 30#5) s0) ++
--           zeroExtend (8 <<< if (!0#1 == 1#1) = true then 2 + ((2#2).lsb 1).toNat else 2 + (2#2).toNat)
--             (r (StateField.GPR 29#5) s0)) := by
--           simp (config := {decide := true}) [state_simp_rules, minimal_theory, bitvec_rules, lsb, reduceGetLsb, ofBool_true, ofNat_eq_ofNat]
--           apply read_mem_bytes_of_write_mem_bytes_same
--           simp only [Nat.reducePow, Nat.reduceLeDiff]
--           done

----------------------------------------------------------------------

-- Test 4: sha512_block_armv8_test_4_sym --- this is a symbolic
-- simulation test for the AWS-LC production SHA512 code (the program
-- we'd like to verify).

-- set_option profiler true in
theorem sha512_block_armv8_test_4_sym (s0 s_final : ArmState)
  (h_s0_ok : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0 = true)
  (h_s0_pc : read_pc s0 = 0x1264c0#64)
  (h_s0_program : s0.program = sha512_program_map)
  (h_run : s_final = run 32 s0) :
  read_err s_final = StateError.None := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic simulation
  -- sym_n 1 h_s0_program
  sorry

end SHA512_proof
