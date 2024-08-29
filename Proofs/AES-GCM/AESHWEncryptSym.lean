/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Tests.«AES-GCM».AESHWEncryptProgram
import Tactics.Sym
import Tactics.StepThms

namespace AESHWEncryptProgram

#genStepEqTheorems aes_hw_encrypt_program

theorem aes_hw_encrypt_program_run_60 (s0 sf : ArmState)
    (h_s0_program : s0.program = aes_hw_encrypt_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = aes_hw_encrypt_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run 60 s0)
    -- AES256 rounds = 14, the address of rounds is stored in x2
    (h_rounds : 14 = read_mem_bytes 8 (read_gpr 64 2#5 s0) s0) :
    read_err sf = .None := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `aes_hw_encrypt_program.min` is somehow
  --    unable to be reflected
  -- TODO: branching condition currently not supported
  sorry
  -- sym_n 60
  -- subst h_run
  -- assumption
  -- done
