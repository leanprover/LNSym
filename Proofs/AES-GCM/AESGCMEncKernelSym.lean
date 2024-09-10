/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.Memory.Separate
import Proofs.«AES-GCM».AESGCMEncKernelPre
import Tactics.Sym

namespace AESGCMEncKernelProgram

abbrev in_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 0#5) s
abbrev in_bits_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 1#5) s
abbrev Xi_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 3#5) s
abbrev ivec_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 4#5) s
abbrev key_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 5#5) s
abbrev rounds_addr (s : ArmState) : BitVec 64 := (r (StateField.GPR 5#5) s) + 240#64
abbrev Htable_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 6#5) s
abbrev out_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 2#5) s

set_option maxRecDepth 1000000 in
theorem aes_gcm_enc_kernel_program_run_xx (s0 sf : ArmState)
    (h_s0_program : s0.program = aes_gcm_enc_kernel_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = aes_gcm_enc_kernel_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run 139 s0)
    -- AES256 rounds = 14, the address of rounds is stored in x5+240
    (h_rounds : 14#32 = read_mem_bytes 4 (rounds_addr s0) s0)
    -- memory separation
    (h_mem : Memory.Region.pairwiseSeparate
      [⟨(in_addr s0), 128⟩, ⟨(in_bits_addr s0), 64⟩,
       ⟨(Xi_addr s0), 128⟩, ⟨(ivec_addr s0), 128⟩,
       ⟨(key_addr s0), 1984⟩, -- 240*8 bits key schedule and 64 bits rounds
       ⟨(Htable_addr s0), 2048⟩, -- 16*128 bits, only first 12 elements are used
       ⟨(out_addr s0), 128⟩ ])
    : read_err sf = .None := by
    simp (config := {ground := true}) only at h_s0_pc
    sym_n 138
    case h_s1_sp_aligned =>
      apply Aligned_BitVecAdd_64_4
      · assumption
      · simp only (config := {ground := true})
    init_next_step h_run h_step_139 s139
    replace h_step_139 := h_step_139.symm
    rw [aes_gcm_enc_kernel_program.stepi_eq_0x7cf838] at h_step_139<;> try assumption
    -- Instruction at pc 0x7cf79c#64 : cmp x17, #0xc, compares rounds
    -- against 12 and branch out to AES-128 if rounds is less than 12 (equals 10)
    -- We need accumulated (non)effects from this instruction to get branch condition
    -- It would be tedious to list all the (non)effects out in a simp tactic
    -- simp [state_simp_rules, bitvec_rules, minimal_theory] at h_step_139
    sorry

end AESGCMEncKernelProgram
