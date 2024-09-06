/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Proofs.«AES-GCM».GCMInitV8Pre
import Tactics.Sym
import Tactics.Aggregate
import Specs.GCMV8

namespace GCMInitV8Program

abbrev H_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 1#5) s
abbrev Htable_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 0#5) s

set_option debug.byAsSorry true in
set_option maxRecDepth 1000000 in
set_option profiler true in
theorem gcm_init_v8_program_run_152 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_init_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_init_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run gcm_init_v8_program.length s0)
    (h_mem : Memory.Region.pairwiseSeparate
      [ ⟨(H_addr s0), 128⟩,
        ⟨(Htable_addr s0), 2048⟩ ])
    : read_err sf = .None := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_init_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 152
  done

-- TODO: this function is from Tests.Common
-- need to put it in a better place
def revflat (x : List (BitVec n)) : BitVec (n * x.length) :=
  have h : n * x.reverse.length = n * x.length := by simp only [List.length_reverse]
  BitVec.cast h $ BitVec.flatten (List.reverse x)


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
set_option profiler true in
theorem gcm_init_v8_program_correct (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_init_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_init_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run gcm_init_v8_program.length s0)
    (h_mem : Memory.Region.pairwiseSeparate
      [ ⟨(H_addr s0), 128⟩,
        ⟨(Htable_addr s0), 2048⟩ ])
    : -- effects
      -- no instruction decoding error
      read_err sf = .None
      -- program is unchanged
    ∧ sf.program = gcm_init_v8_program
      -- SP is still aligned
    ∧ CheckSPAlignment sf
      -- PC is updated
    ∧ read_pc sf = 0x79f5ec#64
    -- TODO: Commenting out memory related conjuncts since it seems
    -- to make symbolic execution stuck
    --   -- First 12 elemets in Htable is correct
    -- ∧ read_mem_bytes 192 (Htable_addr sf) sf
    --   = revflat (GCMV8.GCMInitV8 (read_mem_bytes 16 (H_addr s0) s0))
    -- non-effects
    -- State values that shouldn't change do not change
    -- TODO: figure out all registers that are used ...
    ∧ (∀ (f : StateField), ¬ (f = StateField.PC) ∧
                           ¬ (f = (StateField.GPR 29#5)) →
        r f sf = r f s0)
    -- -- Memory safety: memory location that should not change did
    -- -- not change
    -- -- The addr exclude output region Htable
    -- ∧ (∀ (n : Nat) (addr : BitVec 64) (h: addr < (Htable_addr sf) ∨ addr >= (Htable_addr sf) + 128*12),
    --     read_mem_bytes n addr sf = read_mem_bytes n addr s0)
    := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_init_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 152
  -- sym_aggregate
  sorry
