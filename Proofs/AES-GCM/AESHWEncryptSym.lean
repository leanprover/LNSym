/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Tests.«AES-GCM».AESHWEncryptProgram
import Tactics.Sym
import Tactics.StepThms
import Correctness.ArmSpec

namespace AESHWEncryptProgram

/-- Precondition for aes_hw_encrypt program. -/
def pre (s : ArmState) : Prop :=
  read_pc s = 0x79f5a0#64 ∧
  s.program = aes_hw_encrypt_program ∧
  read_err s = StateError.None ∧
  CheckSPAlignment s

/-- Postcondition for aes_hw_encrypt program. -/
def post (_s0 sf : ArmState) : Prop :=
  read_pc sf = 0x79f5ec#64 ∧
  read_err sf = StateError.None ∧
  sf.program = aes_hw_encrypt_program ∧
  CheckSPAlignment sf

def exit (s : ArmState) : Prop :=
  read_pc s = 0x79f5ec#64

def cut (s : ArmState) : Bool :=
  -- First instruction
  read_pc s = 0x79f5a0#64 ||
  -- Loop guard (branch instruction)
  read_pc s = 0x79f5d0#64 ||
  -- First instruction following the loop
  read_pc s = 0x79f5d4#64 ||
  -- Last instruction
  read_pc s = 0x79f5ec#64

/--
Loop invariant:
-/
def loop_inv (si : ArmState) : Prop :=
  let curr_Nf := read_flag PFlag.N si
  let curr_Vf := read_flag PFlag.V si
  let curr_Zf := read_flag PFlag.Z si
  let curr_w3 := read_gpr 32 3#5 si
  ((curr_Nf = curr_Vf ∧ curr_Zf = 0#1) ↔ curr_w3 > 0) ∧
  read_err si = .None ∧
  si.program = aes_hw_encrypt_program ∧
  CheckSPAlignment si

def loop_post (si : ArmState) : Prop :=
  read_err si = .None ∧
  si.program = aes_hw_encrypt_program ∧
  CheckSPAlignment si

def assert (s0 si : ArmState) : Prop :=
  pre s0 ∧
  match (read_pc si) with
  | 0x79f5a0#64 =>
    si = s0
  | 0x79f5d0#64 =>
    loop_inv si
  | 0x79f5d4#64 =>
    loop_post si
  | 0x79f5ec#64 =>
    post s0 si
  | _ => False

instance : Spec' ArmState where
  pre    := pre
  post   := post
  exit   := exit
  cut    := cut
  assert := assert

theorem AESHWEncrypt.csteps_eq (s : ArmState) (i : Nat) :
  Correctness.csteps s i = if cut s then i
                           else Correctness.csteps (run 1 s) (i + 1) := by
  rw [Correctness.csteps_eq]
  simp only [Sys.next, Spec'.cut, run]
  done

-------------------------------------------------------------------------------

#genStepEqTheorems aes_hw_encrypt_program


theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_verification_conditions
  case v1 =>
    intro s0 h_pre
    simp_all only [Spec.pre, Spec'.assert, pre, assert, minimal_theory]
  case v2 =>
    intro sf h_exit
    simp_all only [Spec.exit, Spec'.cut, exit, cut, minimal_theory]
  case v3 =>
    intro s0 sf h_assert h_exit
    simp_all only [Spec.exit, Spec'.assert, Spec.post, post, exit, assert, minimal_theory]
  case v4 =>
    intro s0 si h_assert h_exit
    simp_all only [Spec'.assert, Spec.exit, assert, exit,
                   minimal_theory, state_simp_rules]
    obtain ⟨h_pre, h_assert⟩ := h_assert
    split at h_assert
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry

theorem termination :
  Termination ArmState := by
  sorry


-- theorem aes_hw_encrypt_program_run_60 (s0 sf : ArmState)
--     (h_s0_program : s0.program = aes_hw_encrypt_program)
--     (h_s0_err : read_err s0 = .None)
--     (h_s0_pc : read_pc s0 = aes_hw_encrypt_program.min)
--     (h_s0_sp_aligned : CheckSPAlignment s0)
--     (h_run : sf = run 60 s0)
--     -- AES256 rounds = 14, the address of rounds is stored in x2
--     (h_rounds : 14 = read_mem_bytes 8 (read_gpr 64 2#5 s0) s0) :
--     read_err sf = .None := by
--   simp (config := {ground := true}) only at h_s0_pc
--   -- ^^ Still needed, because `aes_hw_encrypt_program.min` is somehow
--   --    unable to be reflected
--   -- TODO: branching condition currently not supported
--   sorry
--   -- sym_n 60
--   -- subst h_run
--   -- assumption
--   -- done
