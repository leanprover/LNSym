/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

Experimental: The goal is to prove that this program implements memcpy correctly
using the VCG framework.
-/
import Arm
import Tactics.StepThms
import Tactics.Sym
import Correctness.ArmSpec

/-- Helper projections for registers `xn` -/
@[state_simp_rules]
def ArmState.x (n : Nat) : ArmState → BitVec 64
| s => read_gpr 64 n s

@[state_simp_rules]
def ArmState.x0 := ArmState.x 0
@[state_simp_rules]
def ArmState.x1 := ArmState.x 1
@[state_simp_rules]
def ArmState.x2 := ArmState.x 2

namespace Memcpy

/-
while (x0 != 0) {
  q4 := read_mem(16 bytes from address x1)
  x1 := x1 + 16
  write_mem(16 bytes of q4 to address x2)
  x2 := x2 + 16
  x0 := x0 - 1
}
-/
def program : Program :=
  def_program
    [
     /- 00000000000008e0 <mem_copy>:                         -/
     (0x8e0#64, 0x14000004#32),  /- b   8f0 <loop_test>      -/
     /- 00000000000008e4 <mem_copy_loop>:                    -/
     (0x8e4#64, 0x3cc10424#32),  /- ldr q4, [x1], #16        -/
     (0x8e8#64, 0x3c810444#32),  /- str q4, [x2], #16        -/
     (0x8ec#64, 0xd1000400#32),  /- sub x0, x0, #0x1         -/
     /- 00000000000008f0 <loop_test>:                        -/
     (0x8f0#64, 0xf100001f#32),  /- cmp x0, #0x0             -/
     (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
     (0x8f8#64, 0xd65f03c0#32)   /- ret                      -/
    ]


/-- Precondition for the correctness of the MemCpy program. -/
def pre (s : ArmState) : Prop :=
  let num_blks := ArmState.x0 s
  -- 16 bytes are copied in each iteration of the loop.
  let num_bytes := num_blks * 16
  let src_base  := ArmState.x1 s
  let dst_base  := ArmState.x2 s
  -- (TODO) Also allow for the possibility of src_base = dst_base
  -- or even more generally,
  -- dst_base ≤ src_base ∨
  -- src_base + num_bytes ≤ dst_base.
  mem_separate' src_base num_bytes.toNat dst_base num_bytes.toNat ∧
  read_pc s = 0x8e0#64 ∧
  s.program = program ∧
  read_err s = .None ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym1_n` tactic currently expects this. Remove this conjunct when `sym1_n`
  -- is updated to make this requirement optional.
  CheckSPAlignment s

/-- Postcondition for the correctness of the MemCpy program. -/
def post (s0 sf : ArmState) : Prop :=
  let num_blks := ArmState.x0 s0
  let num_bytes := num_blks * 16
  let src_base  := ArmState.x1 s0
  let dst_base  := ArmState.x2 s0
  -- The destination in the final state is a copy of the source in the initial
  -- state.
  /-
  NOTE: we could also state this property as follows:

  (read_mem_bytes num_bytes.toNat dst_base sf =
   read_mem_bytes num_bytes.toNat src_base s0) ∧

  and we ought to try expressing it this way too.

  However, we prefer using quantifiers because it mirrors how we tend to state
  and prove some cryptographic obligations, i.e., each `n`-byte block in a given
  region is hashed/encrypted correctly (for some appropriate `n`, which is 16
  here).
  -/
  (∀ i : BitVec 64, i < num_blks →
    read_mem_bytes 16 (dst_base + (16 * i)) sf =
    id (read_mem_bytes 16 (src_base + (16 * i)) s0)) ∧
  -- All memory regions separate from the destination are unchanged.
  (∀ (n : Nat) (addr : BitVec 64),
      mem_separate' dst_base num_bytes.toNat addr n →
      read_mem_bytes n addr sf = read_mem_bytes n addr s0) ∧
  read_pc sf = 0x8f8#64 ∧
  read_err sf = .None ∧
  sf.program = program ∧
  CheckSPAlignment sf

def exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = 0x8f8#64

def cut (s : ArmState) : Bool :=
  -- First instruction
  read_pc s = 0x8e0#64 ||
  -- Loop guard (branch instruction)
  read_pc s = 0x8f4#64 ||
  -- First instruction following the loop
  -- which also happens to be the program's last instruction
  read_pc s = 0x8f8#64

def loop_inv (s0 si : ArmState) : Prop :=
  let num_blks := ArmState.x0 s0
  let curr_num_blks := ArmState.x0 si
  let num_blks_copied := num_blks - curr_num_blks
  let num_bytes_copied := 16 * num_blks_copied
  let src_base  := ArmState.x1 s0
  let curr_src_base := ArmState.x1 si
  let dst_base  := ArmState.x2 s0
  let curr_dst_base  := ArmState.x2 si
  let curr_zf := r (StateField.FLAG PFlag.Z) si
  curr_num_blks ≤ num_blks ∧
  ((curr_zf = 1#1) ↔ (curr_num_blks = 0#64)) ∧
  curr_src_base = src_base + num_bytes_copied ∧
  curr_dst_base = dst_base + num_bytes_copied ∧
  (∀ i : BitVec 64, i < num_blks_copied →
    read_mem_bytes 16 (dst_base + (16 * i)) si =
    id (read_mem_bytes 16 (src_base + (16 * i)) s0)) ∧
  read_err si = .None ∧
  si.program = program ∧
  CheckSPAlignment si

def assert (s0 si : ArmState) : Prop :=
  pre s0 ∧
  match (read_pc si) with
  | 0x8e0#64 => -- First instruction
    si = s0
  | 0x8f4#64 => -- Loop guard
    loop_inv s0 si
  | 0x8f8 => -- Loop and program post
    post s0 si
  | _ => False

instance : Spec' ArmState where
  pre    := pre
  post   := post
  exit   := exit
  cut    := cut
  assert := assert

-------------------------------------------------------------------------------
-- Symbolic Simulation of basic blocks

-- #genStepEqThms program

-------------------------------------------------------------------------------

theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_verification_conditions
  case v1 =>
    intro s0 h_pre
    sorry
  case v2 =>
    intro sf h_exit
    sorry
  case v3 =>
    intro s0 sf h_assert h_exit
    sorry
  case v4 =>
    intro s0 si h_assert h_exit
    sorry

theorem termination :
  Termination ArmState := by
  simp [Termination, Spec.pre, Spec.exit, exit,
        state_simp_rules, bitvec_rules, minimal_theory]
  intro s h_pre
  sorry

end Memcpy
