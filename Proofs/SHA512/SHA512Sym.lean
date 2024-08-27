/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Util
import Tactics.Sym
import Tactics.CSE
import Tests.SHA2.SHA512ProgramTest
import Proofs.SHA512.SHA512StepLemmas
import Lean
open BitVec

/-! ### Symbolic Simulation for SHA512 (1 message block)
In this experiment, we fix the number of blocks to be hashed (in
register `x2`) to `1`, which essentially transforms the SHA512 program
into a straight-line one.

We attempt to prove that the final state after symbolically simulating a fixed
number of SHA512 instructions is error free and that register x2 is 0 --- note
that the register `x2` is decremented early on in this program:

    (0x126504#64 , 0xf1000442#32),      --  subs    x2, x2, #0x1

In the near future, we'd like to prove that the hash computed for this
one input block matches the expected value, i.e., one dictated by
`SHA2.sha512`.

Also see `Tests.SHA2.SHA512ProgramTest` for an example of a concrete
run that checks the implementation against the specification.
-/

namespace SHA512

abbrev stack_ptr  (s : ArmState) : BitVec 64 := r (StateField.GPR 31#5) s
abbrev ctx_addr   (s : ArmState) : BitVec 64 := r (StateField.GPR 0#5) s
abbrev input_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 1#5) s
abbrev num_blocks (s : ArmState) : BitVec 64 := r (StateField.GPR 2#5) s
-- (FIXME) Programmatically obtain the ktbl address from the ELF binary's
-- .rodata section. This address is computed in the program and stored in
-- register x3 using the following couple of instructions:
-- (0x1264d4#64 , 0xd0000463#32),      --  adrp    x3, 1b4000 <ecp_nistz256_precomputed+0x25000>
-- (0x1264d8#64 , 0x910c0063#32),      --  add     x3, x3, #0x300
abbrev ktbl_addr : BitVec 64 := 0x1b4300#64

-- set_option profiler true in
-- set_option profiler.threshold 1 in
-- set_option pp.deepTerms false in
open Memory in
set_option maxHeartbeats 9999999 in -- To be fixed by https://github.com/leanprover/LNSym/pull/113
theorem sha512_block_armv8_1block (s0 sf : ArmState)
  -- (FIXME) Ignore the `stp` instruction for now.
  (h_s0_pc : read_pc s0 = 0x1264c4#64)
  (h_s0_err : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_s0_program : s0.program = program)
  -- We fix the number of blocks to hash to 1.
  (_h_s0_num_blocks : num_blocks s0 = 1)
  (_h_s0_x3 : r (StateField.GPR 3#5) s0 = ktbl_addr)
  (_h_s0_ctx : read_mem_bytes 64 (ctx_addr s0) s0 = SHA2.h0_512.toBitVec)
  (_h_s0_ktbl : read_mem_bytes (SHA2.k_512.length * 8) ktbl_addr s0 = BitVec.flatten SHA2.k_512)
  -- (FIXME) Add separateness invariants for the stack's memory region.
  -- (FIXME @bollu): State the separate assumptions in terms of `List.Pairwise mem_separate ...` to ensure linear number of `mem_separate` hypotheses.
  (_h_s0_ctx_input_separate :
    ⟨ctx_addr s0, 64⟩ ⟂ ⟨input_addr s0, (num_blocks s0).toNat * 128⟩)
  (_h_s0_ktbl_ctx_separate :
    ⟨ctx_addr s0, 64⟩ ⟂ ⟨ktbl_addr, SHA2.k_512.length * 8⟩)
  (_h_s0_ktbl_input_separate :
    ⟨input_addr s0, (num_blocks s0).toNat * 128⟩ ⟂ ⟨ktbl_addr, SHA2.k_512.length * 8⟩)
  -- (FIXME) Use program.length instead of 20 here (depends on the
  -- performance of the new symbolic simulation tactic).
  (h_run : sf = run 20 s0) :
  r (StateField.GPR 2#5) sf = 0#64 ∧
  r StateField.ERR sf = StateError.None := by
  sym_n 20
  /-
  (FIXME @bollu) cse fails with the following message:
  no goals to be solved
  -/
  cse (config := { processHyps := .allHyps })
  -- Final Steps
  unfold run at h_run
  subst sf
  rw [h_s20_err]
  simp only [minimal_theory]
  -- (FIXME) Need effects aggregation here.
  sorry

end SHA512
