/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Proofs.SHA512.SHA512Prelude
open BitVec

/-! ## Reasoning about the SHA512 loop

We prove that at the end of an iteration of the SHA512 loop, `sha512_loop_post`
is satisfied.
-/

namespace SHA512

structure sha512_loop_post (nblocks : BitVec 64) (si : ArmState) : Prop where
  h_program    : si.program = program
  h_err        : r .ERR si = .None
  -- (FIXME) PC should be 0x126c94#64 i.e., we are poised to execute the first
  -- instruction following the loop.
  h_pc         : r .PC si = 0x1268e8#64
  h_sp_aligned : CheckSPAlignment si
  h_num_blocks : num_blocks si = 0#64
  -- h_ktbl_addr  : r (.GPR 3#5) si = ktbl_addr
  -- h_ctx        : si[ctx_addr si, 64] = SHA2.h0_512.toBitVec
  -- h_ktbl       : si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512
  -- h_mem_sep    : Memory.Region.pairwiseSeparate
  --                 [(stack_ptr si,   16),
  --                  (ctx_addr si,    64),
  --                  (input_addr si - 128#64, ((num_blocks si).toNat * 128)),
  --                  (ktbl_addr,      (SHA2.k_512.length * 8))]

theorem sha512_loop_post.iff_def :
  (sha512_loop_post nblocks si) ↔
  (si.program = program ∧
   r .ERR si = .None ∧
  -- (FIXME) PC should be 0x126c94#64 i.e., we are poised to execute the first
  -- instruction following the loop.
   r .PC si = 0x1268e8#64 ∧
   CheckSPAlignment si ∧
   num_blocks si = 0#64) := by
  constructor
  · intro h
    obtain ⟨h_program, h_err, h_pc, h_sp_aligned, h_num_blocks⟩ := h
    simp only [*, minimal_theory]
  · intro h
    constructor <;> simp only [*, minimal_theory]
  done

/- TODO: Symbolically simulate (program.length - 16 - 3) = 485 instructions
here. We elide the 16 instructions before the loop and 3 instructions after it.
Note that this would involve automatically reasoning about the conditional
branch here:
-- (0x126c90#64 , 0xb5ffc382#32) --  cbnz    x2, 126500 <sha512_block_armv8+0x40>
-/
set_option linter.unusedVariables false in
-- set_option trace.Tactic.sym.heartbeats true in
-- set_option profiler true in
-- set_option profiler.threshold 1 in
theorem sha512_block_armv8_loop_1block (s0 sf : ArmState)
  (h_s0_prelude : sha512_prelude 1#64 s0)
  (h_run : sf = run 250 s0) :
  sha512_loop_post 0#64 sf := by
  -- Prelude
  obtain ⟨h_s0_program, h_s0_err, h_s0_pc, h_s0_sp_aligned,
          h_s0_num_blocks, h_s0_x3, h_s0_ctx,
          h_s0_ktbl, h_s0_separate⟩ := h_s0_prelude
  simp only [num_blocks, ctx_addr, stack_ptr, input_addr] at *
  simp only [sha512_loop_post.iff_def]
  -- Symbolic Simulation
  sym_n 250
  -- Epilogue
  -- cse (config := { processHyps := .allHyps })
  simp (config := {decide := true})  only
        [fst_AddWithCarry_eq_add, fst_AddWithCarry_eq_sub_neg,
         h_s0_num_blocks,
         bitvec_rules, minimal_theory]
  done

end SHA512
