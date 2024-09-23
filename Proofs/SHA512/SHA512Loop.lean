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

-- (TODO @shilpi) Write the loop invariant.

structure sha512_loop_post
  (pc nblocks sp ctx_base input_base : BitVec 64)
  (si : ArmState) : Prop where
  h_program    : si.program = program
  h_pc         : r .PC si = pc
  h_err        : r .ERR si = .None
  h_sp_aligned : CheckSPAlignment si
  -- No blocks must be left unhashed by the time the loop runs to completion.
  h_num_blocks : num_blocks si = 0#64
  h_sp         : stack_ptr si = sp - 16#64
  h_ctx_base   : ctx_addr si = ctx_base
  h_input_base : input_addr si = input_base
  -- (TODO @shilpi) The ctx must contain the hash.
  -- h_ctx        : si[ctx_base, 64] = SHA2.h0_512.toBitVec
  h_ktbl       : si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512
  h_mem_sep    : Memory.Region.pairwiseSeparate
                  [(sp - 16#64,   16),
                   (ctx_base,     64),
                   (input_base,   (nblocks.toNat * 128)),
                   (ktbl_addr,    (SHA2.k_512.length * 8))]

theorem sha512_loop_post.iff_def :
  (sha512_loop_post pc nblocks sp ctx_base input_base si) ↔
  (si.program = program ∧
   r .PC si = pc ∧
   r .ERR si = .None ∧
   CheckSPAlignment si ∧
   num_blocks si = 0#64 ∧
   stack_ptr si = sp - 16#64 ∧
   ctx_addr si = ctx_base ∧
   input_addr si = input_base ∧
  --  si[ctx_base, 64] = SHA2.h0_512.toBitVec ∧
   si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
   Memory.Region.pairwiseSeparate
                 [(sp - 16#64,   16),
                  (ctx_base,     64),
                  (input_base,   (nblocks.toNat * 128)),
                  (ktbl_addr,    (SHA2.k_512.length * 8))]) := by
  constructor
  · intro h
    obtain ⟨⟩ := h
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
set_option debug.skipKernelTC true in
-- set_option trace.Tactic.sym.heartbeats true in
-- set_option profiler true in
-- set_option profiler.threshold 1 in
set_option maxHeartbeats 0 in
-- set_option maxRecDepth 0 in
theorem sha512_block_armv8_loop_1block (si sf : ArmState)
  (h_N : N = 1#64)
  (h_si_prelude : sha512_prelude 0x126500#64 N SP CtxBase InputBase si)
  -- TODO: Ideally, nsteps ought to be 485 to be able to simulate the loop to
  -- completion.
  (h_steps : nsteps = 20)
  (h_run : sf = run nsteps si) :
  -- (FIXME) PC should be 0x126c94#64 i.e., we are poised to execute the first
  -- instruction following the loop. For now, we stop early on to remain in sync.
  -- with the number of steps we simulate.
  sha512_loop_post (0x126500#64 + nsteps*4)
     N SP CtxBase InputBase sf := by
  -- Prelude
  subst h_N h_steps
  obtain ⟨h_si_program, h_si_pc, h_si_err, h_si_sp_aligned,
          h_si_num_blocks, h_si_sp, h_si_ctx_base,
          h_si_input_base, h_si_ctx, h_si_ktbl, h_si_separate⟩ := h_si_prelude
  simp only [num_blocks, ctx_addr, stack_ptr, input_addr] at *
  simp only [sha512_loop_post.iff_def]
  -- Symbolic Simulation
  sym_n 20
  -- Epilogue
  -- cse (config := { processHyps := .allHyps })
  simp (config := {ground := true}) only
        [fst_AddWithCarry_eq_sub_neg,
         ConditionHolds,
         state_simp_rules,
         bitvec_rules, minimal_theory]
  sym_aggregate
  exact ⟨h_si_ktbl, h_si_separate⟩
  done

end SHA512
