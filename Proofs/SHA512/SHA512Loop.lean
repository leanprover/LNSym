/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Proofs.SHA512.SHA512Prelude
open BitVec

/-! ## Reasoning about the SHA512 loop

We prove that at the end of an iteration of the SHA512 loop, `loop_post`
is satisfied.
-/

namespace SHA512

/--
Vector instruction `REV64` that reverses the order of 16-byte elements in each
64-bit slice of the 128-bit input.

Ref.:
https://developer.arm.com/documentation/ddi0602/2024-06/SIMD-FP-Instructions/REV64--Reverse-elements-in-64-bit-doublew
-/
def vrev64_16 (x : BitVec 128) :  BitVec 128 :=
  rev_vector 128 64 16 x
    (by decide) (by decide) (by decide)
    (by decide) (by decide)

/--
Loop postcondition when exactly one block needs to be hashed.
-/
def loop_post (PC N SP CtxBase InputBase : BitVec 64)
              (si : ArmState) : Prop :=
  -- TODO: Write a better spec. function.
  -- let spec_digest := 0#512
  -- let impl_digest :=
  --  r (.SFP 3#5) si ++ r (.SFP 2#5) si ++
  --  r (.SFP 1#5) si ++ r (.SFP 0#5) si
  -- All blocks must be hashed.
  num_blocks si = 0 ∧
  si.program = program ∧
  r .PC si = PC ∧
  r .ERR si = .None ∧
  CheckSPAlignment si ∧
  ctx_addr si = CtxBase ∧
  stack_ptr si = SP - 16#64 ∧
  si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
  Memory.Region.pairwiseSeparate
                  [(SP - 16#64,   16),
                   (CtxBase,     64),
                   (InputBase,    (N.toNat * 128)),
                   (ktbl_addr,    (SHA2.k_512.length * 8))] ∧
  r (.GPR 3#5) si = ktbl_addr ∧
  input_addr si = InputBase + (N * 128#64) ∧
  -- Registers contain the last processed input block.
  r (.SFP 16#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 0)), 16]) ∧
  r (.SFP 17#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 1)), 16]) ∧
  r (.SFP 18#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 2)), 16]) ∧
  r (.SFP 19#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 3)), 16]) ∧
  r (.SFP 20#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 4)), 16]) ∧
  r (.SFP 21#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 5)), 16]) ∧
  r (.SFP 22#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 6)), 16]) ∧
  r (.SFP 23#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 7)), 16])
  -- spec_digest = impl_digest -- TODO

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
set_option maxRecDepth 8000 in
theorem sha512_block_armv8_loop_1block (si sf : ArmState)
  (h_N : N = 1#64)
  (h_si_prelude : sha512_prelude 0x126500#64 N SP CtxBase InputBase si)
  -- TODO: Ideally, nsteps ought to be 485 to be able to simulate the loop to
  -- completion.
  (h_steps : nsteps = 200)
  (h_run : sf = run nsteps si) :
  -- (FIXME) PC should be 0x126c94#64 i.e., we are poised to execute the first
  -- instruction following the loop. For now, we stop early on to remain in sync.
  -- with the number of steps we simulate.
  loop_post (0x126500#64 + nsteps*4) N SP CtxBase InputBase sf := by
  -- Prelude
  subst h_N h_steps
  obtain ⟨h_si_program, h_si_pc, h_si_err, h_si_sp_aligned,
          h_si_num_blocks, h_si_sp, h_si_ctx_base,
          h_si_input_base, h_si_ctx, h_si_ktbl, h_si_separate⟩ := h_si_prelude
  simp only [num_blocks, ctx_addr, stack_ptr, input_addr] at *
  simp only [loop_post]
  -- Symbolic Simulation
  /-
  TODO @alex: The following aggregation fails with
  "simp failed, maximum number of steps exceeded"
  -/
  -- sym_n 200
  -- Epilogue
  -- cse (config := { processHyps := .allHyps })
  -- simp (config := {ground := true}) only
        -- [fst_AddWithCarry_eq_sub_neg,
        --  ConditionHolds,
        --  state_simp_rules,
        --  bitvec_rules, minimal_theory]
  -- sym_aggregate
  -- assumption
  -- done
  sorry

end SHA512
