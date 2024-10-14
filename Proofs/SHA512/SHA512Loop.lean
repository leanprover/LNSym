/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Proofs.SHA512.SHA512Prelude
import Proofs.SHA512.SHA512_block_armv8_rules
import Arm.Memory.AddressNormalization
open BitVec

/-! ## Reasoning about the SHA512 loop

We prove that at the end of an iteration of the SHA512 loop, `loop_post`
is satisfied.
-/

namespace SHA512

def loop_post_1 (PC N SP CtxBase InputBase : BitVec 64)
                (si sf : ArmState) : Prop :=
  -- We subtract from `num_blocks` early on in the loop body.
  num_blocks sf = 0#64 ∧
  sf.program = program ∧
  r .PC sf = PC ∧
  r .ERR sf = .None ∧
  CheckSPAlignment sf ∧
  input_addr sf = InputBase ∧
  ctx_addr sf = CtxBase ∧
  stack_ptr sf = SP - 16#64 ∧
  sf[KtblAddr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
  sf[InputBase, (N.toNat * 128)] = si[InputBase, (N.toNat * 128)] ∧
   Memory.Region.pairwiseSeparate
                   [(SP - 16#64,  16),
                    (CtxBase,     64),
                    (InputBase,   (N.toNat * 128)),
                    (KtblAddr,    (SHA2.k_512.length * 8))] ∧
  r (.GPR 3#5) sf = KtblAddr + 16#64 ∧
  r (.SFP 26#5) sf = r (.SFP 0#5) si ∧
  r (.SFP 27#5) sf = r (.SFP 1#5) si ∧
  r (.SFP 28#5) sf = r (.SFP 2#5) si ∧
  r (.SFP 29#5) sf = r (.SFP 3#5) si ∧
  r (StateField.SFP 0x10#5) sf = DPSFP.vrev128_64_8 si[InputBase, 16] ∧
  r (StateField.SFP 0x11#5) sf = DPSFP.vrev128_64_8 si[(InputBase + 0x10#64), 16] ∧
  r (StateField.SFP 0x12#5) sf = DPSFP.vrev128_64_8 si[(InputBase + 0x20#64), 16] ∧
  r (StateField.SFP 0x13#5) sf = DPSFP.vrev128_64_8 si[(InputBase + 0x30#64), 16] ∧
  r (StateField.SFP 0x14#5) sf = DPSFP.vrev128_64_8 si[(InputBase + 0x40#64), 16] ∧
  r (StateField.SFP 0x15#5) sf = DPSFP.vrev128_64_8 si[(InputBase + 0x50#64), 16] ∧
  r (StateField.SFP 0x16#5) sf = DPSFP.vrev128_64_8 si[(InputBase + 0x60#64), 16] ∧
  r (StateField.SFP 0x17#5) sf = DPSFP.vrev128_64_8 si[(InputBase + 0x70#64), 16] ∧
  -- The following is true only when N = 1.
  r (StateField.FLAG PFlag.Z) sf = 0x1#1

theorem sha512_block_armv8_loop_1 (si sf : ArmState)
  (h_N : N = 1#64)
  (h_si_prelude : SHA512.prelude 0x126500#64 N SP CtxBase InputBase si)
  (h_steps : nsteps = 8)
  (h_run : sf = run nsteps si) :
  loop_post_1 (0x126500#64 + nsteps*4) N SP CtxBase InputBase si sf := by
  -- Prelude
  subst h_N h_steps
  obtain ⟨h_si_program, h_si_pc, h_si_err, h_si_sp_aligned,
          h_si_sp, h_si_num_blocks, h_si_ctx_base,
          h_si_input_base, h_si_ktbl_base,
          _h_si_ctx, h_si_ktbl, h_si_separate,
          _h_si_q0, _h_si_q1, _h_si_q2, _h_si_q3,
          h_si_16, h_si_17, h_si_18, h_si_19,
          h_si_20, h_si_21, h_si_22, h_si_23⟩ := h_si_prelude
  simp only [num_blocks, ctx_addr, stack_ptr, input_addr] at *
  simp only [loop_post_1]
  simp at h_si_separate
  -- Symbolic Simulation
  sym_n 8
  -- Epilogue
  simp only [h_si_ktbl, h_si_separate, minimal_theory]
  done

-------------------------------------------------------------------------------

def loop_post_2 (PC N SP CtxBase InputBase : BitVec 64)
                (si sf : ArmState) : Prop :=
  -- We subtract from `num_blocks` early on in the loop body.
  num_blocks sf = 0#64 ∧
  sf.program = program ∧
  r .PC sf = PC ∧
  r .ERR sf = .None ∧
  CheckSPAlignment sf ∧
  input_addr sf = InputBase ∧
  ctx_addr sf = CtxBase ∧
  stack_ptr sf = SP - 16#64 ∧
  sf[KtblAddr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
  sf[InputBase, (N.toNat * 128)] = si[InputBase, (N.toNat * 128)] ∧
  Memory.Region.pairwiseSeparate
                   [(SP - 16#64,  16),
                    (CtxBase,     64),
                    (InputBase,   (N.toNat * 128)),
                    (KtblAddr,    (SHA2.k_512.length * 8))] ∧
  r (.GPR 3#5) sf = KtblAddr + 16#64 + 16#64 ∧
  r (.SFP 3#5) sf =
    DPSFP.sha512h2 (r (StateField.SFP 0x1#5) si) (r (StateField.SFP 0x0#5) si)
      (DPSFP.sha512h (extractLsb' 64 128 (r (StateField.SFP 0x3#5) si ++ r (StateField.SFP 0x2#5) si))
        (extractLsb' 64 128 (r (StateField.SFP 0x2#5) si ++ r (StateField.SFP 0x1#5) si))
        (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x3#5) si)
          (extractLsb' 64 128
            (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x18#5) si)
                (DPSFP.vrev128_64_8 (read_mem_bytes 16 InputBase si)) 0x0#128 ++
              DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x18#5) si)
                (DPSFP.vrev128_64_8 (read_mem_bytes 16 InputBase si)) 0x0#128))
          0x0#128)) ∧
  r (.SFP 4#5) sf =
    DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x1#5) si)
      (DPSFP.sha512h (extractLsb' 64 128 (r (StateField.SFP 0x3#5) si ++ r (StateField.SFP 0x2#5) si))
        (extractLsb' 64 128 (r (StateField.SFP 0x2#5) si ++ r (StateField.SFP 0x1#5) si))
        (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x3#5) si)
          (extractLsb' 64 128
            (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x18#5) si)
                (DPSFP.vrev128_64_8 (read_mem_bytes 16 InputBase si)) 0x0#128 ++
              DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x18#5) si)
                (DPSFP.vrev128_64_8 (read_mem_bytes 16 InputBase si)) 0x0#128))
          0x0#128))
      0x0#128 ∧
  r (.SFP 5#5) sf =
    extractLsb' 64 128 (r (StateField.SFP 0x3#5) si ++ r (StateField.SFP 0x2#5) si) ∧
  r (.SFP 6#5) sf =
    extractLsb' 64 128 (r (StateField.SFP 0x2#5) si ++ r (StateField.SFP 0x1#5) si) ∧
  r (.SFP 7#5) sf =
    extractLsb' 64 128
      (DPSFP.vrev128_64_8 (read_mem_bytes 16 (InputBase + 0x50#64) si) ++
        DPSFP.vrev128_64_8 (read_mem_bytes 16 (InputBase + 0x40#64) si)) ∧
  r (.SFP 16#5) sf =
    DPSFP.sha512su1 (DPSFP.vrev128_64_8 (read_mem_bytes 16 (InputBase + 0x70#64) si))
      (extractLsb' 64 128
        (DPSFP.vrev128_64_8 (read_mem_bytes 16 (InputBase + 0x50#64) si) ++
          DPSFP.vrev128_64_8 (read_mem_bytes 16 (InputBase + 0x40#64) si)))
      (DPSFP.sha512su0 (DPSFP.vrev128_64_8 (read_mem_bytes 16 (InputBase + 0x10#64) si))
        (DPSFP.vrev128_64_8 (read_mem_bytes 16 InputBase si))) ∧
  r (.SFP 24#5) sf =
    extractLsb' 64 128
      (DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x18#5) si)
          (DPSFP.vrev128_64_8 (read_mem_bytes 16 InputBase si)) 0x0#128 ++
        DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (r (StateField.SFP 0x18#5) si)
          (DPSFP.vrev128_64_8 (read_mem_bytes 16 InputBase si)) 0x0#128) ∧
  r (.SFP 25#5) sf =
    read_mem_bytes 16 (KtblAddr + 0x10#64) si

theorem extractLsBytes_ge (h : a ≥ n) (x : BitVec n) :
  x.extractLsBytes a n = 0#(n*8) := by
  apply BitVec.eq_of_getLsbD_eq
  intros i
  simp only [getLsbD_extractLsBytes, Fin.is_lt, decide_True, Bool.true_and, getLsbD_zero]
  apply BitVec.getLsbD_ge
  omega

theorem extractLsBytes_of_read_bytes_le (n m : Nat)
    (h_legal : mem_legal' addr n)
    (h_m_le_n : m ≤ n) :
    (Memory.read_bytes n addr mem).extractLsBytes 0 m =
    Memory.read_bytes m addr mem := by
    apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [extractLsBytes, bitvec_rules]
    simp only [getLsbD_extractLsb', minimal_theory, Fin.isLt]
    have h_n_upper : n ≤ 2^64 := by
      simp only [mem_legal', Nat.reducePow] at h_legal; omega
    have h_m_upper : m ≤ 2^64 := by
      simp [mem_legal'] at h_legal; omega
    have h_i_upper : i < m * 8 := Fin.isLt i
    have h_i_upper2 : i < n * 8 := by omega
    have h_lhs := @Memory.getLsbD_read_bytes n i addr mem h_n_upper
    have h_rhs := @Memory.getLsbD_read_bytes m i addr mem h_m_upper
    simp_all only
    done

/--
info: #[RegType.SFP 0x03#5, RegType.SFP 0x04#5, RegType.SFP 0x05#5, RegType.SFP 0x06#5, RegType.SFP 0x07#5,
  RegType.SFP 0x10#5, RegType.SFP 0x18#5, RegType.SFP 0x19#5]
-/
#guard_msgs in
#eval ((Cfg.create' (0x126500#64 + 8*4) (0x126500#64 + 8*4 + 12*4) SHA512.program).toOption.get!).maybe_modified_regs

theorem sha512_block_armv8_loop_2 (sprev si sf : ArmState)
  (h_N : N = 1#64)
  (h_si_prelude : loop_post_1 (0x126500#64 + 8*4) N SP CtxBase InputBase sprev si)
  (h_steps : nsteps = 12)
  (h_run : sf = run nsteps si) :
  loop_post_2 (0x126500#64 + 8*4 + nsteps*4) N SP CtxBase InputBase
              si sf := by
  -- Prelude
  subst h_N h_steps
  simp at h_si_prelude ⊢
  obtain ⟨h_si_num_blocks, h_si_program, h_si_pc, h_si_err,
          h_si_sp_aligned, h_si_input_base, h_si_ctx_base,
          h_si_sp, h_si_ktbl, keep_h_si_input,
          keep_h_si_separate, h_si_ktbl_base,
          _h_si_q0, _h_si_q1, _h_si_q2, _h_si_q3,
          h_si_16, h_si_17, h_si_18, h_si_19,
          h_si_20, h_si_21, h_si_22, h_si_23, h_si_zf⟩ := h_si_prelude
  simp only [input_addr, ctx_addr] at *
  simp only [BitVec.reduceToNat, Nat.reduceMul] at keep_h_si_input
  simp only [loop_post_2]
  -- Symbolic Simulation
  sym_n 12
  -- Epilogue
  simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  simp only [memory_rules] at *
  simp at keep_h_si_separate
  simp only [h_si_ktbl, keep_h_si_separate, minimal_theory]
  have h_si_input_1 : (Memory.read_bytes 16 InputBase sprev.mem) =
                      (Memory.read_bytes 16 InputBase si.mem) := by
    clear_named [h_s, h_run, step, _h]
    -- simp_mem (config := {useOmegaToClose := true})
    rw [@Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
        128 InputBase (Memory.read_bytes 128 InputBase sprev.mem)]
    · simp only [Nat.reduceMul, Nat.sub_self, bitvec_rules]
      -- (FIXME) Need a theorem about `extractLsBytes_of_read_bytes` to simplify
      -- terms like
      -- `(Memory.read_bytes 128 InputBase sprev.mem).extractLsBytes 0 16`
      sorry
    · rfl
    · simp_mem
  have h_si_input_2 : Memory.read_bytes 16 (InputBase + 0x10#64) sprev.mem =
                      Memory.read_bytes 16 (InputBase + 0x10#64) si.mem := by
    sorry
  have h_si_input_3 : Memory.read_bytes 16 (InputBase + 0x40#64) sprev.mem =
                      Memory.read_bytes 16 (InputBase + 0x40#64) si.mem := by
    sorry
  have h_si_input_4 : Memory.read_bytes 16 (InputBase + 0x50#64) sprev.mem =
                      Memory.read_bytes 16 (InputBase + 0x50#64) si.mem := by
    sorry
  have h_si_input_5 : Memory.read_bytes 16 (InputBase + 0x70#64) sprev.mem =
                      Memory.read_bytes 16 (InputBase + 0x70#64) si.mem := by
    sorry
  simp only [h_si_input_1, h_si_input_2, h_si_input_3,
             h_si_input_4, h_si_input_5,
             minimal_theory]
  done

-------------------------------------------------------------------------------
--/--
--Loop postcondition when exactly one block needs to be hashed.
---/
---- def loop_post (PC N SP CtxBase InputBase : BitVec 64)
--              -- (si : ArmState) : Prop :=
--  TODO: Write a better spec. function.
--  let spec_digest := 0#512
--  let impl_digest :=
--   r (.SFP 3#5) si ++ r (.SFP 2#5) si ++
--   r (.SFP 1#5) si ++ r (.SFP 0#5) si
--  All blocks must be hashed.
--  -- num_blocks si = 0#64 ∧
--  -- si.program = program ∧
--  -- r .PC si = PC ∧
--  -- r .ERR si = .None ∧
--  -- CheckSPAlignment si ∧
--  -- ctx_addr si = CtxBase ∧
--  -- stack_ptr si = SP - 16#64 ∧
--  -- si[KtblAddr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
--  (TODO @alex @bollu Uncomment, please, for stress-testing)
-- Memory.Region.pairwiseSeparate
--                 [(SP - 16#64,   16),
--                  (CtxBase,     64),
--                  (InputBase,    (N.toNat * 128)),
--                  (KtblAddr,    (SHA2.k_512.length * 8))] ∧
--  -- r (.GPR 3#5) si = KtblAddr ∧
--  -- input_addr si = InputBase + (N * 128#64) ∧
--  Registers contain the last processed input block.
--  -- r (.SFP 16#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 0)), 16]) ∧
--  -- r (.SFP 17#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 1)), 16]) ∧
--  -- r (.SFP 18#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 2)), 16]) ∧
--  -- r (.SFP 19#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 3)), 16]) ∧
--  -- r (.SFP 20#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 4)), 16]) ∧
--  -- r (.SFP 21#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 5)), 16]) ∧
--  -- r (.SFP 22#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 6)), 16]) ∧
--  -- r (.SFP 23#5) si = vrev64_16 (si[input_addr si - (128#64 - (16#64 * 7)), 16])
--  spec_digest = impl_digest -- TODO
----
---- /- TODO: Symbolically simulate (program.length - 16 - 3) = 485 instructions
---- here. We elide the 16 instructions before the loop and 3 instructions after it.
---- Note that this would involve automatically reasoning about the conditional
---- branch here:
--(0x126c90#64 , 0xb5ffc382#32) --  cbnz    x2, 126500 <sha512_block_armv8+0x40>
---- -/
---- set_option linter.unusedVariables false in
---- set_option debug.skipKernelTC true in
--set_option trace.Tactic.sym.heartbeats true in
--set_option profiler true in
--set_option profiler.threshold 1 in
---- set_option maxHeartbeats 0 in
--set_option maxRecDepth 8000 in
---- theorem sha512_block_armv8_loop_1block (si sf : ArmState)
--  -- (h_N : N = 1#64)
--  -- (h_si_prelude : SHA512.prelude 0x126500#64 N SP CtxBase InputBase si)
--  TODO: Ideally, nsteps ought to be 485 to be able to simulate the loop to
--  completion.
--  -- (h_steps : nsteps = 400)
--  -- (h_run : sf = run nsteps si) :
--  (FIXME) PC should be 0x126c94#64 i.e., we are poised to execute the first
--  instruction following the loop. For now, we stop early on to remain in sync.
--  with the number of steps we simulate.
--  -- loop_post (0x126500#64 + nsteps*4) N SP CtxBase InputBase sf := by
--  Prelude
--  -- subst h_N h_steps
--  -- obtain ⟨h_si_program, h_si_pc, h_si_err, h_si_sp_aligned,
--          -- h_si_num_blocks, h_si_sp, h_si_ctx_base,
--          -- h_si_input_base, h_si_ctx, h_si_ktbl, h_si_separate⟩ := h_si_prelude
--  -- simp only [num_blocks, ctx_addr, stack_ptr, input_addr] at *
--  -- simp only [loop_post]
--  -- simp at h_si_separate
--  Symbolic Simulation
--  -- /-
--  -- TODO @alex: The following aggregation fails with
--  -- "simp failed, maximum number of steps exceeded"
--  -- -/
--  -- sym_n 100
--  -- sym_n 100
--  -- sym_n 100
--  -- sym_n 100
--  sym_aggregate
----
----
--  Epilogue
--  cse (config := { processHyps := .allHyps })
--  simp (config := {ground := true}) only
--        [fst_AddWithCarry_eq_sub_neg,
--         ConditionHolds,
--         state_simp_rules,
--         bitvec_rules, minimal_theory]
--  sym_aggregate
--  assumption
--  done
--  -- sorry
--
end SHA512
