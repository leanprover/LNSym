/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Util
import Arm.Syntax
import Tactics.Sym
import Tactics.Aggregate
import Tactics.CSE
import Arm.Memory.SeparateAutomation
import Correctness.ArmSpec
import Tests.SHA2.SHA512ProgramTest
import Proofs.SHA512.SHA512StepLemmas
import Lean
open BitVec

/-! ## Reasoning about SHA512 instructions preceeding the loop

We prove that the first basic block of SHA512 produces a state that satisfies
`sha512_prelude`. We can subsequently symbolically simulate the loop body with
`sha512_prelude` as the precondition. See `SHA512Loop.lean`.
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


private theorem add_eq_sub_16 (x : BitVec 64) :
  x + 0xfffffffffffffff0#64 = x - 16#64 := by
  bv_decide

structure sha512_prelude (nblocks : BitVec 64) (si : ArmState) : Prop where
  h_program    : si.program = program
  h_err        : r .ERR si = .None
  h_pc         : r .PC si = 0x126500#64
  h_sp_aligned : CheckSPAlignment si
  h_num_blocks : num_blocks si = nblocks
  h_ktbl_addr  : r (.GPR 3#5) si = ktbl_addr
  -- ctx_addr si = ctx_addr s
  -- input_addr si = input_addr s + 128#64
  -- stack_ptr si = stack_ptr s - 16#64
  h_ctx        : si[ctx_addr si, 64] = SHA2.h0_512.toBitVec
  h_ktbl       : si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512
  h_mem_sep    : Memory.Region.pairwiseSeparate
                  [(stack_ptr si,   16),
                   (ctx_addr si,    64),
                   (input_addr si - 128#64, ((num_blocks si).toNat * 128)),
                   (ktbl_addr,      (SHA2.k_512.length * 8))]

theorem sha512_prelude.def (h : sha512_prelude nblocks si) :
  si.program = program ∧
  r .ERR si = .None ∧
  r .PC si = 0x126500#64 ∧
  CheckSPAlignment si ∧
  num_blocks si = nblocks ∧
  r (.GPR 3#5) si = ktbl_addr ∧
  si[ctx_addr si, 64] = SHA2.h0_512.toBitVec ∧
  si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
  Memory.Region.pairwiseSeparate
            [(stack_ptr si,   16),
             (ctx_addr si,    64),
             (input_addr si - 128#64, ((num_blocks si).toNat * 128)),
             (ktbl_addr,      (SHA2.k_512.length * 8))] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  repeat' apply And.intro
  repeat assumption
  done

theorem sha512_prelude.of_def
  (h : si.program = program ∧
       r .ERR si = .None ∧
       r .PC si = 0x126500#64 ∧
       CheckSPAlignment si ∧
       num_blocks si = nblocks ∧
       r (.GPR 3#5) si = ktbl_addr ∧
       si[ctx_addr si, 64] = SHA2.h0_512.toBitVec ∧
       si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
       Memory.Region.pairwiseSeparate
                [(stack_ptr si,   16),
                 (ctx_addr si,    64),
                 (input_addr si - 128#64, ((num_blocks si).toNat * 128)),
                 (ktbl_addr,      (SHA2.k_512.length * 8))]) :
  sha512_prelude nblocks si := by
  obtain ⟨h_program, h_err, h_pc, h_sp_aligned, h_num_blocks, h_ktbl_addr,
          h_ctx, h_ktbl, h_mem_sep⟩ := h
  constructor
  repeat assumption
  done

theorem sha512_prelude.iff_def :
  (sha512_prelude nblocks si) ↔
  (si.program = program ∧
   r .ERR si = .None ∧
   r .PC si = 0x126500#64 ∧
   CheckSPAlignment si ∧
   num_blocks si = nblocks ∧
   r (.GPR 3#5) si = ktbl_addr ∧
   si[ctx_addr si, 64] = SHA2.h0_512.toBitVec ∧
   si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
   Memory.Region.pairwiseSeparate
            [(stack_ptr si,   16),
             (ctx_addr si,    64),
             (input_addr si - 128#64, ((num_blocks si).toNat * 128)),
             (ktbl_addr,      (SHA2.k_512.length * 8))]) := by
  constructor
  · apply sha512_prelude.def
  · intro h
    apply sha512_prelude.of_def
    assumption
  done

theorem sha512_block_armv8_prelude (s0 sf : ArmState)
  (h_s0_pc : read_pc s0 = 0x1264c0#64)
  (h_s0_err : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_s0_program : s0.program = program)
  -- We fix the number of blocks to hash to 1.
  (h_s0_num_blocks : num_blocks s0 = 1#64)
  (_h_s0_x3 : r (StateField.GPR 3#5) s0 = ktbl_addr)
  (h_s0_ctx : read_mem_bytes 64 (ctx_addr s0) s0 = SHA2.h0_512.toBitVec)
  (h_s0_ktbl : read_mem_bytes (SHA2.k_512.length * 8) ktbl_addr s0 = BitVec.flatten SHA2.k_512)
  (h_s0_separate :
    Memory.Region.pairwiseSeparate
    [((stack_ptr s0 - 16#64),   16),
     (ctx_addr s0,    64),
     (input_addr s0,  ((num_blocks s0).toNat * 128)),
     (ktbl_addr,      (SHA2.k_512.length * 8))])
  (h_run : sf = run 16 s0) :
  sha512_prelude (num_blocks s0) sf ∧
  ctx_addr sf = ctx_addr s0 ∧
  input_addr sf = input_addr s0 + 128#64 ∧
  stack_ptr sf = stack_ptr s0 - 16#64 := by
  -- Symbolic Simulation
  sym_n 1
  case h_s1_sp_aligned =>
    simp only [CheckSPAlignment, state_simp_rules] at h_s0_sp_aligned
    /-
    (FIXME) The `rw` below fails with:
    tactic 'rewrite' failed, did not find instance of the pattern in the target expression
    extractLsb 3 0 (?m.1887 + ?m.1888)

    Why is `Aligned` opened up here?
    -/
    -- rw [Aligned_BitVecAdd_64_4]
    -- This also fails:
    -- have := @Aligned_BitVecAdd_64_4 (r (StateField.GPR 31#5) s0) 18446744073709551600#64
    --         h_s0_sp_aligned (by decide)
    -- rw [this]
    apply Aligned_BitVecAdd_64_4 h_s0_sp_aligned (by decide)
  sym_n 15 at s1
  -- Epilogue
  simp only [num_blocks, stack_ptr, ctx_addr, input_addr, ←add_eq_sub_16] at *
  -- cse (config := { processHyps := .allHyps })
  simp (config := {decide := true}) only
        [h_s0_num_blocks, h_s0_ktbl,
         AddWithCarry, stack_ptr, input_addr,
         bitvec_rules, minimal_theory]
  -- The following discharges
  --  r (StateField.GPR 0x1#5) s0 + 0x40#64 + 0x40#64 =
  --  r (StateField.GPR 0x1#5) s0 + 0x80#64
  simp only [BitVec.add_assoc, bitvec_rules, minimal_theory]
  -- Opening up `sha512_prelude`:
  simp only [sha512_prelude.iff_def, num_blocks, ctx_addr]
  -- (FIXME @alex) Why does `s16.program = program` remain even after aggregation?
  sym_aggregate
  simp only [h_s16_program, minimal_theory]
  -- Only memory-related obligations are left.
  -- Eliminating ∀ in memory non-effect hyps.
  simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  -- Rewrite *_mem_bytes (in terms of ArmState) to *_bytes (in terms of Memory).
  simp only [memory_rules] at *
  -- (FIXME) Need to aggregate memory effects here automatically.
  simp only [h_s16_memory_effects,
             h_s15_memory_effects,
             h_s14_memory_effects,
             h_s13_memory_effects,
             h_s12_memory_effects,
             h_s11_memory_effects,
             h_s10_memory_effects,
             h_s9_memory_effects,
             h_s8_memory_effects,
             h_s7_memory_effects,
             h_s6_memory_effects,
             h_s5_memory_effects,
             h_s4_memory_effects,
             h_s3_memory_effects,
             h_s2_memory_effects,
             h_s1_memory_effects]
  constructor
  · simp_mem
    simp only [Nat.sub_self, bitvec_rules]
    -- (FIXME @bollu) `extractLsBytes_eq_self` is in `bitvec_rules` but still,
    -- we had to apply it below.
    apply extractLsBytes_eq_self
  · simp only [h_s0_num_blocks, bitvec_rules] at h_s0_separate
    constructor
    · -- (FIXME @bollu) simp_mem doesn't make progress here. :-(
      rw [Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate']
      simp only [h_s0_ktbl]
      -- (FIXME @bollu) Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem
      -- works here, but using it is painful.
      have := Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem h_s0_separate 3 0 (by decide)
              (ktbl_addr, (SHA2.k_512.length * 8))
              ((r (StateField.GPR 0x1f#5) s0 + 0xfffffffffffffff0#64), 16)
      simp at this
      simp only [this]
    · simp only [h_s0_separate,
                 BitVec.add_assoc, BitVec.add_sub_cancel, bitvec_rules, minimal_theory]
  done
