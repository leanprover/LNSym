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
import Tactics.ClearNamed
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

/--
Preconditions for the simulation of SHA512.
-/
structure sha512_init_pre
    (pc nblocks sp ctx_base input_base : BitVec 64)
    (s0 : ArmState) : Prop where
  h_program    : s0.program = program
  h_pc         : read_pc s0 = pc
  h_err        : read_err s0 = .None
  h_sp_aligned : CheckSPAlignment s0
  h_num_blocks : num_blocks s0 = nblocks
  h_sp         : stack_ptr s0 = sp
  h_ctx_base   : ctx_addr s0 = ctx_base
  h_input_base : input_addr s0 = input_base
  h_ctx        : s0[ctx_addr s0, 64] = SHA2.h0_512.toBitVec
  h_ktbl       : s0[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512
  h_mem_sep    : Memory.Region.pairwiseSeparate
                  [((sp - 16#64), 16),
                   (ctx_base,     64),
                   (input_base,   (nblocks.toNat * 128)),
                   (ktbl_addr,    (SHA2.k_512.length * 8))]

/--
Invariant that must hold after SHA512's first basic block is simulated, i.e.,
the basic block immediately preceding the loop.
-/
structure sha512_prelude
    (pc nblocks sp ctx_base input_base : BitVec 64)
    (si : ArmState) : Prop where
  h_program    : si.program = program
  h_pc         : r .PC si = pc
  h_err        : r .ERR si = .None
  h_sp_aligned : CheckSPAlignment si
  h_num_blocks : num_blocks si = nblocks
  h_sp         : stack_ptr si = sp - 16#64
  h_ctx_base   : ctx_addr si = ctx_base
  h_input_base : input_addr si = input_base + 128#64
  h_ctx        : si[ctx_base, 64] = SHA2.h0_512.toBitVec
  h_ktbl       : si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512
  h_mem_sep    : Memory.Region.pairwiseSeparate
                  [(sp - 16#64,   16),
                   (ctx_base,     64),
                   (input_base,   (nblocks.toNat * 128)),
                   (ktbl_addr,    (SHA2.k_512.length * 8))]

theorem sha512_prelude.def
  (h : sha512_prelude pc nblocks sp ctx_base input_base si) :
  si.program = program ∧
  r .PC si = pc ∧
  r .ERR si = .None ∧
  CheckSPAlignment si ∧
  num_blocks si = nblocks ∧
  stack_ptr si = sp - 16#64 ∧
  ctx_addr si = ctx_base ∧
  input_addr si = input_base + 128#64 ∧
  si[ctx_base, 64] = SHA2.h0_512.toBitVec ∧
  si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
  Memory.Region.pairwiseSeparate
            [(sp - 16#64, 16),
             (ctx_base,   64),
             (input_base, (nblocks.toNat * 128)),
             (ktbl_addr,  (SHA2.k_512.length * 8))] := by
  obtain ⟨⟩ := h
  repeat' apply And.intro
  repeat assumption
  done

theorem sha512_prelude.of_def
  (h : si.program = program ∧
       r .PC si = pc ∧
       r .ERR si = .None ∧
       CheckSPAlignment si ∧
       num_blocks si = nblocks ∧
       stack_ptr si = sp - 16#64 ∧
       ctx_addr si = ctx_base ∧
       input_addr si = input_base + 128#64 ∧
       si[ctx_base, 64] = SHA2.h0_512.toBitVec ∧
       si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
       Memory.Region.pairwiseSeparate
                 [(sp - 16#64, 16),
                  (ctx_base,   64),
                  (input_base, (nblocks.toNat * 128)),
                  (ktbl_addr,  (SHA2.k_512.length * 8))]) :
         sha512_prelude pc nblocks sp ctx_base input_base si := by
  obtain ⟨h_program, h_pc, h_err, h_sp_aligned, h_num_blocks,
          h_sp, h_ctx_base, h_input_base, h_ctx, h_ktbl,
          h_mem_sep⟩ := h
  constructor
  repeat assumption
  done

theorem sha512_prelude.iff_def :
  (sha512_prelude pc nblocks sp ctx_base input_base si) ↔
  (si.program = program ∧
   r .PC si = pc ∧
   r .ERR si = .None ∧
   CheckSPAlignment si ∧
   num_blocks si = nblocks ∧
   stack_ptr si = sp - 16#64 ∧
   ctx_addr si = ctx_base ∧
   input_addr si = input_base + 128#64 ∧
   si[ctx_base, 64] = SHA2.h0_512.toBitVec ∧
   si[ktbl_addr, (SHA2.k_512.length * 8)] = BitVec.flatten SHA2.k_512 ∧
   Memory.Region.pairwiseSeparate
             [(sp - 16#64, 16),
              (ctx_base,   64),
              (input_base, (nblocks.toNat * 128)),
              (ktbl_addr,  (SHA2.k_512.length * 8))]) := by
  constructor
  · apply sha512_prelude.def
  · intro h
    apply sha512_prelude.of_def
    assumption
  done

private theorem add_eq_sub_16 (x : BitVec 64) :
  x + 0xfffffffffffffff0#64 = x - 16#64 := by
  bv_decide

-- Convention: Use PascalCase for "constants". E.g., `N`, `SP`, `CtxBase`, and
-- `InputBase` below always refer to projections of the initial state `s0`.

-- (TODO) Modifying this theorem is an exercise in patience because of
-- user-interactivity delays. Let's report this.
theorem sha512_block_armv8_prelude (s0 sf : ArmState)
  -- We fix the number of blocks to hash to 1.
  (h_N : N = 1#64)
  (h_s0_init : sha512_init_pre 0x1264c0#64
                               N SP CtxBase InputBase s0)
  (h_run : sf = run 16 s0) :
  sha512_prelude 0x126500#64 N SP CtxBase InputBase sf ∧
  -- (TODO @shilpi) State register non-effects here.
  ∀ (n : Nat) (addr : BitVec 64),
    mem_separate' addr n (SP - 16#64) 16 →
    sf[addr, n] = s0[addr, n] := by
  -- Prelude
  obtain ⟨h_s0_program, h_s0_pc, h_s0_err, h_s0_sp_aligned,
          h_s0_num_blocks, h_s0_sp, h_s0_ctx_base,
          h_s0_input_base, h_s0_ctx, h_s0_ktbl,
          h_s0_mem_sep⟩ := h_s0_init
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
  -- simp only [num_blocks, stack_ptr, ctx_addr, input_addr, ←add_eq_sub_16] at *
  simp only [←add_eq_sub_16] at *
  -- cse (config := { processHyps := .allHyps })
  simp only [sha512_prelude.iff_def, bitvec_rules, minimal_theory]
  -- Opening up `sha512_prelude`:
  -- (FIXME @alex) Why does `s16.program = program` remain even after aggregation?
  sym_aggregate
  simp only [h_s16_program, ←add_eq_sub_16, minimal_theory]
  -- The following discharges
  --  InputBase + 0x40#64 + 0x40#64 =
  --  InputBase + 0x80#64
  -- (TODO @bollu) canonicalization: move constants to the left.
  -- Also upstream, please.
  simp only [BitVec.add_assoc, bitvec_rules, minimal_theory]
  -- Only memory-related obligations are left.
  -- (TODO @alex/@bollu) Remove ∀ in memory (non)effect hyps generated by
  -- `sym_n`. The user may still state memory properties using quantifiers.
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
  -- (NOTE @bollu) The following need to be opened up for `simp_mem`,
  -- apparently. Is this a big deal though? Maybe not?
  -- Sid says this is probably because omega is unable to see through the
  -- defs.
  simp only [num_blocks, stack_ptr, ctx_addr, input_addr] at *
  constructor
  · constructor
    · -- (TODO @bollu) Think about whether `simp_mem` should be powerful enough to solve this goal.
      -- Also, `mem_omega` name suggestion from Alex for the already souped up `simp_mem`.
      simp_mem
      simp only [h_s0_ctx_base, Nat.sub_self, minimal_theory, bitvec_rules]
    · constructor
      · -- (FIXME @bollu) simp_mem doesn't make progress here. :-(
        -- simp only [←h_s0_sp] at h_s0_mem_sep
        rw [Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate']
        simp only [h_s0_ktbl]
        -- (FIXME @bollu) Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem
        -- works here, but using it is painful. Also, mispelled lemma.
        have := Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem
                h_s0_mem_sep 3 0 (by decide)
                (ktbl_addr, (SHA2.k_512.length * 8))
                ((SP + 0xfffffffffffffff0#64), 16)
        simp at this
        simp only [h_s0_sp, this]
      · simp only [h_s0_sp, h_s0_num_blocks, h_s0_input_base, h_s0_ctx_base,
                   h_s0_mem_sep,
                   BitVec.add_assoc, bitvec_rules, minimal_theory]
  · intro n addr h
    simp only [←h_s0_sp] at h
    clear_named [h_, stepi]
    simp_mem
    /-
    (NOTE @bollu): Without the `clear_named...` above, we run into the following
    error(s):

    At this point, the conclusion is:
    `Memory.read_bytes n addr s0.mem = Memory.read_bytes n addr s0.mem`
    which rfl can't close (error: `The rfl tactic failed. Possible reasons:...`)
    and
    `exact Eq.refl _` errors out like so:
    `(deterministic) timeout at elaborator, maximum number of heartbeats
     (200000) has been reached...`
    -/
    rfl
  done

end SHA512
