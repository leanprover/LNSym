/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Memory.MemoryProofs
import Specs.SHA512
import Arm.Memory.SeparateAutomation

-- import Tactics.Sym
-- import Proofs.SHA512.SHA512StepLemmas
open BitVec

/- The memory aliasing proof obligations in
`sha512_block_armv8_prelude_sym_ctx_access` and
`sha512_block_armv8_loop_sym_ktbl_access` are similar -- we want to read a
small portion of a larger memory region. Note that we aren't really reasoning
about read-over-writes here --- `write_mem_bytes` doesn't even appear in these
proofs.

Other considerations:

1. Can we come up with a succinct way of stating that some memory regions are
   mutually separate, and have that formulation work with the automation? E.g.,
   the ctx, input, and ktbl regions in this program are all separate from each
   other, and we need 3C2 `mem_separate` terms to convey this information. If we
   also added the stack (which we have elided at this point), then we'd need 4C2
   terms; this number just grows alarmingly with the number of memory regions under
   consideration.

2. Feel free to change the `mem_separate`/`mem_subset`/`mem_legal` API to a more
   convenient one, if needed (e.g., to take a memory region's base address and
   size (as a `Nat`), instead of a region's first and last address). Think about
   the consequences of such a change --- e.g., using closed intervals disallows
   zero-length memory regions, and using a `Nat` size allows them; any pitfalls
   there?
-/

namespace SHA512MemoryAliasing

abbrev ctx_addr   (s : ArmState) : BitVec 64 := r (StateField.GPR 0#5) s
abbrev input_addr (s : ArmState) : BitVec 64 := r (StateField.GPR 1#5) s
abbrev num_blocks (s : ArmState) : BitVec 64 := r (StateField.GPR 2#5) s
-- (FIXME) Programmatically obtain the ktbl address from the ELF binary's
-- .rodata section. This address is computed in the program and stored in
-- register x3 using the following couple of instructions:
-- (0x1264d4#64 , 0xd0000463#32),      --  adrp    x3, 1b4000 <ecp_nistz256_precomputed+0x25000>
-- (0x1264d8#64 , 0x910c0063#32),      --  add     x3, x3, #0x300
abbrev ktbl_addr : BitVec 64 := 0x1b4300#64

/-
Let's automatically figure out what
`read_mem_bytes 16 <addr> s0`
should simplify to, where `<addr>` can be
[ctx_addr, ctx_addr + 16#64, ctx_addr + 32#64, ctx_addr + 48#64]

Let's also check our address normalization implementation, e.g., does the automation
work for `16#64 + ctx_addr`? What about `8#64 + ctx_addr + 8#64`? Other
variations?
-/
-- set_option trace.simp_mem true in
-- set_option trace.simp_mem.info true in
theorem sha512_block_armv8_prelude_sym_ctx_access (s0 : ArmState)
  (_h_s0_err : read_err s0 = StateError.None)
  (_h_s0_sp_aligned : CheckSPAlignment s0)
  (h_s0_pc : read_pc s0 = 0x1264c4#64)
  (_h_s0_program : s0.program = sha512_program)
  (h_s0_num_blocks : num_blocks s0 = 1)
  (_h_s0_x3 : r (StateField.GPR 3#5) s0 = ktbl_addr)
  (hlegal : mem_legal' (ctx_addr s0) 64)
  (h_s0_ctx : read_mem_bytes 64 (ctx_addr s0) s0 = SHA2.h0_512.toBitVec)
  (h_s0_ktbl : read_mem_bytes (SHA2.k_512.length * 8) ktbl_addr s0 = BitVec.flatten SHA2.k_512)
  -- (FIXME) Add separateness invariants for the stack's memory region.
  -- @bollu: can we assume that `h_s1_ctx_input_separate`
  -- will be given as ((num_blocks s1).toNat * 128)?
  -- This is much more harmonious since we do not need to worry about overflow.
  (h_s0_ctx_input_separate :
    mem_separate' (ctx_addr s0)   64
                 (input_addr s0) ((num_blocks s0).toNat * 128))
  (h_s0_ktbl_ctx_separate :
    mem_separate' (ctx_addr s0) 64
                  ktbl_addr  (SHA2.k_512.length * 8))
  (h_s0_ktbl_input_separate :
    mem_separate' (input_addr s0) ((num_blocks s0).toNat * 128)
                  ktbl_addr      (SHA2.k_512.length * 8))
  -- (h_run : sf = run 4 s0)
  :
  -- @shilpi: rewrite `SHA2.h0_512.toBitVec.extractLsBytes 48 16` to
  -- `(extractLsBytes SHA2.h0_512.toBitVec 48 16)`
  -- cause it's easier to read.
  read_mem_bytes 16 (ctx_addr s0 + 48#64) s0 = SHA2.h0_512.toBitVec.extractLsBytes 48 16 := by
  simp_all only [memory_rules]
  simp_mem
  -- ⊢ SHA2.h0_512.toBitVec.extractLsBytes ((ctx_addr s0 + 48#64).toNat - (ctx_addr s0).toNat) 16 =
  -- SHA2.h0_512.toBitVec.extractLsBytes 48 16
  -- @shilpi: should this also be proven automatically? feels a little unreasonable to me.
  · congr
    -- ⊢ (ctx_addr s0 + 48#64).toNat - (ctx_addr s0).toNat = 48
    bv_omega

/--
info: 'SHA512MemoryAliasing.sha512_block_armv8_prelude_sym_ctx_access' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms sha512_block_armv8_prelude_sym_ctx_access

/-
Let's automatically figure out what
`read_mem_bytes 16 <addr> s0`
should simplify to, where `<addr>` can be
[ktbl_addr, ktbl_addr + 16#64, ktbl_addr + 32#64, ..., ktbl_addr + 624#64].

Let's also check our address normalization implementation, e.g., does the automation
work for `16#64 + ktbl_addr`?

-- @bollu: TODO: implement address normalization here, so we can simplify e.g.
--   TODO: add similar tests for all `ktbl_addr + n*16#64` for n in [0, 16].
--   (16#64 + ktbl_addr) + 16#64
--   ~> 32#64 ktbl_addr
-/
-- set_option trace.simp_mem true in
-- set_option trace.simp_mem.info true in
#time theorem sha512_block_armv8_loop_sym_ktbl_access (s1 : ArmState)
  (_h_s1_err : read_err s1 = StateError.None)
  (_h_s1_sp_aligned : CheckSPAlignment s1)
  (h_s1_pc : read_pc s1 = 0x126500#64)
  (_h_s1_program : s1.program = sha512_program)
  (h_s1_num_blocks : num_blocks s1 = 1)
  (_h_s1_x3 : r (StateField.GPR 3#5) s1 = ktbl_addr)
  (h_s1_ctx : read_mem_bytes 64 (ctx_addr s1) s1 = SHA2.h0_512.toBitVec)
  (h_s1_ktbl : read_mem_bytes (SHA2.k_512.length * 8) ktbl_addr s1 = BitVec.flatten SHA2.k_512)
  -- (FIXME) Add separateness invariants for the stack's memory region.
  -- @bollu: can we assume that `h_s1_ctx_input_separate`
  -- will be given as ((num_blocks s1).toNat * 128)?
  -- This is much more harmonious since we do not need to worry about overflow.
  (h_s1_ctx_input_separate :
    mem_separate' (ctx_addr s1)   64
                 (input_addr s1) ((num_blocks s1).toNat * 128))
  (h_s1_ktbl_ctx_separate :
    mem_separate' (ctx_addr s1)   64
                  ktbl_addr      ((SHA2.k_512.length * 8 )))
  (h_s1_ktbl_input_separate :
    mem_separate' (input_addr s1) ((num_blocks s1).toNat * 128)
                  ktbl_addr      (SHA2.k_512.length * 8)) :
  read_mem_bytes 16 ktbl_addr s1 =
  (BitVec.flatten SHA2.k_512).extractLsBytes 0 16 := by
  simp_all only [memory_rules]
  -- @bollu: we need 'hSHA2_k512_length' to allow omega to reason about
  -- SHA2.k_512.length, which is otherwise treated as an unintepreted constant.
  have hSHA2_k512_length : SHA2.k_512.length = 80 := rfl
  conv =>
    lhs
    simp_mem ⊂ r at h_s1_ktbl with [] -- It should fail if it makes no progress. Also, make small examples that demonstrate such failures.
  rfl

/--
info: 'SHA512MemoryAliasing.sha512_block_armv8_loop_sym_ktbl_access' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms sha512_block_armv8_loop_sym_ktbl_access


end SHA512MemoryAliasing
