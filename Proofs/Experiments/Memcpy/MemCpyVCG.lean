/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

Experimental: The goal is to prove that this program implements memcpy correctly
using the VCG framework.
-/
import Arm
import Tactics.CSE
import Tactics.Rename
import Tactics.Sym
import Tactics.Rename
import Tactics.Name
import Tactics.ClearNamed
import Tactics.StepThms
import Correctness.ArmSpec
import Arm.Insts.Common
import Arm.Memory.SeparateAutomation
import Arm.Syntax
import Tactics.SkipProof

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

#genStepEqTheorems program

open ArmStateNotation

section PC

/--# We define scoped notation for our cutpoint PCs to use in pattern matching. -/

scoped notation "start" => 0x8e0#64
scoped notation "loop_guard" => 0x8f4#64
scoped notation "loop_post" => 0x8f8#64

def pcs : List (BitVec 64) := [
  start,
  loop_guard,
  loop_post
  ]

@[simp] theorem mem_pcs_iff (pc : BitVec 64) :
    pc ∈ pcs ↔ pc = start ∨ pc = loop_guard ∨ pc = loop_post := by simp [pcs]

@[simp] theorem start_mem_pcs : start ∈ pcs := by simp

@[simp] theorem loop_guard_mem_pcs : loop_guard ∈ pcs := by simp

@[simp] theorem loop_post_mem_pcs : loop_post ∈ pcs := by simp

end PC

structure WellFormedAtPc (s : ArmState) (pc : BitVec 64) : Prop where
  h_program : s.program = program
  h_pc : r StateField.PC s = pc
  h_err : r StateField.ERR s = StateError.None
  h_sp_aligned : CheckSPAlignment s


structure Pre (s : ArmState) (num_blks : Nat) (src_base dst_base : BitVec 64) : Prop where
  -- 16 bytes are copied in each iteration of the loop.
  h_mem_sep : mem_separate' src_base (num_blks * 16) dst_base (num_blks * 16)
  -- -- (TODO) Also allow for the possibility of src_base = dst_base
  -- -- or even more generally,
  -- -- dst_base ≤ src_base ∨
  -- -- src_base + num_bytes ≤ dst_base.
  -- mem_separate' src_base num_bytes.toNat dst_base num_bytes.toNat ∧
  h_pc : r StateField.PC s = 0x8e0#64
  h_program : s.program = program
  h_err : r StateField.ERR s = StateError.None
  h_sp_aligned : CheckSPAlignment s
  h_total_blocks_size : 16 * num_blks < 2 ^ 64

/-- Precondition for the correctness of the MemCpy program. -/
def pre (s : ArmState) : Prop :=
  let num_blks := ArmState.x0 s
  let src_base  := ArmState.x1 s
  let dst_base  := ArmState.x2 s
  Pre s num_blks.toNat src_base dst_base

structure Post (s0 sf : ArmState)
    (num_blks : Nat)
    (src_base dst_base : BitVec 64) : Prop where
  num_blks_le : num_blks ≤ ArmState.x0 s0
  z_eq_zero_iff_x_eq_0 : r (StateField.FLAG PFlag.Z) sf = 1#1 ↔ ArmState.x0 sf = 0#64
  src_base_eq : ArmState.x1 sf = src_base + 16 * (ArmState.x0 s0 - num_blks)
  dst_base_eq : ArmState.x2 sf = dst_base + 16 * (ArmState.x0 s0 - num_blks)
  mem_eq : ∀ i : BitVec 64, i < num_blks →
    read_mem_bytes 16 (dst_base + (16 * i)) sf =
    id (read_mem_bytes 16 (src_base + (16 * i)) s0)
  mem_sep_eq : ∀ (n : Nat) (addr : BitVec 64),
      mem_separate' dst_base num_blks addr n →
      read_mem_bytes n addr sf = read_mem_bytes n addr s0
  err_eq : r StateField.ERR sf = .None
  program_eq : sf.program = program
  sp_aligned : CheckSPAlignment sf

/-- Postcondition for the correctness of the MemCpy program. -/
def post (s0 sf : ArmState) : Prop :=
  let num_blks := ArmState.x0 s0
  let num_bytes := num_blks.toNat * 16
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
  -- TODO (@bollu): we can't prove this, because we don't have this in the loop invariant
  -- to show that emory regions separate from the destination are unchanged.
  -- -- All memory regions separate from the destination are unchanged.
  (∀ (n : Nat) (addr : BitVec 64),
      mem_separate' dst_base num_bytes addr n →
      read_mem_bytes n addr sf = read_mem_bytes n addr s0) ∧
  r StateField.PC sf = 0x8f8#64 ∧
  r StateField.ERR sf = .None ∧
  sf.program = program ∧
  CheckSPAlignment sf

def exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  r StateField.PC s = 0x8f8#64

def cut (s : ArmState) : Bool :=
  -- First instruction
  r StateField.PC s = 0x8e0#64 ||
  -- Loop guard (branch instruction)
  r StateField.PC s = 0x8f4#64 ||
  -- First instruction following the loop
  -- which also happens to be the program's last instruction
  r StateField.PC s = 0x8f8#64

structure LoopInv (s0 si : ArmState)
    (num_blks : Nat)
    (curr_num_blks : Nat)
    (src_base dst_base : BitVec 64) : Prop where
  num_blks_le : curr_num_blks ≤ num_blks
  z_eq_zero_iff_x_eq_0 : r (StateField.FLAG PFlag.Z) si = 1#1 ↔ curr_num_blks = 0#64
  src_base_eq : ArmState.x1 si = src_base + 16 * (num_blks - curr_num_blks)
  dst_base_eq : ArmState.x2 si = dst_base + 16 * (num_blks - curr_num_blks)
  mem_eq : ∀ i : BitVec 64, i < curr_num_blks →
    read_mem_bytes 16 (dst_base + (16 * i)) si =
    id (read_mem_bytes 16 (src_base + (16 * i)) s0)
  mem_sep_eq : ∀ (n : Nat) (addr : BitVec 64),
      mem_separate' dst_base curr_num_blks addr n →
      read_mem_bytes n addr si = read_mem_bytes n addr s0
  err_eq : r StateField.ERR si = .None
  program_eq : si.program = program
  sp_aligned : CheckSPAlignment si

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
  (∀ (n : Nat) (addr : BitVec 64),
      mem_separate' dst_base num_bytes_copied.toNat addr n →
      read_mem_bytes n addr si = read_mem_bytes n addr s0) ∧
  r StateField.ERR si = .None ∧
  si.program = program ∧
  CheckSPAlignment si

def loop_inv.r_z_eq_zero_iff_x_eq_0 (h : loop_inv s0 si) : r (StateField.FLAG PFlag.Z) si = 1#1 ↔ ArmState.x0 si = 0#64 := by
  simp only [loop_inv] at h
  simp [h]

def assert (s0 si : ArmState) : Prop :=
  pre s0 ∧
  match (r StateField.PC si) with
  | start => -- First instruction
    si = s0
  | loop_guard => -- Loop guard
    loop_inv s0 si
  | loop_post => -- Loop and program post
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

section CutTheorems

--  /- 00000000000008e0 <mem_copy>:                         -/
-- 1/7 (0x8e0#64, 0x14000004#32),  /- b   8f0 <loop_test>      -/
--  /- 00000000000008e4 <mem_copy_loop>:                    -/
-- 2/7 (0x8e4#64, 0x3cc10424#32),  /- ldr q4, [x1], #16        -/
-- 3/7 (0x8e8#64, 0x3c810444#32),  /- str q4, [x2], #16        -/
-- 4/7 (0x8ec#64, 0xd1000400#32),  /- sub x0, x0, #0x1         -/
--  /- 00000000000008f0 <loop_test>:                        -/
-- 5/7 (0x8f0#64, 0xf100001f#32),  /- cmp x0, #0x0             -/
-- 6/7 (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
-- 7/7 (0x8f8#64, 0xd65f03c0#32)   /- ret                      -/



structure Stepped (s sn : ArmState) where
  h_step : sn = stepi s

def Stepped.of_next {s sn : ArmState} (h : Sys.next s = sn) : Stepped s sn := ⟨h.symm⟩


structure Step_8e0_8f0 (scur snext : ArmState) extends WellFormedAtPc snext 0x8f0 : Prop where
  h_mem : snext.mem = scur.mem
  h_cut : cut snext = false
  h_x1 : snext.x1 = scur.x1
  h_x2 : snext.x2 = scur.x2
  h_x0 : snext.x0 = scur.x0

--  /- 00000000000008e0 <mem_copy>:                         -/
-- 1/7 (0x8e0#64, 0x14000004#32),  /- b   8f0 <loop_test>      -/
theorem program.step_8e0_8f0_of_wellformed (s sn : ArmState)
    (hs : WellFormedAtPc s 0x8e0)
    (hstep : Stepped s sn) :
    Step_8e0_8f0 s sn := by
  obtain ⟨h_program, h_pc, h_err, h_sp_aligned⟩ := hs
  have := program.stepi_eq_0x8e0 h_program h_pc h_err
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor <;> simp only [*, cut, state_simp_rules, minimal_theory, bitvec_rules, memory_rules]
  · constructor <;> simp only [*, cut, state_simp_rules, minimal_theory, bitvec_rules, memory_rules]
  · decide

structure Step_8e4_8e8 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8e8 : Prop where
  h_x1 : snext.x1 = scur.x1 + 0x10#64
  h_mem : snext.mem = scur.mem
  h_q4 : snext.q4 = scur[scur.x1, 16]
  h_x0 : snext.x0 = scur.x0
  h_x2 : snext.x2 = scur.x2

def Step_8e4_8e8.h_cut (h : Step_8e4_8e8 scur snext) : cut snext = false := by
  have h_pc := h.toWellFormedAtPc.h_pc
  simp [h_pc, cut]
  decide

-- 2/7 (0x8e4#64, 0x3cc10424#32),  /- ldr q4, [x1], #16        -/
theorem program.step_8e4_8e8_of_wellformed_of_stepped (scur snext : ArmState)
    (hscur : WellFormedAtPc scur 0x8e4)
    (hstep : Stepped scur snext) : Step_8e4_8e8 scur snext := by
  obtain h_program := hscur.h_program
  obtain h_pc := hscur.h_pc
  obtain h_err := hscur.h_err
  obtain h_sp_aligned := hscur.h_sp_aligned

  have := program.stepi_eq_0x8e4 h_program h_pc h_err
  simp [BitVec.extractLsb] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor <;> simp only [*, cut, state_simp_rules, minimal_theory, bitvec_rules]
  · constructor <;> simp [*, state_simp_rules, minimal_theory, BitVec.extractLsb]

-- 3/7 (0x8e8#64, 0x3c810444#32),  /- str q4, [x2], #16        -/
structure Step_8e8_8ec (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8ec : Prop where
  h_x2 : snext.x2 = scur.x2 + 0x10#64
  h_mem : snext.mem = scur.mem.write_bytes 16 scur.x2 scur.q4
  h_x0 : snext.x0 = scur.x0
  h_x1 : snext.x1 = scur.x1
  h_q4 : snext.q4 = scur.q4

def Step_8e8_8ec.h_cut (h : Step_8e8_8ec scur snext) : cut snext = false := by
  have h_pc := h.toWellFormedAtPc.h_pc
  simp [h_pc, cut]
  decide

theorem program.step_8e8_8ec_of_wellformed (scur snext : ArmState)
    (hscur : WellFormedAtPc scur 0x8e8)
    (hstep : Stepped scur snext) : Step_8e8_8ec scur snext := by
  obtain h_program := hscur.h_program
  obtain h_pc := hscur.h_pc
  obtain h_err := hscur.h_err
  obtain h_sp_aligned := hscur.h_sp_aligned

  have := program.stepi_eq_0x8e8 h_program h_pc h_err
  simp [BitVec.extractLsb] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]
  · simp only [ArmState.x2, BitVec.ofNat_eq_ofNat, ne_eq, reduceCtorEq, not_false_eq_true,
    r_of_w_different, r_of_w_same, this]
  · rw [this]
    simp [state_simp_rules, memory_rules]
  · simp only [ArmState.x0, BitVec.ofNat_eq_ofNat, ne_eq, reduceCtorEq, not_false_eq_true,
    r_of_w_different, StateField.GPR.injEq, BitVec.reduceEq, r_of_write_mem_bytes, this]
  · simp only [ArmState.x1, BitVec.ofNat_eq_ofNat, ne_eq, reduceCtorEq, not_false_eq_true,
    r_of_w_different, StateField.GPR.injEq, BitVec.reduceEq, r_of_write_mem_bytes, this]
  · simp only [ArmState.q4, BitVec.ofNat_eq_ofNat, ne_eq, reduceCtorEq, not_false_eq_true,
    r_of_w_different, StateField.GPR.injEq, BitVec.reduceEq, r_of_write_mem_bytes, this]


-- 4/7 (0x8ec#64, 0xd1000400#32),  /- sub x0, x0, #0x1         -/
structure Step_8ec_8f0 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8f0 : Prop where
  h_x0 : snext.x0 = scur.x0 - 0x1#64
  h_mem : snext.mem = scur.mem
  h_x1 : snext.x1 = scur.x1
  h_x2 : snext.x2 = scur.x2
  h_q4 : snext.q4 = scur.q4

def Step_8ec_8f0.h_cut (h : Step_8ec_8f0 scur snext) : cut snext = false := by
  have h_pc := h.toWellFormedAtPc.h_pc
  simp [h_pc, cut]
  decide

theorem program.step_8ec_8f0_of_wellformed (scur snext : ArmState)
    (hs : WellFormedAtPc scur 0x8ec#64)
    (hstep : Stepped scur snext) : Step_8ec_8f0 scur snext := by
  obtain h_program := hs.h_program
  obtain h_pc := hs.h_pc
  obtain h_err := hs.h_err
  obtain h_sp_aligned := hs.h_sp_aligned

  have := program.stepi_eq_0x8ec h_program h_pc h_err
  simp [BitVec.extractLsb] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor <;> simp (config := { ground := true, decide := true}) [*,
      state_simp_rules, minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg, memory_rules]
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules, memory_rules]

-- 5/7 (0x8f0#64, 0xf100001f#32),  /- cmp x0, #0x0             -/
structure Step_8f0_8f4 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8f4 : Prop where
  h_mem : snext.mem = scur.mem
  h_v : snext.V = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.v
  h_c : snext.C = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.c
  h_z : snext.Z = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.z
  h_n : snext.N = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.n
  h_cut : cut snext = true
  h_x0 : snext.x0 = scur.x0
  h_x1 : snext.x1 = scur.x1
  h_x2 : snext.x2 = scur.x2
  h_q4 : snext.q4 = scur.q4

theorem program.step_8f0_8f4_of_wellformed (scur snext : ArmState)
    (hs : WellFormedAtPc scur 0x8f0#64)
    (hstep : Stepped scur snext) : Step_8f0_8f4 scur snext := by
  obtain h_program := hs.h_program
  obtain h_pc := hs.h_pc
  obtain h_err := hs.h_err
  obtain h_sp_aligned := hs.h_sp_aligned

  have := program.stepi_eq_0x8f0 h_program h_pc h_err
  simp (config := { ground := true, decide := true}) [BitVec.extractLsb,
    fst_AddWithCarry_eq_sub_neg,
    fst_AddWithCarry_eq_add] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor <;> simp [*, cut, state_simp_rules, minimal_theory, bitvec_rules]
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]


-- 6/7 (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
structure Step_8f4_8e4 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8e4 : Prop where
  h_mem : snext.mem = scur.mem
  h_x0 : snext.x0 = scur.x0
  h_x1 : snext.x1 = scur.x1
  h_x2 : snext.x2 = scur.x2
  h_q4 : snext.q4 = scur.q4

def Step_8f4_8e4.h_cut (h : Step_8f4_8e4 scur snext) : cut snext = false := by
  have h_pc := h.toWellFormedAtPc.h_pc
  simp [h_pc, cut]
  decide

theorem program.step_8f4_8e4_of_wellformed_of_z_eq_0 (scur snext : ArmState)
    (hs : WellFormedAtPc scur 0x8f4)
    (h_z : (r (StateField.FLAG PFlag.Z) scur) = 0#1)
    (hstep : Stepped scur snext) : Step_8f4_8e4 scur snext := by
  obtain h_program := hs.h_program
  obtain h_pc := hs.h_pc
  obtain h_err := hs.h_err
  obtain h_sp_aligned := hs.h_sp_aligned

  have := program.stepi_eq_0x8f4 h_program h_pc h_err
  simp (config := { ground := true, decide := true}) [BitVec.extractLsb,
    fst_AddWithCarry_eq_sub_neg,
    fst_AddWithCarry_eq_add] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor <;> solve
    | simp (config := { ground := true, decide := true}) [*,
      state_simp_rules, minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg]
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]

-- 6/7 (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
structure Step_8f4_8f8 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8f8 : Prop where
  h_mem : snext.mem = scur.mem
  h_q4 : snext.q4 = scur.q4

def Step_8f4_8f8.h_cut (h : Step_8f4_8f8 scur snext) : cut snext = true := by
  have h_pc := h.toWellFormedAtPc.h_pc
  simp [h_pc, cut]

-- 6/7 (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
theorem program.step_8f4_8f8_of_wellformed_of_z_eq_1 (scur snext : ArmState)
    (hs : WellFormedAtPc scur 0x8f4)
    (h_z : (r (StateField.FLAG PFlag.Z) scur) = 0x1#1)
    (hstep : Stepped scur snext) : Step_8f4_8f8 scur snext := by
  obtain h_program := hs.h_program
  obtain h_pc := hs.h_pc
  obtain h_err := hs.h_err
  obtain h_sp_aligned := hs.h_sp_aligned

  have := program.stepi_eq_0x8f4 h_program h_pc h_err
  simp (config := { ground := true, decide := true}) [BitVec.extractLsb,
    fst_AddWithCarry_eq_sub_neg,
    fst_AddWithCarry_eq_add] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor <;>
    simp (config := { ground := true, decide := true}) [*, state_simp_rules, h_z,
      minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg, cut]
  · constructor <;> simp [*, h_z, state_simp_rules, minimal_theory, bitvec_rules, cut]

end CutTheorems

section PartialCorrectness

-- set_option skip_proof.skip true in
theorem Memcpy.extracted_2 (s0 si : ArmState)
  (h_si_x0_nonzero : si.x0 ≠ 0)
  (h_s0_x1 : s0.x1 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x1 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)))
  (h_s0_x2 : s0.x2 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x2 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)))
  (h_assert_1 : si.x0 ≤ s0.x0) (h_assert_3 : si.x1 = s0.x1 + 0x10#64 * (s0.x0 - si.x0))
  (h_assert_4 : si.x2 = s0.x2 + 0x10#64 * (s0.x0 - si.x0))
  (h_assert_6 :
    ∀ (n : Nat) (addr : BitVec 64),
      mem_separate' s0.x2 (0x10#64 * (s0.x0 - si.x0)).toNat addr n →
        Memory.read_bytes n addr si.mem = Memory.read_bytes n addr s0.mem)
  (h_assert_5 :
    ∀ (i : BitVec 64),
      i < s0.x0 - si.x0 →
        Memory.read_bytes 16 (s0.x2 + 0x10#64 * i) si.mem = Memory.read_bytes 16 (s0.x1 + 0x10#64 * i) s0.mem)
  (h_pre_1 : mem_separate' s0.x1 (s0.x0.toNat * 16) s0.x2 (s0.x0.toNat * 16))
  -- (h_pre_6 : 16 * s0.x0.toNat < 2 ^ 64)
  (n : Nat)
  (addr : BitVec 64)
  (hsep : mem_separate' s0.x2 (0x10#64 * (s0.x0 - (si.x0 - 0x1#64))).toNat addr n) :
  Memory.read_bytes n addr
      (Memory.write_bytes 16 (s0.x2 + 0x10#64 * (s0.x0 - si.x0))
        (Memory.read_bytes 16 (s0.x1 + 0x10#64 * (s0.x0 - si.x0)) si.mem) si.mem) =
    Memory.read_bytes n addr s0.mem := by
  have h_le : (s0.x0 - (si.x0 - 0x1#64)).toNat ≤ s0.x0.toNat := by bv_omega
  have h_upper_bound := hsep.hb.omega_def
  have h_upper_bound₂ := h_pre_1.hb.omega_def
  have h_upper_bound₃ := hsep.ha.omega_def
  have h_width_lt : (0x10#64).toNat * (s0.x0 - (si.x0 - 0x1#64)).toNat < 2 ^ 64 := by
    have := mem_separate'.len_le h_pre_1
    bv_omega
  rw [Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate']
  · rw [h_assert_6]
    apply mem_separate'.of_le_size hsep
    rw [BitVec.toNat_mul_of_lt (by skip_proof bv_omega)]
    rw [BitVec.toNat_mul_of_lt]
    · skip_proof bv_omega
    · skip_proof omega
  · apply mem_separate'.symm
    apply mem_separate'.of_subset'_of_subset' hsep
    · apply mem_subset'.of_omega
      refine ⟨?_, ?_, ?_, ?_⟩ <;> skip_proof bv_omega
    · apply mem_subset'_refl hsep.hb

-- set_option skip_proof.skip true in
set_option maxHeartbeats 999999 in
theorem Memcpy.extracted_0 (s0 si : ArmState)
  (h_si_x0_nonzero : si.x0 ≠ 0)
  (h_s0_x1 : s0.x1 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x1 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)))
  (h_s0_x2 : s0.x2 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x2 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)))
  (h_assert_1 : si.x0 ≤ s0.x0)
  (h_assert_3 : si.x1 = s0.x1 + 0x10#64 * (s0.x0 - si.x0))
  (h_assert_4 : si.x2 = s0.x2 + 0x10#64 * (s0.x0 - si.x0))
  (h_assert_6 :
    ∀ (n : Nat) (addr : BitVec 64),
      mem_separate' s0.x2 (0x10#64 * (s0.x0 - si.x0)).toNat addr n →
        Memory.read_bytes n addr si.mem = Memory.read_bytes n addr s0.mem)
  (h_assert_5 :
    ∀ (i : BitVec 64),
      i < s0.x0 - si.x0 →
        Memory.read_bytes 16 (s0.x2 + 0x10#64 * i) si.mem = Memory.read_bytes 16 (s0.x1 + 0x10#64 * i) s0.mem)
  (h_pre_1 : mem_separate' s0.x1 (s0.x0.toNat * 16) s0.x2 (s0.x0.toNat * 16)) (h_pre_2 : r StateField.PC s0 = 0x8e0#64)
  (h_pre_6 : 16 * s0.x0.toNat < 2 ^ 64)
  :
  (∀ (i : BitVec 64),
      i < s0.x0 - (si.x0 - 0x1#64) →
        Memory.read_bytes 16 (s0.x2 + 0x10#64 * i)
            (Memory.write_bytes 16 (s0.x2 + 0x10#64 * (s0.x0 - si.x0))
              (Memory.read_bytes 16 (s0.x1 + 0x10#64 * (s0.x0 - si.x0)) si.mem) si.mem) =
          Memory.read_bytes 16 (s0.x1 + 0x10#64 * i) s0.mem) ∧
    ∀ (n : Nat) (addr : BitVec 64),
      mem_separate' s0.x2 (0x10#64 * (s0.x0 - (si.x0 - 0x1#64))).toNat addr n →
        Memory.read_bytes n addr
            (Memory.write_bytes 16 (s0.x2 + 0x10#64 * (s0.x0 - si.x0))
              (Memory.read_bytes 16 (s0.x1 + 0x10#64 * (s0.x0 - si.x0)) si.mem) si.mem) =
          Memory.read_bytes n addr s0.mem := by
  apply And.intro
  · intros i hi
    have h_subset_2 : mem_subset' s0.x2 (0x10#64 * (s0.x0 - si.x0)).toNat s0.x2 (s0.x0.toNat * 16) := by
      skip_proof simp_mem
    have h_subset_1 : mem_subset' (s0.x1 + 0x10#64 * (s0.x0 - si.x0)) 16 s0.x1 (s0.x0.toNat * 16) := by
      skip_proof {
        simp only [show 0x10#64 * (s0.x0 - si.x0) = (s0.x0 - si.x0) * 0x10#64 by bv_omega]
        apply mem_subset'.of_offset
        · decide
        · bv_omega
        · simp_mem
        · rfl
      }
    have icases : i = s0.x0 - si.x0 ∨ i < s0.x0 - si.x0 := by skip_proof bv_omega
    have s2_sum_inbounds := h_pre_1.hb.omega_def
    have i_sub_x0_mul_16 : 16 * i.toNat < 16 * s0.x0.toNat := by skip_proof bv_omega

    rcases icases with hi | hi
    · subst hi
      rw [Memory.read_bytes_write_bytes_eq_of_mem_subset']
      · simp [bitvec_rules]
        rw [h_assert_6]
        · apply mem_separate'.symm
          apply mem_separate'.of_subset'_of_subset' h_pre_1 h_subset_1 h_subset_2
      · apply mem_subset'_refl
        have h_s0_x2_legal := h_pre_1.hb
        have h_s0_sub_si_small : s0.x0 - si.x0 ≤ s0.x0 := by skip_proof bv_omega
        skip_proof simp_mem

    · rw [Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate']
      · apply h_assert_5 _ hi
      · constructor
        · skip_proof simp_mem
        · skip_proof simp_mem
        · left
          skip_proof {
            have s2_sum_inbounds := h_pre_1.hb.omega_def
            have i_sub_x0_mul_16 : 16 * i.toNat < 16 * s0.x0.toNat := by skip_proof bv_omega
            rw [BitVec.toNat_add_eq_toNat_add_toNat (by bv_omega)]
            rw [BitVec.toNat_add_eq_toNat_add_toNat (by bv_omega)]
            rw [BitVec.toNat_mul_of_lt (by bv_omega)]
            rw [BitVec.toNat_mul_of_lt (by bv_omega)]
            rw [BitVec.toNat_sub_of_lt (by bv_omega)]
            bv_omega
          }
  · intros n addr hsep
    apply Memcpy.extracted_2 <;> assumption
theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_assertions
  case v1 =>
    intro s0 h_pre
    have {..} := h_pre
    simp only [Spec.pre, pre, BitVec.ofNat_eq_ofNat, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, Spec'.assert, assert] at h_pre ⊢
    simp only [h_pre, and_self]
    simp only [and_self, *]
  case v2 =>
    intro sf h_exit
    simp only [Spec.exit, Spec'.cut, cut, exit] at h_exit ⊢
    simp only [h_exit, BitVec.reduceEq, decide_False, Bool.or_self, decide_True, Bool.or_true]
  case v3 =>
    intro s0 sf h_assert h_exit
    simp [Spec'.assert, Spec.exit, Spec.post, post, exit,
      assert] at h_assert h_exit ⊢
    simp [h_exit] at h_assert ⊢
    simp only [h_assert, and_self, and_true]
    obtain ⟨h_pre, h_mem₁, h_mem₂, h_err, h_program, h_sp_aligned⟩ := h_assert
    constructor
    · exact h_mem₁
    · exact h_mem₂
  case v4 =>
    intro s0 si h_assert h_exit
    simp only [Spec'.assert, assert, post, Nat.reduceMul, BitVec.ofNat_eq_ofNat, id_eq,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Spec.exit, exit] at h_assert h_exit ⊢
    obtain ⟨h_pre, h_assert⟩ := h_assert
    split at h_assert
    case h_1 pc h_si =>
      subst h_assert
      simp [show (Sys.run si 1 = Sys.next si) by rfl]
      name h_s1_next_si : s1 := Sys.next si
      have h_si_wellformed : WellFormedAtPc si 2272 := by
        have {..} := h_pre
        constructor <;> assumption
      have step_8e0_8f0 := program.step_8e0_8f0_of_wellformed si s1 h_si_wellformed (.of_next h_s1_next_si)
      rw [Correctness.snd_cassert_of_not_cut (by simp [Spec'.cut, h_s1_next_si, step_8e0_8f0.h_cut])];
      simp only [Nat.zero_add]
      name h_s2_next_s1 : s2 := Sys.next s1

      have step_8f0_8f4 := program.step_8f0_8f4_of_wellformed s1 s2  step_8e0_8f0.toWellFormedAtPc (.of_next h_s2_next_s1)
      rw [Correctness.snd_cassert_of_cut (by simp [Spec'.cut, h_s2_next_s1, step_8f0_8f4.h_cut])];
      simp only [Spec'.assert, assert, h_pre,
        BitVec.ofNat_eq_ofNat, loop_inv, Nat.reduceMul, id_eq, true_and]
      simp only [step_8f0_8f4.h_pc, BitVec.ofNat_eq_ofNat, Nat.reducePow]
      simp only [Nat.reducePow, step_8f0_8f4.h_err, step_8f0_8f4.h_program,
        step_8f0_8f4.h_sp_aligned, and_self, and_true]
      have h_x0 : s2.x0 ≤ si.x0  := by
        simp only [step_8f0_8f4.h_x0, step_8e0_8f0.h_x0]
        simp only [BitVec.le_def, Nat.le_refl]
      simp only [h_x0, true_and]

      have h_s2_z : (r (StateField.FLAG PFlag.Z) s2 = 0x1#1 ↔ s2.x0 = 0x0#64) := by
        simp only [step_8f0_8f4.h_z, step_8f0_8f4.h_x0]
        apply zero_iff_z_eq_one
      simp only [h_s2_z, true_and]

      have h_s2_x1 : s2.x1 = si.x1 + 0x10#64 * (si.x0 - s2.x0) := by
        simp only [step_8f0_8f4.h_x1, step_8e0_8f0.h_x1]
        simp only [step_8f0_8f4.h_x0, step_8e0_8f0.h_x0]
        simp only [BitVec.sub_self, BitVec.reduceMul, BitVec.add_zero]
      simp only [h_s2_x1, true_and]

      have h_s2_x2 : s2.x2 = si.x2 + 0x10#64 * (si.x0 - s2.x0) := by
        simp only [step_8f0_8f4.h_x2, step_8e0_8f0.h_x2]
        simp only [step_8f0_8f4.h_x0, step_8e0_8f0.h_x0]
        simp only [BitVec.sub_self, BitVec.reduceMul, BitVec.add_zero]
      simp only [h_s2_x2, true_and]

      constructor
      · intro i hi
        rw [step_8f0_8f4.h_x0, step_8e0_8f0.h_x0] at hi
        simp at hi
        exfalso
        simp [BitVec.lt_def] at hi -- i < 0
      · intros n addr h_mem_sep
        simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes]
        rw [step_8f0_8f4.h_mem]
        rw [step_8e0_8f0.h_mem]
    case h_2 pc h_si =>
      simp [show (Sys.run si 1 = Sys.next si) by rfl]
      name h_s1_next_si : s1 := Sys.next si
      have si_well_formed : WellFormedAtPc si 0x8f4#64 := by
        simp [loop_inv] at h_assert
        constructor <;> try simp [*, state_simp_rules]

      have h_si_x0 := h_assert.r_z_eq_zero_iff_x_eq_0
      by_cases hz : r (StateField.FLAG PFlag.Z) si = 0x1#1
      · have step :=
          program.step_8f4_8f8_of_wellformed_of_z_eq_1
            si s1 si_well_formed hz (Stepped.of_next h_s1_next_si)
        rw [Correctness.snd_cassert_of_cut (by simp [Spec'.cut, Sys.next, h_s1_next_si,  step.h_cut])];
        simp only [Spec'.assert, assert, h_pre, step.h_pc, BitVec.ofNat_eq_ofNat, post,
          Nat.reduceMul, id_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          true_and]
        have h_si_x0_eq_zero := h_si_x0.mp hz
        constructor
        · intros i hi
          rw [loop_inv] at h_assert
          have h_mem := h_assert.right.right.right.right.left
          simp only [h_si_x0_eq_zero, BitVec.sub_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
            id_eq] at h_mem
          specialize (h_mem i hi)
          rw [← h_mem]
          simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, step.h_mem]
        · constructor
          · intros n addr
            intros h_sep
            simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, step.h_mem]
            obtain ⟨h_s0_mem₁, h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned⟩ := h_pre
            obtain ⟨h_si_x0, h_si_Z, h_si_x1, h_si_x2, h_si_read_overlap, h_si_read_sep, h_wellformed⟩ := h_assert
            simp only [memory_rules] at h_si_read_sep
            rw [h_si_read_sep]
            rw [h_si_x0_eq_zero]
            skip_proof simp_mem -- nice!
          · simp only [step.h_err, step.h_program, step.h_sp_aligned, and_self]
      · have step_8f4_8e4 :=
          program.step_8f4_8e4_of_wellformed_of_z_eq_0 si s1 si_well_formed
          (BitVec.eq_zero_iff_neq_one.mp hz)
          (Stepped.of_next h_s1_next_si)
        rw [Correctness.snd_cassert_of_not_cut (by simp only [Spec'.cut, step_8f4_8e4.h_cut])];
        simp only [Nat.zero_add]

        name h_s2_next_s1 : s2 := Sys.next s1
        have step_8e4_8e8 :=
          program.step_8e4_8e8_of_wellformed_of_stepped s1 s2 step_8f4_8e4.toWellFormedAtPc (.of_next h_s2_next_s1)
        rw [Correctness.snd_cassert_of_not_cut (by simp only [Spec'.cut, step_8e4_8e8.h_cut])];
        simp only [Nat.reduceAdd]

        name h_s3_next_s2 : s3 := Sys.next s2
        have step_8e8_8ec :=
          program.step_8e8_8ec_of_wellformed s2 s3 step_8e4_8e8.toWellFormedAtPc (.of_next h_s3_next_s2)
        rw [Correctness.snd_cassert_of_not_cut (by simp only [Spec'.cut, step_8e8_8ec.h_cut])];
        simp only [Nat.reduceAdd]

        name h_s4_next_s3 : s4 := Sys.next s3
        have step_8ec_8f0 :=
          program.step_8ec_8f0_of_wellformed s3 s4 step_8e8_8ec.toWellFormedAtPc (.of_next h_s4_next_s3)
        rw [Correctness.snd_cassert_of_not_cut (by simp only [Spec'.cut, step_8ec_8f0.h_cut])];
        simp only [Nat.reduceAdd]

        name h_s5_next_s4 : s5 := Sys.next s4
        have step_8f0_8f4 :=
          program.step_8f0_8f4_of_wellformed s4 s5 step_8ec_8f0.toWellFormedAtPc (.of_next h_s5_next_s4)
        rw [Correctness.snd_cassert_of_cut (by simp only [Spec'.cut, step_8f0_8f4.h_cut])];
        simp only [Spec'.assert, assert, h_pre, step_8f0_8f4.h_pc, BitVec.ofNat_eq_ofNat, loop_inv,
          Nat.reduceMul, id_eq, Nat.reducePow, true_and]
        simp only [loop_inv, BitVec.ofNat_eq_ofNat, Nat.reduceMul, id_eq, Nat.reducePow] at h_assert
        have h_s5_x0 : s5.x0 = si.x0 - 0x1#64  := by
            rw [step_8f0_8f4.h_x0,
            step_8ec_8f0.h_x0,
            step_8e8_8ec.h_x0,
            step_8e4_8e8.h_x0, step_8f4_8e4.h_x0]
        have h_s4_x0 : s4.x0 = si.x0 - 0x1#64 := by
          rw [step_8ec_8f0.h_x0,
            step_8e8_8ec.h_x0,
            step_8e4_8e8.h_x0, step_8f4_8e4.h_x0]
        have h_si_x0_nonzero : si.x0 ≠ 0 := by
          intro hcontra
          have := h_si_x0.mpr hcontra
          skip_proof contradiction

        have h_s5_x1 : s5.x1 = si.x1 + 0x10#64 := by
          rw [step_8f0_8f4.h_x1,
            step_8ec_8f0.h_x1,
            step_8e8_8ec.h_x1,
            step_8e4_8e8.h_x1, step_8f4_8e4.h_x1]

        have h_s5_x2 : s5.x2 = si.x2 + 0x10#64 := by
          rw [step_8f0_8f4.h_x2,
            step_8ec_8f0.h_x2,
            step_8e8_8ec.h_x2,
            step_8e4_8e8.h_x2, step_8f4_8e4.h_x2]

        have h_si_x1 :  si.x1 = s0.x1 + 0x10#64 * (s0.x0 - si.x0) := by
          simp only [h_assert]

        have h_si_x2 : si.x2 = s0.x2 + 0x10#64 * (s0.x0 - si.x0) := by
          simp only [h_assert]

        have h_s5_z : (r (StateField.FLAG PFlag.Z) s5 = 0x1#1 ↔ si.x0 - 0x1#64 = 0x0#64) := by
          simp only [step_8f0_8f4.h_z, h_s4_x0]
          apply zero_iff_z_eq_one
        simp only [h_s5_z]

        simp only [show s5.x0 ≤ s0.x0 by bv_omega, true_and]
        rw [h_s5_x0, h_s5_x1, h_si_x1]
        have h_s0_x1 : s0.x1 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x1 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)) := by
          rw [show s0.x0 - (si.x0 - 0x1#64) = (s0.x0 - si.x0) + 0x1#64 by skip_proof bv_omega,
            BitVec.BitVec.mul_add,
            BitVec.add_assoc, BitVec.mul_one]
        simp only [h_s0_x1, true_and]

        rw [h_s5_x2, h_si_x2]
        have h_s0_x2 : s0.x2 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x2 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)) := by
          rw [show s0.x0 - (si.x0 - 0x1#64) = (s0.x0 - si.x0) + 0x1#64 by skip_proof bv_omega,
            BitVec.BitVec.mul_add]
          skip_proof bv_omega
        simp only [h_s0_x2, true_and]
        simp only [step_8f0_8f4.h_err,
          step_8f0_8f4.h_program,
          step_8f0_8f4.h_sp_aligned,
          and_self,
          and_true]
        simp only [memory_rules]
        rw [step_8f0_8f4.h_mem]
        rw [step_8ec_8f0.h_mem]
        rw [step_8e8_8ec.h_mem]
        rw [step_8e4_8e8.h_mem]
        rw [step_8f4_8e4.h_mem]
        rw [step_8e4_8e8.h_x2]
        rw [step_8f4_8e4.h_x2]
        rw [step_8e4_8e8.h_q4]
        rw [h_si_x2]
        obtain ⟨h_assert_1, h_assert_2, h_assert_3, h_assert_4, h_assert_5, h_assert_6, h_assert_7⟩ := h_assert
        simp only [memory_rules]
        simp only [step_8f4_8e4.h_mem]
        simp only [step_8f4_8e4.h_x1]
        rw [h_si_x1]
        simp only [memory_rules] at h_assert_6 h_assert_5
        have ⟨h_pre_1, h_pre_2, h_pre_3, h_pre_4, h_pre_5, h_pre_6⟩ := h_pre
        apply Memcpy.extracted_0 <;> assumption
    case h_3 pc h_si =>
      contradiction
    case h_4 pc h_si =>
      apply False.elim h_assert
/--
info: 'Memcpy.partial_correctness' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms partial_correctness

end PartialCorrectness

theorem termination :
  Termination ArmState := by
  simp [Termination, Spec.pre, Spec.exit, exit,
        state_simp_rules, bitvec_rules, minimal_theory]
  intro s h_pre
  sorry

end Memcpy
