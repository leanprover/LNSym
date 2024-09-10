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
  | start => -- First instruction
    si = s0
  | loop_guard => -- Loop guard
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


structure WellFormedAtPc (s : ArmState) (pc : BitVec 64) : Prop where
  h_program : s.program = program
  h_pc : r StateField.PC s = pc
  h_err : r StateField.ERR s = StateError.None
  h_sp_aligned : CheckSPAlignment s


structure Stepped (s sn : ArmState) where
  h_step : sn = stepi s

abbrev Step_8e0_ef0 (s : ArmState) := WellFormedAtPc s 0x8e0

--  /- 00000000000008e0 <mem_copy>:                         -/
-- 1/7 (0x8e0#64, 0x14000004#32),  /- b   8f0 <loop_test>      -/
theorem program.stepi_0x8e0_cut (s sn : ArmState)
    (hs : Step_8e0_ef0 s)
    (hstep : Stepped s sn) :
    WellFormedAtPc sn 0x8f0 := by
  obtain ⟨h_program, h_pc, h_err, h_sp_aligned⟩ := hs
  have := program.stepi_eq_0x8e0 h_program h_pc h_err
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor <;> simp only [*, state_simp_rules, minimal_theory, bitvec_rules]

/-
  w StateField.PC 0x8e8#64
    (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
      (w (StateField.SFP 0x4#5)
        (BitVec.zeroExtend 128
          (read_mem_bytes (8 <<< (BitVec.extractLsb 1 1 0x3#2 ++ 0x0#2).toNat / 8) (r (StateField.GPR 0x1#5) s) s))
-/
structure Step_8e4_8e8 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8e8 : Prop where
  h_x1 : snext.x1 = scur.x1 + 0x10#64
  h_mem : snext.mem = scur.mem
  h_q4 : snext.q4 = scur[scur.x1, 16]

-- 2/7 (0x8e4#64, 0x3cc10424#32),  /- ldr q4, [x1], #16        -/
theorem program.stepi_0x8e4_cut (scur snext : ArmState)
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
  constructor <;>  simp only [*, state_simp_rules, minimal_theory, bitvec_rules]
  · constructor <;> simp? [*, state_simp_rules, minimal_theory, BitVec.extractLsb]

-- 3/7 (0x8e8#64, 0x3c810444#32),  /- str q4, [x2], #16        -/
structure Step_8e8_8ec (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8ec : Prop where
  h_x2 : snext.x2 = scur.x2 + 0x10#64
  h_mem : snext.mem = scur.mem.write_bytes 16 scur.x0 scur.q4

theorem program.stepi_0x8e8_cut (sprev scur snext : ArmState)
    (hs : Step_8e4_8e8 sprev scur)
    (hstep : Stepped scur snext) : Step_8e8_8ec scur snext := by
  obtain h_program := hs.h_program
  obtain h_pc := hs.h_pc
  obtain h_err := hs.h_err
  obtain h_sp_aligned := hs.h_sp_aligned

  have := program.stepi_eq_0x8e8 h_program h_pc h_err
  simp [BitVec.extractLsb] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]
  · simp? [*, state_simp_rules, minimal_theory, BitVec.extractLsb]

-- 4/7 (0x8ec#64, 0xd1000400#32),  /- sub x0, x0, #0x1         -/
structure Step_8ec_8f0 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8f0 : Prop where
  h_x0 : snext.x0 = scur.x0 - 0x1#64
  h_mem : snext.mem = scur.mem

theorem program.stepi_0x8ec_cut (sprev scur snext : ArmState)
    (hs : Step_8e8_8ec sprev scur)
    (hstep : Stepped scur snext) : Step_8ec_8f0 scur snext := by
  obtain h_program := hs.h_program
  obtain h_pc := hs.h_pc
  obtain h_err := hs.h_err
  obtain h_sp_aligned := hs.h_sp_aligned

  have := program.stepi_eq_0x8ec h_program h_pc h_err
  simp [BitVec.extractLsb] at this
  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]
  · simp? (config := { ground := true, decide := true}) [*,
      state_simp_rules, minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg]

-- 5/7 (0x8f0#64, 0xf100001f#32),  /- cmp x0, #0x0             -/
structure Step_8f0_8f4 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8f4 : Prop where
  h_mem : snext.mem = scur.mem
  h_v : snext.V = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.v
  h_c : snext.C = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.c
  h_z : snext.Z = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.z
  h_n : snext.N = (AddWithCarry scur.x0 0xffffffffffffffff#64 0x1#1).snd.n


theorem program.stepi_0x8f0_cut (sprev scur snext : ArmState)
    (hs : Step_8ec_8f0 sprev scur)
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
  constructor
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]
  · simp? (config := { ground := true, decide := true}) [*,
      state_simp_rules, minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg]

-- 6/7 (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
structure Step_8f4_8e4 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8e4 : Prop where
  h_mem : snext.mem = scur.mem
  -- h_pc : snext.pc = 0x8e4#64

theorem program.stepi_0x8f4_0x834_cut (sprev scur snext : ArmState)
    (hs : Step_8f0_8f4 sprev scur)
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
  constructor
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]
  · simp? (config := { ground := true, decide := true}) [*,
      state_simp_rules, minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg]

-- 6/7 (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
structure Step_8f4_8f8 (scur : ArmState) (snext : ArmState) extends WellFormedAtPc snext 0x8f8 : Prop where
  h_mem : snext.mem = scur.mem
  -- h_pc : snext.pc = 0x8e4#64

theorem program.stepi_0x8f4_0x8f8_cut (sprev scur snext : ArmState)
    (hs : Step_8f0_8f4 sprev scur)
    (h_z : (r (StateField.FLAG PFlag.Z) scur) = 1#1)
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
  constructor
  · constructor <;> simp [*, state_simp_rules, minimal_theory, bitvec_rules]
  · simp? (config := { ground := true, decide := true}) [*,
      state_simp_rules, minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg]


-- 7/7 (0x8f8#64, 0xd65f03c0#32)   /- ret                      -/
structure Step_8f8_ret (scur : ArmState) (snext : ArmState) : Prop where
  h_mem : snext.mem = scur.mem

theorem program.stepi_0x8f8_cut (sprev scur snext : ArmState)
    (hs : Step_8f4_8f8 sprev scur)
    (hstep : Stepped scur snext) : Step_8f8_ret scur snext := by
  obtain h_program := hs.h_program
  obtain h_pc := hs.h_pc
  obtain h_err := hs.h_err
  obtain h_sp_aligned := hs.h_sp_aligned

  have := program.stepi_eq_0x8f8 h_program h_pc h_err
  simp (config := { ground := true, decide := true}) [BitVec.extractLsb,
    fst_AddWithCarry_eq_sub_neg,
    fst_AddWithCarry_eq_add] at this

  obtain ⟨h_step⟩ := hstep
  subst h_step
  constructor
  · simp? (config := { ground := true, decide := true}) [*,
      state_simp_rules, minimal_theory, BitVec.extractLsb, fst_AddWithCarry_eq_sub_neg]

end CutTheorems

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
