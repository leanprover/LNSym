/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

Experimental: Use the Correctness module to prove that this program
computes the maximum of two numbers.
-/
import Arm
import Tactics.CSE
import Tactics.Sym
import Tactics.Rename
import Tactics.Name
import Tactics.ClearNamed
import Tactics.StepThms
import Correctness.ArmSpec
import Proofs.Experiments.Max.MaxProgram
import Arm.Insts.Common
import Arm.Memory.SeparateAutomation
import Arm.Syntax

namespace MaxTandem
open Max


section PC

/--# We define scoped notation for our cutpoint PCs to use in pattern matching. -/

scoped notation "entry_start" => 0x894#64
scoped notation "then_start" => 0x8b0#64
scoped notation "else_start" => 0x8bc#64
scoped notation "merge_end" => 0x8cc#64


open ArmStateNotation

def pcs : List (BitVec 64) := [
  entry_start,
  then_start,
  else_start,
  merge_end
  ]

end PC

def cut (s : ArmState) : Bool := decide (read_pc s ∈ pcs)

section Invariants

/-- Precondition for the correctness of the Add program. -/
def pre (s : ArmState) : Prop :=
  read_pc s = entry_start ∧
  s.program = program ∧
  read_err s = StateError.None ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment s ∧
  s.sp ≥ 32 ∧
  mem_legal' s.sp 80 -- TODO: find the correct smallest bound we need here.

/-- Specification function. -/
def spec (x0 x1 : BitVec 64) : BitVec 64 :=
  if BitVec.slt (x0.zeroExtend 32)  (x1.zeroExtend 32)
  then (x1.zeroExtend 32).zeroExtend 64
  else (x0.zeroExtend 32).zeroExtend 64

def post (s0 sf : ArmState) : Prop :=
  sf.x0 = BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (spec s0.x0 s0.x1)) ∧
  read_pc sf = 0x8cc#64 ∧
  read_err sf = StateError.None ∧
  sf.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment sf

def entry_start_inv (s0 si : ArmState) : Prop := si = s0

/-- Invariant right at the conditional branch -/
def entry_end_inv (s0 si : ArmState): Prop :=
  read_err si = .None ∧
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si ∧
  si[s0.sp - 32#64 + 12#64, 4] = s0.x0.zeroExtend 32 ∧
  si[s0.sp - 32#64 + 8#64, 4] = s0.x1.zeroExtend 32 ∧
  si.sp = s0.sp - 32#64

/-!
Notice the pattern: The invariant after the conditional branch
is the invariant before the conditional branch, plus what the conditional branch taught us
-/

def then_start_inv (s0 si : ArmState) : Prop :=
  entry_end_inv s0 si ∧
  ¬ ((BitVec.zeroExtend 32 s0.x0).sle (BitVec.zeroExtend 32 s0.x1) = true)

def else_start_inv (s0 si : ArmState) : Prop :=
  entry_end_inv s0 si ∧
  ((BitVec.zeroExtend 32 s0.x0).sle (BitVec.zeroExtend 32 s0.x1) = true)

def exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = 0x8cc#64

end Invariants


def assert (s0 si : ArmState) : Prop :=
  pre s0 ∧
  -- Using `match` is preferable to `if` for the `split` tactic (and for readability).
  match (read_pc si) with
  | entry_start => entry_start_inv s0 si
  | then_start => then_start_inv s0 si
  | else_start => else_start_inv s0 si
  | merge_end => post s0 si -- @bollu: why do I need an `assert` here, if it's tracked by `post`? We should change VCG.
  | _ => False

instance : Spec' ArmState where
  pre    := pre
  post   := post
  exit   := exit
  cut    := cut
  assert := assert

-------------------------------------------------------------------------------
-- Generating the program effects and non-effects

section CutTheorems

-- (FIXME) Obtain *_cut theorems for each instruction automatically.
-- 1/15: sub  sp, sp, #0x20  ;
theorem program.stepi_0x894_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x894#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x898#64 ∧
  r StateField.ERR sn = .None ∧
  (sn.x0) = (s.x0) ∧
  (sn.x1) = (s.x1) ∧
  (sn.sp) = (s.sp) - 0x20#64 ∧
  sn.mem = s.mem ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  subst h_step
  have := Max.program.stepi_eq_0x894 h_program h_pc h_err
  -- clear Decidable.rec (...)
  simp only [minimal_theory] at this
  simp_all only [run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory, pcs]
  simp only [List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
    true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]
  /- Toy automation for deciding Aligned, will be converted to a decision procedure in a follow up PR -/
  repeat first
  | simp [aligned_rules, state_simp_rules]
  | apply Aligned_BitVecSub_64_4;
  | apply Aligned_BitVecAdd_64_4;
  | apply Aligned_AddWithCarry_64_4;
  | apply Aligned_AddWithCarry_64_4'
  repeat solve
  | decide
  | bv_omega_bench
  | assumption

/--
info: 'MaxTandem.program.stepi_0x894_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x894_cut

-- 2/15: str  w0, [sp, #12]  ; sp[12] = w0_a
set_option trace.simp_mem.info true in
theorem program.stepi_0x898_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x898#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_legal : mem_legal' s.sp 40)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x89c#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  sn[(sn.sp) + 8#64, 4] = s[s.sp + 8#64, 4] ∧
  sn[(sn.sp) + 12#64, 4] = (s.x0).truncate 32 ∧
  (sn.x0) = (s.x0) ∧
  (sn.x1) = (s.x1) ∧
  (sn.sp) = (s.sp) ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x898 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
    true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]
  simp only [memory_rules, state_simp_rules]
  simp_mem
  rfl

/--
info: 'MaxTandem.program.stepi_0x898_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x898_cut

-- 3/15: str  w1, [sp, #8]   ; sp[8] = w1_a
theorem program.stepi_0x89c_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x89c#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_legal : mem_legal' s.sp 40)
  (h_step : sn = run 1 s)
  :
  cut sn = false ∧
  sn[(sn.sp) + 8#64, 4] = (s.x1).truncate 32 ∧
  sn[(sn.sp) + 12#64, 4] = s[s.sp + 12#64, 4] ∧
  (sn.x0) = (s.x0) ∧
  (sn.x1) = (s.x1) ∧
  (sn.sp) = (s.sp) ∧
  r StateField.PC sn = 0x8a0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x89c h_program h_pc h_err
  simp only [minimal_theory, bitvec_rules] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
    true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]
  simp [memory_rules, state_simp_rules, minimal_theory]
  simp_mem
  rfl

/--
info: 'MaxTandem.program.stepi_0x89c_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x89c_cut

-- 4/15: ldr  w1, [sp, #12]  ; w1_b = sp[12]
theorem program.stepi_0x8a0_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8a0#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  sn[(sn.sp) + 8#64, 4] = s[s.sp + 8#64, 4] ∧
  sn[(sn.sp) + 12#64, 4] = s[s.sp + 12#64, 4] ∧
  sn.x0 = s.x0 ∧
  sn.x1 = BitVec.zeroExtend 64 (s[sn.sp + 12#64, 4])  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.sp = s.sp ∧
  r StateField.PC sn = 0x8a4#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x8a0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
    true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]
  done

/--
info: 'MaxTandem.program.stepi_0x8a0_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8a0_cut

-- 5/15: ldr  w0, [sp, #8]
theorem program.stepi_0x8a4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8a4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  sn[(sn.sp) + 8#64, 4] = s[s.sp + 8#64, 4] ∧
  sn[(sn.sp) + 12#64, 4] = s[s.sp + 12#64, 4] ∧
  sn.x0 = BitVec.zeroExtend 64 (s[sn.sp + 8#64, 4])  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.x1 = s.x1  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.sp = s.sp ∧
  r StateField.PC sn = 0x8a8#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x8a4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
    true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]

/--
info: 'MaxTandem.program.stepi_0x8a4_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8a4_cut

-- 6/15: cmp  w1, w0 -- | TODO: add necessary conditions
theorem program.stepi_0x8a8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8a8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x8ac#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  sn.C = (AddWithCarry (s.x1.zeroExtend 32) (~~~s.x0.zeroExtend 32) 1#1).snd.c ∧
  sn.V = (AddWithCarry (s.x1.zeroExtend 32) (~~~s.x0.zeroExtend 32) 1#1).snd.v ∧
  sn.Z = (AddWithCarry (s.x1.zeroExtend 32) (~~~s.x0.zeroExtend 32) 1#1).snd.z ∧
  sn.N = (AddWithCarry (s.x1.zeroExtend 32) (~~~s.x0.zeroExtend 32) 1#1).snd.n ∧
  sn[(sn.sp) + 8#64, 4] = s[s.sp + 8#64, 4] ∧
  sn[(sn.sp) + 12#64, 4] = s[s.sp + 12#64, 4] ∧
  sn.x0 = s.x0  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.x1 = s.x1  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.sp = s.sp ∧
  CheckSPAlignment sn ∧
  sn.mem = s.mem := by
  have := program.stepi_eq_0x8a8 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
    true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]

/--
info: 'MaxTandem.program.stepi_0x8a8_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8a8_cut

-- 7/15
theorem program.stepi_0x8ac_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8ac#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = true ∧
  r StateField.PC sn =
  (if ¬(s.N = s.V ∧ s.Z = 0#1)
  then 2236#64 -- takes the branch
  else 0x8b0#64) ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  sn[(sn.sp) + 8#64, 4] = s[s.sp + 8#64, 4] ∧
  sn[(sn.sp) + 12#64, 4] = s[s.sp + 12#64, 4] ∧
  sn.x0 = s.x0  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.x1 = s.x1  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.sp = s.sp ∧
  CheckSPAlignment sn ∧
  sn.mem = s.mem
  := by
  have := program.stepi_eq_0x8ac h_program h_pc h_err
  simp only [minimal_theory] at this
  simp only [← not_and] at *
  simp only [cut, read_pc, pcs, List.mem_cons, List.mem_singleton, Bool.decide_or, Bool.or_eq_true,
    decide_eq_true_eq, state_value]
  split
  case isTrue h =>
    have : sn = w StateField.PC (2236#64) s := by
      simp only [state_simp_rules] at h
      rw [h_step]
      simp [h] at this
      rw [← this]
      rfl
    simp [this, state_simp_rules, h_sp_aligned, h_err, h_program]
  case isFalse h =>
    /- TODO: we have too many layers of abstraction. We need to choose a simp normal form
    between `run` and `step`. -/
    have : sn = w StateField.PC (2224#64) s := by
      simp only [state_simp_rules] at h
      rw [h_step]
      simp [h] at this
      rw [← this]
      rfl
    simp [this, state_simp_rules, h_sp_aligned, h_err, h_program]

/--
info: 'MaxTandem.program.stepi_0x8ac_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8ac_cut

-- 8/15: ldr  w0, [sp, #12]
theorem program.stepi_0x8b0_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8b0#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x8b4#64 ∧
  r StateField.ERR sn = .None ∧
  sn[(sn.sp) + 8#64, 4] = s[s.sp + 8#64, 4] ∧
  sn[(sn.sp) + 12#64, 4] = s[s.sp + 12#64, 4] ∧
  sn.x0 = BitVec.zeroExtend 64 s[sn.sp + 12#64, 4]  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.x1 = s.x1  ∧ -- TODO: change notation to work on Memory, rather than ArmSTate + read_bytes
  sn.sp = s.sp ∧
  sn.program = program ∧
  sn.mem = s.mem ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8b0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true]
  simp only [List.not_mem_nil, or_self, not_false_eq_true]

/--
info: 'MaxTandem.program.stepi_0x8b0_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8b0_cut

-- 9/15 :str  w0, [sp, #28]
theorem program.stepi_0x8b4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8b4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x8b8#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  sn.x0 = s.x0 ∧
  sn[sn.sp + 28#64, 4] = sn.x0.zeroExtend 32 ∧
  sn.sp = s.sp ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8b4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true]
  simp only [List.not_mem_nil, or_self, or_false, or_true]
  simp only [not_false_eq_true]

/--
info: 'MaxTandem.program.stepi_0x8b4_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8b4_cut

-- 10/15: b  8c4
theorem program.stepi_0x8b8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8b8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  r StateField.PC sn = 0x8c4#64 ∧
  r StateField.ERR sn = .None ∧
  cut sn = false ∧ -- TODO: why do we speak about the *next* state being a cut?
  sn.program = program ∧
  sn.mem = s.mem ∧
  sn[sn.sp + 28#64, 4] = s[s.sp + 28#64, 4] ∧
  sn.sp = s.sp ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8b8 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_false, or_true]
  simp only [List.not_mem_nil, or_self, or_false, or_true]
  simp only [not_false_eq_true]
/--
info: 'MaxTandem.program.stepi_0x8b8_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8b8_cut

-- 11/15: ldr  w0, [sp, #8]
theorem program.stepi_0x8bc_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8bc#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x8c0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  -- @bollu: try and alwas write the RHS in terms of `s`, rather than `sn`.
  sn.x0 = BitVec.zeroExtend 64 (s[s.sp + 8#64, 4])  ∧
  sn.sp = s.sp ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8bc h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, or_false, or_true]
  simp only [List.not_mem_nil, or_self, or_false, or_true]
  simp only [not_false_eq_true]

/--
info: 'MaxTandem.program.stepi_0x8bc_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8bc_cut

--- 12/15: str  w0, [sp, #28]
theorem program.stepi_0x8c0_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8c0#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x8c4#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  sn[sn.sp + 28, 4] = s.x0.zeroExtend 32  ∧
  sn.sp = s.sp ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8c0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp [pcs]

  /--
info: 'MaxTandem.program.stepi_0x8c0_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8c0_cut

-- 13/15: ldr  w0, [sp, #28]
theorem program.stepi_0x8c4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8c4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  r StateField.PC sn = 0x8c8#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  sn.mem = s.mem ∧
  cut sn = false ∧
  sn.sp = s.sp ∧
  sn[sn.sp + 28#64, 4] = s[s.sp + 28#64, 4]  ∧
  sn.x0 = BitVec.zeroExtend 64 (sn[sn.sp + 28#64, 4])  ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8c4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp [pcs]

/--
info: 'MaxTandem.program.stepi_0x8c4_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8c4_cut

-- 14/15: add  sp, sp, #0x20
theorem program.stepi_0x8c8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8c8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  r StateField.PC sn = 0x8cc#64 ∧
  r StateField.ERR sn = .None ∧
  cut sn = true ∧
  sn.program = program ∧
  sn.x0 = s.x0 ∧
  sn.sp = s.sp + 0x20#64 ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8c8 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_true, true_and, false_or,
    true_or]
  apply Aligned_BitVecAdd_64_4
  · assumption
  · decide

/--
info: 'MaxTandem.program.stepi_0x8c8_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8c8_cut

end CutTheorems

/-- info: Correctness.cassert {σ : Type} [Sys σ] [Spec' σ] (s0 si : σ) (i : Nat) : Nat × Prop -/
#guard_msgs in #check Correctness.cassert

/-- info: MaxTandem.cut (s : ArmState) : Bool -/
#guard_msgs in #check cut

theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_assertions
  case v1 =>
    intro s0 h_pre
    simp only [Spec.pre] at h_pre
    have ⟨h_pre_pc, _h2⟩ := h_pre
    simp only [Spec'.assert, assert, minimal_theory]
    rw [h_pre_pc]
    constructor
    · assumption
    · rfl
  case v2 =>
    intro sf h_exit
    simp_all (config := {decide := true}) only
        [Spec.exit, exit, Spec'.cut, cut,
         state_simp_rules, minimal_theory]
  case v3 =>
    intro s0 sf h_assert h_exit
    -- (FIXME) Remove Spec.post to replicate bug where simp_all somehow
    -- aggressively makes the goal unprovable.
    -- simp_all only [Spec'.assert, Spec.exit, assert, exit, Spec.post]
    simp only [Spec'.assert, assert] at h_assert
    simp only [Spec.exit, exit] at h_exit
    -- Why do we see the hex values instead of PC notation?
    simp only [h_exit] at h_assert
    simp only [Spec.post]
    simp_all
  case v4 =>
    intro s0 si h_assert h_not_exit
    simp only [Correctness.arm_run]
    simp [Spec.exit, exit] at h_not_exit
    simp [Spec'.assert, assert, h_not_exit, minimal_theory, read_pc] at h_assert
    obtain ⟨h_pre, h_assert⟩ := h_assert
    -- have h_pre_copy : pre s0 := h_pre
    simp [pre] at h_pre
    have ⟨h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned, h_sp_geq, h_mem_legal⟩ := h_pre
    split at h_assert
    · -- Next cutpoint from 0x894#64 (1/15)
      subst si
      rename_i x h_pc
      name h_s0_run : s1 := run 1 s0
      obtain ⟨h_s1_cut, h_s1_pc, h_s1_err, h_s1_x0, h_s1_x1, h_s1_sp, _h_s1_mem, h_s1_program, h_s1_sp_aligned⟩ :=
        program.stepi_0x894_cut s0 s1 h_s0_program h_pc h_s0_err h_s0_sp_aligned h_s0_run.symm
      rw [Correctness.snd_cassert_of_not_cut h_s1_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s1 = run 1 s1 by rfl]
      clear_named [h_s0]

      -- 2/15
      name h_s1_run : s2 := run 1 s1
      obtain ⟨h_s2_cut, h_s2_pc, h_s2_err, h_s2_program, h_s2_read_sp_8, h_s2_read_sp_12, h_s2_x0, h_s2_x1, h_s2_sp, h_s2_sp_aligned⟩ :=
        program.stepi_0x898_cut s1 s2 h_s1_program h_s1_pc h_s1_err h_s1_sp_aligned (by mem_omega) h_s1_run.symm
      rw [Correctness.snd_cassert_of_not_cut h_s2_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s2 = run 1 s2 by rfl]
      replace h_s2_sp : s2.sp = (s0.sp - 32#64) := by simp_all
      replace h_s2_x0 : s2.x0 = s0.x0 := by simp_all
      replace h_s2_x1 : s2.x1 = s0.x1 := by simp_all
      replace h_s2_read_sp12 : read_mem_bytes 4 (s2.sp + 12#64) s2 = BitVec.truncate 32 s0.x0 := by simp_all
      clear_named [h_s1]

      -- 3/15
      name h_run : s3 := run 1 s2
      obtain h := program.stepi_0x89c_cut s2 s3 h_s2_program h_s2_pc h_s2_err h_s2_sp_aligned (by mem_omega) h_run.symm
      obtain ⟨h_s3_cut, h_s3_read_sp_8, h_s3_read_sp_12, h_s3_x0, h_s3_x1, h_s3_sp, h_s3_pc, h_s3_err, h_s3_program, h_s3_sp_aligned⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s3_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s3 = run 1 s3 by rfl]
      replace h_s3_x0 : s3.x0 = s0.x0 := by simp_all
      replace _h_s3_x1 : s3.x1 = s0.x1 := by simp_all
      replace h_s3_sp : s3.sp = s0.sp - 32 := by simp_all
      /- TODO: this should be s0.x0-/
      replace h_s3_read_sp12 : read_mem_bytes 4 (s3.sp + 12#64) s3 = BitVec.truncate 32 s0.x0 := by simp_all
      replace _h_s3_read_sp8 : read_mem_bytes 4 (s3.sp + 8#64) s3 = BitVec.truncate 32 s0.x1 := by simp_all
      clear_named [h_s2]

      -- 4/15
      name h_run : s4 := run 1 s3
      obtain h := program.stepi_0x8a0_cut s3 s4 h_s3_program h_s3_pc h_s3_err h_s3_sp_aligned h_run.symm
      obtain ⟨h_s4_cut, h_s4_read_sp_8, h_s4_read_sp_12, h_s4_x0, h_s4_x1, h_s4_sp, h_s4_pc, h_s4_err, h_s4_program, h_s4_sp_aligned⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s4_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s4 = run 1 s4 by rfl]
      replace h_s4_sp : s4.sp = s0.sp - 32 := by simp_all
      replace _h_s4_x0 : s4.x0 = s0.x0 := by simp_all
      replace h_s4_x1 : s4.x1 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x0) := by simp_all
      replace h_s4_sp : s4.sp = s0.sp - 32 := by simp_all
      replace h_s4_read_sp12 : read_mem_bytes 4 (s4.sp + 12#64) s4 = BitVec.truncate 32 s0.x0 := by simp_all
      replace _h_s4_read_sp8 : read_mem_bytes 4 (s4.sp + 8#64) s4 = BitVec.truncate 32 s0.x1 := by simp_all
      clear_named [h_s3]

      -- 5/15
      name h_run : s5 := run 1 s4
      obtain h := program.stepi_0x8a4_cut s4 s5 h_s4_program h_s4_pc h_s4_err h_s4_sp_aligned h_run.symm
      obtain ⟨h_s5_cut, h_s5_read_sp_8, h_s5_read_sp_12, h_s5_x0, h_s5_x1, h_s5_sp, h_s5_pc, h_s5_err, h_s5_program, h_s5_sp_aligned⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s5_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s5 = run 1 s5 by rfl]
      replace h_s5_sp : s5.sp = s0.sp - 32 := by simp_all
      replace h_s5_x0 : s5.x0 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x1) := by simp_all
      replace h_s5_x1 : s5.x1 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x0) := by simp_all
      replace h_s5_sp : s5.sp = s0.sp - 32 := by simp_all
      replace h_s5_read_sp12 : read_mem_bytes 4 (s5.sp + 12#64) s5 = BitVec.truncate 32 s0.x0 := by simp_all
      replace _h_s5_read_sp8 : read_mem_bytes 4 (s5.sp + 8#64) s5 = BitVec.truncate 32 s0.x1 := by simp_all
      clear_named [h_s4]

      -- 6/15
      name h_run : s6 := run 1 s5
      obtain h := program.stepi_0x8a8_cut s5 s6 h_s5_program h_s5_pc h_s5_err h_s5_sp_aligned h_run.symm
      obtain ⟨h_s6_cut, h_s6_pc, h_s6_err, h_s6_program, h_s6_c, h_s6_v, h_s6_z, h_s6_n, h_s6_read_sp_8, h_s6_read_sp_12, h_s6_x0, h_s6_x1, h_s6_sp, h_s6_sp_aligned, _h_s6_mem⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s6_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s6 = run 1 s6 by rfl]
      replace h_s6_sp : s6.sp = s0.sp - 32 := by simp_all
      replace h_s6_x0 : s6.x0 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x1) := by simp_all
      replace h_s6_x1 : s6.x1 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x0) := by simp_all
      replace h_s6_sp : s6.sp = s0.sp - 32 := by simp_all
      replace h_s6_read_sp12 : read_mem_bytes 4 (s6.sp + 12#64) s6 = BitVec.truncate 32 s0.x0 := by simp_all
      replace _h_s6_read_sp8 : read_mem_bytes 4 (s6.sp + 8#64) s6 = BitVec.truncate 32 s0.x1 := by simp_all
      replace h_s6_c : s6.C = (AddWithCarry (s0.x0.zeroExtend 32) (~~~s0.x1.zeroExtend 32) 1#1).snd.c := by simp_all
      replace h_s6_n : s6.N = (AddWithCarry (s0.x0.zeroExtend 32) (~~~s0.x1.zeroExtend 32) 1#1).snd.n := by simp_all
      replace h_s6_v : s6.V = (AddWithCarry (s0.x0.zeroExtend 32) (~~~s0.x1.zeroExtend 32) 1#1).snd.v := by simp_all
      replace h_s6_z : s6.Z = (AddWithCarry (s0.x0.zeroExtend 32) (~~~s0.x1.zeroExtend 32) 1#1).snd.z := by simp_all

      clear_named [h_s5]

    -- 7/16
      name h_run : s7 := run 1 s6
      obtain h := program.stepi_0x8ac_cut s6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by simp [*])
      obtain ⟨h_s7_cut, h_s7_pc, h_s7_err, h_s7_program, h_s7_read_sp_8, h_s7_read_sp_12, h_s7_x0, h_s7_x1, h_s7_sp, h_s7_sp_aligned, _h_s7_mem⟩ := h
      rw [Correctness.snd_cassert_of_cut h_s7_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      replace h_s7_sp : s7.sp = s0.sp - 32 := by simp_all
      replace h_s7_x0 : s7.x0 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x1) := by simp_all
      replace h_s7_x1 : s7.x1 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x0) := by simp_all
      replace h_s7_sp : s7.sp = s0.sp - 32 := by simp_all
      replace h_s7_read_sp12 : read_mem_bytes 4 ((s0.sp - 32#64) + 12#64) s7 = BitVec.truncate 32 s0.x0 := by simp_all
      replace h_s7_read_sp8 : read_mem_bytes 4 ((s0.sp - 32#64) + 8#64) s7 = BitVec.truncate 32 s0.x1 := by simp_all
      have h_s7_s6_c := h_s6_c
      have h_s7_s6_n := h_s6_n
      have h_s7_s6_v := h_s6_v
      have h_s7_s6_z := h_s6_z
      clear_named [h_run, h_s6] -- TODO: I clear h_run here. Is this a good idea?
      split at h_s7_pc
      case isTrue h => -- branch taken
        simp only [Spec'.assert, assert, h_pre, read_pc, h_s7_pc, else_start_inv, read_err,
          h_s7_err, h_s7_program, h_s7_sp_aligned, entry_end_inv, Nat.reduceMul, h_s7_read_sp12,
          h_s7_read_sp8, and_self, true_and, h_s7_sp, BitVec.ofNat_eq_ofNat, true_and]
        have h_s7_sle := sle_iff_not_n_eq_v_and_z_eq_0_32 (BitVec.zeroExtend 32 s0.x0) (BitVec.zeroExtend 32 s0.x1)
        rw [← h_s7_s6_n, ← h_s7_s6_v, ← h_s7_s6_z] at h_s7_sle
        replace h_s7_sle := h_s7_sle.mp h
        simp [h_s7_sle]
        simp [h_pre, pre]
      case isFalse h =>  -- branch not taken
        simp only [Spec'.assert, assert, h_pre, read_pc, h_s7_pc, then_start_inv, entry_end_inv,
          read_err, h_s7_err, h_s7_program, h_s7_sp_aligned, Nat.reduceMul, h_s7_read_sp12,
          h_s7_read_sp8, and_self, Bool.not_eq_true, true_and, h_s7_sp, BitVec.ofNat_eq_ofNat, true_and]
        have h_s7_sgt := sgt_iff_n_eq_v_and_z_eq_0_32 (BitVec.zeroExtend 32 s0.x0) (BitVec.zeroExtend 32 s0.x1)
        simp only [not_and, not_imp, Decidable.not_not] at h
        rw [← h_s7_s6_n, ← h_s7_s6_v, ← h_s7_s6_z] at h_s7_sgt
        replace h_s7_sgt := h_s7_sgt.mp h
        simp [h_pre, pre]
        bv_decide
    · -- start @ then_start_inv
      simp [then_start_inv] at h_assert
      rename_i x h_s1_pc
      rename si to s1
      obtain ⟨⟨h_s1_err, h_s1_program, h_s1_sp_aligned, h_s1_read_sp_12, h_s1_read_sp_8, h_s1_sp⟩, h_KEEP_x0_x1⟩ := h_assert
      clear_named [h_assert]
      name h_s1_run : s2 := run 1 s1
      obtain ⟨h_s2_cut, h_s2_pc, h_s2_err, h_s2_read_sp_8, h_s2_read_sp_12, h_s2_x0, h_s2_x1, h_s2_sp, h_s2_program, _h_s2_mem, h_s2_sp_aligned⟩ :=
        program.stepi_0x8b0_cut s1 s2 h_s1_program h_s1_pc h_s1_err h_s1_sp_aligned h_s1_run.symm
      rw [Correctness.snd_cassert_of_not_cut h_s2_cut];
      simp [show Sys.next s2 = run 1 s2 by rfl]
      replace h_s2_x0 : s2.x0 = BitVec.zeroExtend 64 (BitVec.zeroExtend 32 s0.x0) := by
        rw [h_s2_x0]
        rw [h_s2_sp]
        rw [h_s1_sp]

        simp_all
      replace h_s2_x0 : s2.x0 = spec s0.x0 s0.x1 := by
        simp [spec, h_s2_x0]
        split  <;> bv_decide
      clear_named [h_s0]

      -- 3/15
      name h_run : s3 := run 1 s2
      obtain h := program.stepi_0x8b4_cut s2 s3 (by trivial) (by trivial) (by trivial) (by trivial) (h_run.symm)
      obtain ⟨h_s3_cut, h_s3_pc, h_s3_err, h_s3_program, h_s3_x0, h_s3_sp_28, h_s3_sp, h_s3_sp_aliged⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s3_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next _ = run 1 _ by rfl]
      replace h_s3_sp_28 : read_mem_bytes 4 (s3.sp + 28#64) s3 = BitVec.zeroExtend 32 (spec s0.x0 s0.x1) := by simp_all
      replace h_s3_sp : s3.sp = s0.sp - 32#64 := by simp_all
      clear_named [h_s2, h_s1]

      -- 4/15
      name h_run : s4 := run 1 s3
      obtain h_s4 := program.stepi_0x8b8_cut s3 s4 (by trivial) (by trivial) (by trivial) (by trivial) (h_run.symm)
      rw [Correctness.snd_cassert_of_not_cut (si := s4) (by simp_all [Spec'.cut])];
      simp [show Sys.next _ = run 1 _ by rfl]
      have h_s4_sp : s4.sp = s0.sp - 32#64 := by simp_all
      have h_s4_sp_28 : read_mem_bytes 4 (s4.sp + 28#64) s4 = BitVec.zeroExtend 32 (spec s0.x0 s0.x1) := by simp_all
      clear_named [h_s3]

      -- 5/15
      name h_run : s5 := run 1 s4
      obtain h_s5 := program.stepi_0x8c4_cut s4 s5 (by simp_all) (by simp_all) (by simp_all) (by simp_all) (h_run.symm)
      rw [Correctness.snd_cassert_of_not_cut (si := s5) (by simp_all [Spec'.cut])];
      have h_s5_x0 : s5.x0 = BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (spec s0.x0 s0.x1)) := by
        simp only [show s5.x0 = BitVec.zeroExtend 64 (read_mem_bytes 4 (s5.sp + 28#64) s5) by simp_all]
        simp only [Nat.reduceMul]
        /- Damn, that the rewrite system is not confluent really messes me up over here ;_;
        `simp` winds up rewriting `s5.sp` into `s4.sp` first because of the rule, and
        fails to match `read_mem_bytes... (s5.sp + ...) = read_mem_bytes ... (s4.sp + ...)`.
        One might say that this entire proof is stupid, but really, I 'just' want it to build an
        e-graph and figure it out.
         -/
        have : (read_mem_bytes 4 (s5.sp + 28#64) s5) = read_mem_bytes 4 (s4.sp + 28#64) s4 := by
          obtain ⟨_, _, _, _, _, _, h, _⟩ := h_s5
          exact h
        simp [this]
        rw [h_s4_sp_28]
      simp [show Sys.next _ = run 1 _ by rfl]

      -- 6/15
      name h_run : s6 := run 1 s5
      obtain h_s6 := program.stepi_0x8c8_cut s5 s6 (by simp_all) (by simp_all) (by simp_all) (by simp_all) (h_run.symm)
      rw [Correctness.snd_cassert_of_cut (si := s6) (by simp_all [Spec'.cut])];
      simp [Spec'.assert, assert, read_pc, h_s6, h_pre, post, read_err]
      simp [h_s5_x0, h_pre, pre]
    · -- start @ else_start_inv
      simp [else_start_inv] at h_assert
      rename_i x h_s1_pc
      rename si to s1
      obtain ⟨⟨h_s1_err, h_s1_program, h_s1_sp_aligned, h_s1_read_sp_12, h_s1_read_sp_8, h_s1_sp⟩, h_KEEP_x0_x1⟩ := h_assert
      clear_named [h_assert]
      name h_s1_run : s2 := run 1 s1
      obtain ⟨h_s2_cut, h_s2_pc, h_s2_err, h_s2_program, h_s2_x0, h_s2_sp_aligned⟩ :=
        program.stepi_0x8bc_cut s1 s2 h_s1_program h_s1_pc h_s1_err h_s1_sp_aligned h_s1_run.symm
      rw [Correctness.snd_cassert_of_not_cut h_s2_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s2 = run 1 s2 by rfl]
      replace h_s2_x0 : s2.x0 = BitVec.zeroExtend 64 (BitVec.zeroExtend 32 s0.x1) := by simp_all
      replace h_s2_x0 : s2.x0 = spec s0.x0 s0.x1 := by
        simp [spec, h_s2_x0]
        split  <;> bv_decide
      clear_named [h_s0]

      -- 3/15
      name h_run : s3 := run 1 s2
      obtain h := program.stepi_0x8c0_cut s2 s3 (by trivial) (by trivial) (by trivial) (by simp_all) (h_run.symm)
      obtain ⟨h_s3_cut, h_s3_pc, h_s3_err, h_s3_program, h_s3_x0, h_s3_sp, h_s3_sp_aliged⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s3_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next _ = run 1 _ by rfl]
      replace h_s3_sp_28 : read_mem_bytes 4 (s3.sp + 28#64) s3 = BitVec.zeroExtend 32 (spec s0.x0 s0.x1) := by simp_all
      replace h_s3_sp : s3.sp = s0.sp - 32#64 := by simp_all
      clear_named [h_s2, h_s1]

      -- 4/15
      name h_run : s4 := run 1 s3
      obtain h_s4 := program.stepi_0x8c4_cut s3 s4 (by trivial) (by trivial) (by trivial) (by trivial) (h_run.symm)
      rw [Correctness.snd_cassert_of_not_cut (si := s4) (by simp_all [Spec'.cut])];
      simp [show Sys.next _ = run 1 _ by rfl]
      have h_s4_sp : s4.sp = s0.sp - 32#64 := by simp_all
      have h_s4_sp_28 : read_mem_bytes 4 (s4.sp + 28#64) s4 = BitVec.zeroExtend 32 (spec s0.x0 s0.x1) := by simp_all
      clear_named [h_s3]

      -- 6/15
      name h_run : s5 := run 1 s4
      obtain h_s5 := program.stepi_0x8c8_cut s4 s5 (by simp_all) (by simp_all) (by simp_all) (by simp_all) (h_run.symm)
      rw [Correctness.snd_cassert_of_cut (si := s5) (by simp_all [Spec'.cut])];
      simp [Spec'.assert, assert, read_pc, h_s5, h_pre, post, read_err]
      simp_all [h_pre, pre]
    · rename_i x si_pc
      contradiction
    · apply False.elim h_assert

/--
info: 'MaxTandem.partial_correctness' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms partial_correctness

end MaxTandem
