/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel

Experimental: Use the Correctness module to prove that this program computes the
following via a naive loop that iterates over `x0`:
`x0 := x0 + x1`
-/
import Arm
import Tactics.CSE
import Tactics.Sym
import Tactics.StepThms
import Correctness.ArmSpec
import Proofs.Experiments.Max.MaxProgram
import Arm.Insts.Common
import Arm.Memory.SeparateAutomation

namespace MaxTandem
open Max


#check ArmState

section PC

scoped notation "entry_start" => 0x894#64
-- scoped notation "entry_end" => 0x8ac#64
scoped notation "then_start" => 0x8b0#64 -- yeesh, this is actually else.
-- scoped notation "then_end" => 0x8b8#64
scoped notation "else_start" => 0x8bc#64
-- scoped notation "else_end" => 0x8c0#64
-- scoped notation "merge_start" => 0x8c4#64
scoped notation "merge_end" => 0x8cc#64


namespace ArmStateNotation
--   scoped notation s "." slot  => r slot s
--   scoped notation s "." slot " := " val "; "  => w slot val s
--   scoped notation "x0" => StateField.GPR 0#5
--   scoped notation "x1" => StateField.GPR 1#5
--   scoped notation "sp" => StateField.GPR 31#5
--   scoped notation "pc" => StateField.PC

-- --   -- scoped notation s"@x0" => r (StateField.GPR 0x0#5) s
-- --   -- scoped notation x "[:32]" => BitVec.zeroExtend 32 x
-- --   -- scoped notation s"@sp" => r (StateField.GPR 31#5) s
-- --   -- scoped notation s"@pc" => r (StateField.PC) s
-- --   -- scoped notation s"@ERR" => r (StateField.ERR) s


@[inherit_doc read_mem_bytes]
syntax:max term noWs "[" withoutPosition(term)  ","  withoutPosition(term) noWs "]" : term
macro_rules | `($s[$base,$n]) => `(read_mem_bytes $n $base $s)


  -- scoped notation s "[" base ", " n "]" => read_mem_bytes n base s
  -- scoped notation s "[" base ", " n "]" ":= " val "; " => write_mem_bytes n base val s
end ArmStateNotation

open ArmStateNotation



def pcs : List (BitVec 64) := [entry_start,
  -- entry_end,
  then_start,
  -- then_end,
  else_start,
  -- else_end,
  -- merge_start,
  merge_end]

end PC

def cut (s : ArmState) : Bool := decide (read_pc s ∈ pcs)

section Invariants
-- variable (s0 si : ArmState)

/-- Precondition for the correctness of the Add program. -/
def pre (s : ArmState) : Prop :=
  read_pc s = entry_start ∧
  s.program = program ∧
  read_err s = StateError.None ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment s ∧
  mem_legal' s.sp 80 -- TODO: find the correct smallest bound we need here.


/-- Specification function. -/
def spec (x0 x1 : BitVec 64) : BitVec 64 :=
  if x0.zeroExtend 32 < x1.zeroExtend 32
  then (x1.zeroExtend 32).zeroExtend 64
  else (x0.zeroExtend 32).zeroExtend 64

def post (s0 sf : ArmState) : Prop :=
  sf.x0 = spec s0.x0 s0.x1 ∧
  read_pc sf = 0x894#64 ∧
  read_err sf = StateError.None ∧
  sf.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment sf

@[simp] def entry_start_inv (s0 si : ArmState) : Prop := si = s0



@[simp] def entry_end_inv (s0 si : ArmState): Prop :=
  read_err si = .None ∧
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si ∧
  si[s0.sp - 20#64 + 12#64, 4] = s0.x0.zeroExtend 32 ∧
  si[s0.sp - 20#64 + 8#64, 4] = s0.x1.zeroExtend 32 -- TODO: read flags.
  -- ∧ read_mem_bytes 4 (r (Spec) si) si = 0x0#32

@[simp] def then_start_inv (s0 si : ArmState): Prop :=
  entry_end_inv s0 si ∧
  ¬ (s0.x0 ≤ s0.x1)


@[simp] def then_end_inv (s0 si : ArmState) : Prop :=
  read_err si = .None ∧
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si ∧
  si[s0.sp - 20#64 + 28#64, 4] = (spec s0.x0 s0.x1).zeroExtend 32


@[simp] def else_start_inv (s0 si : ArmState) : Prop :=
  read_err si = .None ∧
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si ∧
  entry_end_inv s0 si ∧
  (s0.x0 ≤ s0.x1)

@[simp] def else_end_inv (s0 si : ArmState) : Prop :=
  read_err si = .None ∧
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si ∧
  si[s0.sp - 20#64 + 28#64, 4] = (spec s0.x0 s0.x1).zeroExtend 32



@[simp] def merge_start_inv (s0 si : ArmState) : Prop :=
  read_err si = .None ∧
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si  ∧
  si[s0.sp - 20#64 + 28#64, 4] = (spec s0.x0 s0.x1).zeroExtend 32


@[simp] def merge_end_inv (s0 sf : ArmState): Prop := post s0 sf

def exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = 0x8cc#64
end Invariants


def assert (s0 si : ArmState) : Prop :=
  pre s0 ∧
  -- Using `match` is preferable to `if` for the `split` tactic (and for
  -- readability).
  match (read_pc si) with
  | entry_start => entry_start_inv s0 si
  -- | entry_end => entry_end_inv s0 si
  | then_start => then_start_inv s0 si
  -- | then_end => then_end_inv s0 si
  | else_start => else_start_inv s0 si
  -- | else_end => else_end_inv s0 si
  -- | merge_start => merge_start_inv s0 si
  -- | merge_end => merge_end_inv s0 si
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
  simp (config := { decide := true, ground := true }) only [minimal_theory] at this
  simp_all only [run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory, pcs]
  simp only [List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
    true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]
  repeat first
  | simp (config := { ground := true, decide := true}) [aligned_rules, state_simp_rules]
  | apply Aligned_BitVecSub_64_4;
  | apply Aligned_BitVecAdd_64_4;
  | apply Aligned_AddWithCarry_64_4;
  | apply Aligned_AddWithCarry_64_4'

  repeat solve
  | apply Aligned_of_extractLsb_eq_zero; bv_decide
  | apply Aligned_of_toNat_mod_eq_zero; bv_omega
  | decide
  | bv_omega
  | assumption

/--
info: 'MaxTandem.program.stepi_0x894_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x894_cut

-- 2/15: str  w0, [sp, #12]  ; sp[12] = w0_a
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
set_option trace.simp_mem.info true in
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
  sn.C = (AddWithCarry (BitVec.zeroExtend 32 (r (StateField.GPR 1#5) s))
            (~~~BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s)) 1#1).snd.c ∧
  sn.V = (AddWithCarry (BitVec.zeroExtend 32 (r (StateField.GPR 1#5) s))
            (~~~BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s)) 1#1).snd.v ∧
  sn.Z = (AddWithCarry (BitVec.zeroExtend 32 (r (StateField.GPR 1#5) s))
            (~~~BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s)) 1#1).snd.z ∧
  sn.N = (AddWithCarry (BitVec.zeroExtend 32 (r (StateField.GPR 1#5) s))
            (~~~BitVec.zeroExtend 32 (r (StateField.GPR 0#5) s)) 1#1).snd.n ∧
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
  -- simp only [or_false, or_true]


/--
info: 'MaxTandem.program.stepi_0x8a8_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8a8_cut

-- 7/15
-- @bollu: this is useless? we were able to make progress even without this? (branch.)
-- b.le 8bc
theorem program.stepi_0x8ac_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8ac#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = true ∧
  r StateField.PC sn =
  (if ¬(r (StateField.FLAG PFlag.N) s = r (StateField.FLAG PFlag.V) s ∧ r (StateField.FLAG PFlag.Z) s = 0#1)
  then 2236#64 -- takes the branch
  else 0x8b0#64) ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn
  := by
  have := program.stepi_eq_0x8ac h_program h_pc h_err
  simp only [minimal_theory] at this
  simp only [← not_and] at *
  simp only [cut, read_pc, pcs, List.mem_cons, List.mem_singleton, Bool.decide_or, Bool.or_eq_true,
    decide_eq_true_eq, state_value]
  split
  case isTrue h =>
    simp [h] at this
    have : sn = w StateField.PC (2236#64) s := by
      rw [h_step, ← this]
      rfl
    simp [this, state_simp_rules, h_sp_aligned, h_err, h_program]
  case isFalse h =>
    simp [h] at this
    /- TODO: we have too many layers of abstraction. We need to choose a simp normal form
    between `run` and `step`. -/
    have : sn = w StateField.PC (2224#64) s := by
      rw [h_step, ← this]
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
  sn.program = program ∧
  sn.x0 = BitVec.zeroExtend 64 s[sn.sp + 12, 4] ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8b0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true]
  simp only [List.not_mem_nil, or_self, not_false_eq_true]
  -- simp only [pcs, List.mem_cons, BitVec.reduceEq, List.mem_singleton, or_self, not_false_eq_true,
  --   true_and, List.not_mem_nil, or_self, not_false_eq_true, true_and]
  -- simp only [or_false, or_true]

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
  sn[sn.sp + 28, 4] = sn.x0.zeroExtend 32 ∧
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

-- ldr  w0, [sp, #8]
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
  sn.x0 = BitVec.zeroExtend 64 (sn[sn.sp + 8, 4])  ∧
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

--- str  w0, [sp, #28]
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
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8c0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp [pcs]

  /--
info: 'MaxTandem.program.stepi_0x8c0_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8c0_cut

-- ldr  w0, [sp, #28]
theorem program.stepi_0x8c4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x8c4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  r StateField.PC sn = 0x8c8#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  cut sn = false ∧
  sn.x0 = BitVec.zeroExtend 64 (sn[sn.sp + 28, 4])  ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8c4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp [pcs]

/--
info: 'MaxTandem.program.stepi_0x8c4_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8c4_cut

-- add  sp, sp, #0x20
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
  sn.sp = s.sp + 0x20#64 ∧
  CheckSPAlignment sn :=  by
  have := program.stepi_eq_0x8c8 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  simp (config := {ground := true, decide := true})
  apply Aligned_BitVecAdd_64_4
  · assumption
  · decide

/--
info: 'MaxTandem.program.stepi_0x8c8_cut' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms program.stepi_0x8c8_cut

end CutTheorems

-- -- Branch instruction!
-- theorem program.stepi_0x4005b4_cut (s sn : ArmState)
--   (h_program : s.program = program)
--   (h_pc : r StateField.PC s = 0x4005b4#64)
--   (h_err : r StateField.ERR s = StateError.None)
--   (h_sp_aligned : CheckSPAlignment s)
--   (h_step : sn = run 1 s) :
--   cut sn = (r (StateField.FLAG PFlag.Z) s = 1#1) ∧
--   r StateField.PC sn = (if (r (StateField.FLAG PFlag.Z) s = 1#1) then
--                                   0x4005b8#64
--                               else
--                                   0x4005a8#64) ∧
--   r StateField.ERR sn = .None ∧
--   sn.program = program ∧
--   CheckSPAlignment sn := by
--   have := program.stepi_eq_0x4005b4 h_program h_pc h_err
--   simp only [minimal_theory] at this
--   simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
--   split
--   · rename_i h
--     simp_all only [state_simp_rules, bitvec_rules, minimal_theory]
--   · rename_i h; simp only [minimal_theory] at h
--     simp_all only [state_simp_rules, minimal_theory]
--     done

-- theorem program.stepi_0x4005b8_cut (s sn : ArmState)
--   (h_program : s.program = program)
--   (h_pc : r StateField.PC s = 0x4005b8#64)
--   (h_err : r StateField.ERR s = StateError.None)
--   (h_sp_aligned : CheckSPAlignment s)
--   (h_step : sn = run 1 s) :
--   cut sn = true ∧
--   r StateField.PC sn = 0x4005bc#64 ∧
--   r StateField.ERR sn = .None ∧
--   sn.program = program ∧
--   CheckSPAlignment sn := by
--   have := program.stepi_eq_0x4005b8 h_program h_pc h_err
--   simp only [minimal_theory] at this
--   simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
--   done

-- -- (TODO) program.stepi_0x4005bc_cut elided.
-- -- theorem program.stepi_0x4005bc_cut (s sn : ArmState)
-- --   (h_program : s.program = program)
-- --   (h_pc : r StateField.PC s = 0x4005bc#64)
-- --   (h_err : r StateField.ERR s = StateError.None)
-- --   (h_sp_aligned : CheckSPAlignment s)
-- --   (h_step : sn = run 1 s) :
-- --   cut sn = false := by
-- --   have := program.stepi_eq_0x4005bc h_program h_pc h_err
-- --   simp only [minimal_theory] at this

-- --   simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
-- --   done

-------------------------------------------------------------------------------

-- Throwaway tactic to do symbolic simulation in the context of
-- Correctness.partial_correctness_from_assertions.
open Lean (FVarId TSyntax logWarning) in
open Lean.Elab.Tactic (TacticM evalTactic withMainContext) in
def sym1_cassert (curr_state_number : Nat)
                 (cassert_eq : Lean.Name)
                 (cut_eq : Lean.Name)
                 : TacticM Unit :=
  withMainContext do
    let n_str := toString curr_state_number
    let n'_str := toString (curr_state_number + 1)
    let mk_name (s : String) : Lean.Name :=
      Lean.Name.mkStr Lean.Name.anonymous s
    -- h_st_*: name of the hypothesis about projections from state st.
    let h_st_program := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_program"))
    let h_st_pc := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_pc"))
    let h_st_err := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_err"))
    let h_st_sp_aligned := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_sp_aligned"))
    -- st: name of the current state
    let st := Lean.mkIdent (mk_name ("s" ++ n_str))
    -- stn: name of the next state
    let stn := Lean.mkIdent (mk_name ("s" ++ n'_str))
    -- stn': temporary name of the next state
    let stn' := Lean.mkIdent (mk_name ("s" ++ n'_str ++ "'"))
    -- h_st_run: name of the hypothesis with the `run` function
    let h_st_run := Lean.mkIdent (mk_name ("h_s" ++ n_str ++ "_run"))
    -- stepi_st: name of the hypothesis which associates st and stn with a stepi
    -- function.
    let stepi_st := Lean.mkIdent (mk_name ("stepi_s" ++ n_str))
    -- cassert_eq lemma
    let cassert_eq_lemma := Lean.mkIdent cassert_eq
    -- cut_lemma
    let cut_lemma := Lean.mkIdent cut_eq
    evalTactic (←
      `(tactic|
         (rw [$cassert_eq_lemma:ident]
          generalize $h_st_run:ident : run 1 $st:ident = $stn':ident
          replace $h_st_run:ident := ($h_st_run:ident).symm
          sym_n 1 at $st:ident
          have h_cut := $cut_lemma:ident $st:ident $stn:ident
                         $h_st_program:ident $h_st_pc:ident
                         $h_st_err:ident $h_st_sp_aligned:ident
                         (by simp only [run, $stepi_st:ident])
          simp only [run_opener_zero] at $h_st_run:ident
          rw [$h_st_run:ident] at *
          simp only [h_cut, Nat.reduceAdd, minimal_theory]
          clear $stn':ident h_cut $h_st_run:ident $stepi_st:ident
      )))

-- sym_i_assert tactic symbolically simulates 1 instruction from the state
-- number `i`.
elab "sym_i_cassert" i:num cassert_eq:ident cut_eq:ident : tactic => do
  sym1_cassert i.getNat cassert_eq.getId cut_eq.getId

theorem cassert_eq (s0 si : ArmState) (i : Nat) :
  Correctness.cassert s0 si i = if cut si then (i, assert s0 si)
                       else Correctness.cassert s0 (run 1 si) (i + 1) := by
  rw [Correctness.cassert_eq]
  simp only [Sys.next, Spec'.cut, Spec'.assert, run]
  done
/--
rename an old term `old` identifier a new identifier `new`, and replace
all occurrences of `old` with `new`.
-/
macro "rename" old:ident "to" new:ident : tactic =>
  `(tactic|
    generalize h_rename : $old = $new <;> subst $old)

/-- define a value `x := val`, and name the hypothesis `heq : x := val` -/
macro "name" heq:ident ":" x:ident " := " val:term : tactic =>
  `(tactic| generalize $heq : $val = $x)


/-- info: Correctness.cassert {σ : Type} [Sys σ] [Spec' σ] (s0 si : σ) (i : Nat) : Nat × Prop -/
#guard_msgs in #check Correctness.cassert

/-- info: MaxTandem.cut (s : ArmState) : Bool -/
#guard_msgs in #check cut

open Lean Elab Meta Tactic in
/-- If no name is supplied, then clears all inaccessible names.
If a list of names is supplied, then clear all inaccessible names that have
*any* one of the strings as prefixes. -/
elab "clear_named" "[" names:(ident),* "]": tactic =>  do
  withMainContext do
    for hyp in (← getLCtx) do
      trace[debug] "name: {hyp.userName}"
      for name in names.getElems do
        if name.getId.toString.isPrefixOf hyp.userName.toString then
          replaceMainGoal [← (← getMainGoal).clear hyp.fvarId]
          continue


/-
open Lean Meta Elab in
dsimproc [vcg_rules] reduce_snd_cassert_of_cut
  (Correctness.cassert _ _ _) := fun e => do
  let_expr Correctness.cassert s0 si i := e | return .continue
  for hyp in (← getLCtx) do
    -- cut si = true
    -- match_expr hyp.type with
    -- | cut s2 = true
    pure ()
  return .continue
-/
set_option trace.debug true in
theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_assertions
  case v1 =>
    intro s0 h_pre
    simp only [Spec.pre] at h_pre
    have ⟨h_pre_pc, h2⟩ := h_pre
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
    simp only [h_exit, merge_end_inv] at h_assert
    simp only [Spec.post]
    simp_all
  case v4 =>
    intro s0 si h_assert h_not_exit
    simp only [Correctness.arm_run]
    simp [Spec.exit, exit] at h_not_exit
    simp only [Spec'.assert, assert, h_not_exit, minimal_theory] at h_assert
    obtain ⟨h_pre, h_assert⟩ := h_assert
    have ⟨h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned, h_mem_legal⟩ := h_pre
    simp_all only [Spec'.assert, Spec.exit, assert, exit,
                   minimal_theory, state_simp_rules]
    split at h_assert
    · -- Next cutpoint from 0x894#64 (1/15)
      subst si
      rename_i x h_pc
      name h_s0_run : s1 := run 1 s0
      obtain ⟨h_s1_cut, h_s1_pc, h_s1_err, h_s1_x0, h_s1_x1, h_s1_sp, h_s1_mem, h_s1_program, h_s1_sp_aligned⟩ :=
        program.stepi_0x894_cut s0 s1 h_s0_program h_pc h_s0_err h_s0_sp_aligned h_s0_run.symm
      rw [Correctness.snd_cassert_of_not_cut h_s1_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s1 = run 1 s1 by rfl]
      clear_named [h_s0]

      -- 2/15
      name h_s1_run : s2 := run 1 s1
      obtain ⟨h_s2_cut, h_s2_pc, h_s2_err, h_s2_program, h_s2_read_sp_8, h_s2_read_sp_12, h_s2_x0, h_s2_x1, h_s2_sp, h_s2_sp_aligned⟩ :=
        program.stepi_0x898_cut s1 s2 h_s1_program h_s1_pc h_s1_err h_s1_sp_aligned _ h_s1_run.symm
      rw [Correctness.snd_cassert_of_not_cut h_s2_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s2 = run 1 s2 by rfl]
      replace h_s2_sp : s2.sp = (s0.sp - 32#64) := by simp_all
      replace h_s2_x0 : s2.x0 = s0.x0 := by simp_all
      replace h_s2_x1 : s2.x1 = s0.x1 := by simp_all
      replace h_s2_read_sp12 : read_mem_bytes 4 (s2.sp + 12#64) s2 = BitVec.truncate 32 s0.x0 := by simp_all
      clear_named [h_s1]

      -- 3/15
      name h_run : s3 := run 1 s2
      obtain h := program.stepi_0x89c_cut s2 s3 h_s2_program h_s2_pc h_s2_err h_s2_sp_aligned _ h_run.symm
      obtain ⟨h_s3_cut, h_s3_read_sp_8, h_s3_read_sp_12, h_s3_x0, h_s3_x1, h_s3_sp, h_s3_pc, h_s3_err, h_s3_program, h_s3_sp_aligned⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s3_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s3 = run 1 s3 by rfl]
      replace h_s3_x0 : s3.x0 = s0.x0 := by simp_all
      replace h_s3_x1 : s3.x1 = s0.x1 := by simp_all
      replace h_s3_sp : s3.sp = s0.sp - 32 := by simp_all
      /- TODO: this should be s0.x0-/
      replace h_s3_read_sp12 : read_mem_bytes 4 (s3.sp + 12#64) s3 = BitVec.truncate 32 s0.x0 := by simp_all
      replace h_s3_read_sp8 : read_mem_bytes 4 (s3.sp + 8#64) s3 = BitVec.truncate 32 s0.x1 := by simp_all
      clear_named [h_s2]

      -- 4/15
      name h_run : s4 := run 1 s3
      obtain h := program.stepi_0x8a0_cut s3 s4 h_s3_program h_s3_pc h_s3_err h_s3_sp_aligned h_run.symm
      obtain ⟨h_s4_cut, h_s4_read_sp_8, h_s4_read_sp_12, h_s4_x0, h_s4_x1, h_s4_sp, h_s4_pc, h_s4_err, h_s4_program, h_s4_sp_aligned⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s4_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s4 = run 1 s4 by rfl]
      replace h_s4_sp : s4.sp = s0.sp - 32 := by simp_all
      replace h_s4_x0 : s4.x0 = s0.x0 := by simp_all
      replace h_s4_x1 : s4.x1 = BitVec.zeroExtend 64 (BitVec.truncate 32 s0.x0) := by simp_all
      replace h_s4_sp : s4.sp = s0.sp - 32 := by simp_all
      replace h_s4_read_sp12 : read_mem_bytes 4 (s4.sp + 12#64) s4 = BitVec.truncate 32 s0.x0 := by simp_all
      replace h_s4_read_sp8 : read_mem_bytes 4 (s4.sp + 8#64) s4 = BitVec.truncate 32 s0.x1 := by simp_all
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
      replace h_s5_read_sp8 : read_mem_bytes 4 (s5.sp + 8#64) s5 = BitVec.truncate 32 s0.x1 := by simp_all
      clear_named [h_s4]

      -- 6/15
      name h_run : s6 := run 1 s5
      obtain h := program.stepi_0x8a8_cut s5 s6 h_s5_program h_s5_pc h_s5_err h_s5_sp_aligned h_run.symm
      obtain ⟨h_s6_cut, h_s6_pc, h_s6_err, h_s6_program, h_s6_c, h_s6_v, h_s6_z, h_s6_n, h_s6_read_sp_8, h_s6_read_sp_12, h_s6_x0, h_s6_x1, h_s6_sp, h_s6_sp_aligned, h_s6_mem⟩ := h
      rw [Correctness.snd_cassert_of_not_cut h_s6_cut]; -- try rw [Correctness.snd_cassert_of_cut h_cut];
      simp [show Sys.next s6 = run 1 s6 by rfl]
      replace h_s6_sp : s6.sp = s0.sp - 32 := by simp_all
      replace h_s6_x0 : s6.x0 = BitVec.zeroExtend 65 (BitVec.truncate 32 s0.x1) := by simp_all
      replace h_s6_x1 : s6.x1 = BitVec.zeroExtend 65 (BitVec.truncate 32 s0.x0) := by simp_all
      replace h_s6_sp : s6.sp = s0.sp - 32 := by simp_all
      replace h_s6_read_sp12 : read_mem_bytes 5 (s6.sp + 12#64) s6 = BitVec.truncate 32 s0.x0 := by simp_all
      replace h_s6_read_sp8 : read_mem_bytes 5 (s6.sp + 8#64) s6 = BitVec.truncate 32 s0.x1 := by simp_all
      clear_named [h_s5]

      -- replace h_read_sp_12 : read_mem_bytes 4 (s2.sp + 12#64) s3 = BitVec.truncate 32 s1.x0 := by
      --   exact h_read_sp_12
        -- clear_named h_program -- TODO: stick to naming discipline of h_s3_... to be able to clear via this tactic.
      -- -- Begin: Symbolic simulation
      -- sym_i_cassert 0 cassert_eq program.stepi_0x894_cut
      -- case h_s1_sp_aligned =>
      --   simp (config := {decide := true, ground := true}) only []
      --   apply Aligned_BitVecSub_64_4
      --   · assumption
      --   · decide
      -- sym_i_cassert 1 cassert_eq program.stepi_0x898_cut
      -- simp only [h_s1_sp_aligned, minimal_theory] at h_step_2
      -- sym_i_cassert 2 cassert_eq program.stepi_0x89c_cut
      -- simp only [h_s2_sp_aligned, minimal_theory] at h_step_3
      -- sym_i_cassert 3 cassert_eq program.stepi_0x8a0_cut
      -- simp only [h_s3_sp_aligned, minimal_theory] at h_step_4
      -- sym_i_cassert 4 cassert_eq program.stepi_0x8a4_cut
      -- simp only [h_s4_sp_aligned, minimal_theory] at h_step_5
      -- sym_i_cassert 5 cassert_eq program.stepi_0x8a8_cut
      -- -- End: Symbolic simulation
      -- simp only [assert, h_pre, h_s6_pc,
      --            state_simp_rules, bitvec_rules, minimal_theory]
      -- simp only [h_s6_pc, h_s6_program, h_s6_err, h_s6_sp_aligned,
      --            entry_end_inv, state_simp_rules, minimal_theory]
      -- -- @bollu: I'm not sure why we need to do this.
      -- simp [cut, h_s3_pc, read_pc, pcs]
      done
    · -- start @ then_start_inv
      simp [then_start_inv] at h_assert
      sorry
    · -- start @ else_start_inv
      simp [else_start_inv] at h_assert
      sorry
  /-
    · -- Next cutpoint from 0x8ac (B.LE instruction)
      --
      -- (FIXME @shilpi) Hack for awful sym_i_cassert tactic which expects a
      -- numeric suffix for the state variables.
      -- generalize h_si_s1 : si = s1; subst si
      --
      rename_i h_inv_pc
      obtain ⟨h_inv_err, h_inv_program, h_inv_sp_aligned⟩ := h_assert
      -- Also see:
      -- https://developer.arm.com/documentation/ddi0602/2023-03/Shared-Pseudocode/shared-functions-system?lang=en#impl-shared.ConditionHolds.1
      -- https://developer.arm.com/documentation/dui0801/l/Condition-Codes/Condition-flags
      by_cases h_cond_holds : (r (StateField.FLAG PFlag.N) si = r (StateField.FLAG PFlag.V) si) ∧
                               (r (StateField.FLAG PFlag.Z) si = 0#1)
      case neg => -- Branch taken
        -- have h_inv_x0_nz : ¬ r (StateField.GPR 0#5) si = 0#64 := by
        --   -- TODO: missing iff_rule?
        --   simp (config := {decide := true}) only
        --     [h_cond_holds, minimal_theory] at h_inv_zf_x0
        --   assumption
        -- Begin: Symbolic simulation
        -- Instruction 1 (branch instruction)
        rw [cassert_eq]
        generalize h_run : run 1 si = s1
        replace h_run := (h_run).symm
        -- (TODO) Better handling of branch instructions.
        -- sym_n 1 at si
        have stepi_si : stepi si = s1 := by simp only [h_run, run]
        have h_step_1 := @program.stepi_eq_0x8ac si h_inv_program h_inv_pc h_inv_err
        rw [stepi_si] at h_step_1
        simp only [← not_and] at h_step_1
        simp only [h_cond_holds, minimal_theory] at h_step_1
        have h_cut := @program.stepi_0x8ac_cut si s1
                       h_inv_program h_inv_pc h_inv_err h_inv_sp_aligned
                       h_run
        simp only [h_cond_holds, bitvec_rules, minimal_theory]
          at h_step_1 h_cut
        simp only [h_cut, minimal_theory]
        clear stepi_si h_run
        (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
         (all_goals (try assumption)))
        clear h_cut
        -- End: Symbolic simulation
        simp only [assert, h_pre, h_s1_pc,
                   minimal_theory, state_simp_rules]
        simp only [else_start_inv]
        done
      case pos =>
        sorry
    · -- start @ then_start_inv
      simp [then_start_inv] at h_assert
      sym_i_cassert 0 cassert_eq program.stepi_0x894_cut
      case h_s1_sp_aligned =>
        simp (config := {decide := true, ground := true}) only []
        apply Aligned_BitVecSub_64_4
        · assumption
        · decide
      -- End: Symbolic simulation
      sorry
    · -- start @ then_end_inv
      rename_i x h_s1_pc -- what in the world is this `x`?
      simp [then_end_inv] at h_assert
      obtain ⟨h_s1_err, h_s1_program, h_s1_sp_aligned⟩ := h_assert
      generalize h_si_s1 : si = s1; subst si
      sym_i_cassert 1 cassert_eq program.stepi_0x8b8_cut
      simp [assert, h_s2_pc, read_pc]
      simp [h_pre, h_s2_err, h_s2_program, h_s2_sp_aligned, read_err]

    · -- start @ else_start_inv
      rename_i x h_s1_pc -- what in the world is this `x`?
      simp [else_start_inv] at h_assert
      obtain ⟨h_s1_err, h_s1_program, h_s1_sp_aligned⟩ := h_assert
      rename si to s1
      name h_s2 : s2 := run 1 s1
      -- generalize h_s2 : run 1 s1 = s2
      obtain ⟨h_cut, h_pc, h_err, h_program, h_s2_x0, h_sp_aligned⟩  :=
        program.stepi_0x8bc_cut s1 s2 h_s1_program h_s1_pc h_s1_err h_s1_sp_aligned h_s2.symm
      rw [Correctness.snd_cassert_of_cut h_cut]
      simp only [Spec'.assert, assert, state_simp_rules,
        h_pre, read_pc, h_pc, else_end_inv, read_err, h_err,
        h_program, h_sp_aligned, and_self]
    ·  -- start @ else_end_inv
      rename_i x h_s1_pc
      simp [else_end_inv] at h_assert

      obtain ⟨h_s1_err, h_s1_program, h_s1_sp_aligned⟩ := h_assert
      rename si to s1
      name h_s2 : s2 := run 1 s1
      obtain ⟨h_cut, h_pc, h_err, h_program, h_s2_x0, h_sp_aligned⟩ :=
        program.stepi_0x8c0_cut s1 s2 h_s1_program h_s1_pc h_s1_err h_s1_sp_aligned h_s2.symm
      try rw [Correctness.snd_cassert_of_cut h_cut]; try rw [Correctness.snd_cassert_of_not_cut h_cut];
      simp [Spec'.assert, assert, h_pc, read_pc, h_err, read_err, h_program, h_sp_aligned, h_pre]
    · -- start @ merge_start_inv
      sorry
    · -- start @ merge_end_inv
      rename_i x h_s1_pc
      simp [merge_end_inv] at h_assert

      obtain ⟨h_s1_err, h_s1_program, h_s1_sp_aligned⟩ := h_assert
      rename si to s1
      -- what? why can't I have a cutpoint here? I don't get it.
      rw [h_s1_pc] at h_not_exit
      simp at h_not_exit

    · exact False.elim h_assert
-/

/--
info: 'MaxTandem.partial_correctness' depends on axioms: [propext, sorryAx, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms partial_correctness
-------------------------------------------------------------------------------

-- def loop_clock (x0 : BitVec 64) : Nat :=
--   if h : x0 = 0#64 then
--     1
--   else
--     have : x0 - 0x1#64 < x0 := by
--      bv_omega
--     4 + loop_clock (x0 - 1)
--   termination_by x0.toNat

-- theorem loop_clock_inv_lemma (h : ¬x = 0x0#64) :
--   loop_clock (x - 0x1#64) < loop_clock x := by
--   generalize h_xn : x.toNat = xn
--   have h_xn_ge_1 : 1 ≤ xn := by bv_omega
--   induction xn, h_xn_ge_1 using Nat.le_induction generalizing x
--   case base =>
--     have h_x_eq_1 : x = 1#64 := by bv_omega
--     unfold loop_clock
--     simp only [h_x_eq_1, BitVec.sub_self, BitVec.ofNat_eq_ofNat,
--                reduceDIte, gt_iff_lt, BitVec.reduceEq]
--     omega
--   case succ =>
--     rename_i xn' h_xn' h_inv
--     unfold loop_clock
--     simp only [BitVec.ofNat_eq_ofNat, dite_eq_ite, gt_iff_lt]
--     have h1 : ¬ x - 0x1#64 = 0x0#64 := by bv_omega
--     have h2 : (x - 0x1#64).toNat = xn' := by bv_omega
--     simp only [h, h1, h2, h_inv,
--                reduceIte, Nat.add_lt_add_iff_left, not_false_eq_true]
--   done

-- def clock (s : ArmState) : Nat :=
--   let x0 := r (StateField.GPR 0#5) s
--   if x0 = 0#64 then
--     2 + 1 + 1
--   else
--     2 + ((loop_clock x0) + 1)

-- /--
-- Our formalization of the rank of a cutpoint for this program is the number of
-- instructions that remain to be executed from that point.
-- -/
-- def rank (si : ArmState) : Nat :=
--   match (read_pc si) with
--   | 0x4005a4#64 =>
--     -- First instruction
--     clock si
--   | 0x4005b4#64 =>
--     -- Loop guard
--     (loop_clock (r (StateField.GPR 0#5) si)) + 1
--   | 0x4005b8#64 =>
--     -- First instruction following the loop
--     1
--   | 0x4005bc#64 =>
--     -- Last instruction
--     0
--   | _ =>
--    -- No cutpoints remain
--     0

-- theorem loop_clk_plus_one_lt_clock :
--   (loop_clock (r (StateField.GPR 0x0#5) s)) + 1 < clock s := by
--   simp only [clock]
--   unfold loop_clock
--   split <;> omega

-- theorem rank_decreases_eq (si sn : ArmState) (i : Nat) :
--   Correctness.rank_decreases rank si sn i =
--     if cut sn then (i, rank sn < rank si)
--               else Correctness.rank_decreases rank si (run 1 sn) (i + 1) := by
--   rw [Correctness.rank_decreases_eq]
--   simp only [Spec'.cut, Sys.next, run]
--   done

-- -- (FIXME) The termination proof looks very similar to the partial correctness
-- -- one, and we ought to do them in one swoop.
-- theorem termination :
--   Termination ArmState := by
--   apply Correctness.termination_from_decreasing_rank rank
--   case v1 =>
--     intro s0 h_pre
--     simp_all only [Spec.pre, pre, Spec'.assert, assert,
--                     minimal_theory]
--   case v2 =>
--     intro s0 si h_assert h_not_exit
--     simp only [Correctness.arm_run]
--     simp [Spec.exit, exit] at h_not_exit
--     simp only [Spec'.assert, assert, h_not_exit, minimal_theory] at h_assert
--     obtain ⟨h_pre, h_assert⟩ := h_assert
--     have ⟨h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned⟩ := h_pre
--     simp_all only [Spec'.assert, Spec.exit, assert, exit,
--                    minimal_theory, state_simp_rules]
--     split at h_assert
--     · -- Next cutpoint from 0x4005a4#64 (first instruction)
--       subst si
--       -- Begin: Symbolic simulation
--       sym_i_cassert 0 rank_decreases_eq program.stepi_0x4005a4_cut
--       sym_i_cassert 1 rank_decreases_eq program.stepi_0x4005b0_cut
--       -- End: Symbolic simulation
--       simp only [rank, h_s0_pc, h_s2_pc, state_simp_rules]
--       simp (config := {ground := true}) only at h_step_2
--       simp only [h_step_2, h_step_1, loop_clk_plus_one_lt_clock,
--                  state_simp_rules, bitvec_rules, minimal_theory]
--       done
--     · -- Next cutpoint from 0x4005b4#64 (loop guard)
--       --
--       -- (FIXME @shilpi) Hack for awful sym_i_cassert tactic which expects a
--       -- numeric suffix for the state variables.
--       -- generalize h_si_s1 : si = s1; subst si
--       --
--       rename_i h_inv_pc
--       obtain ⟨h_inv_x0_lt, h_inv_zf_x0, h_inv_x1,
--               h_inv_err, h_inv_program, h_inv_sp_aligned⟩ := h_assert
--       simp only [state_simp_rules, bitvec_rules, minimal_theory] at *
--       by_cases h_cond_holds : r (StateField.FLAG PFlag.Z) si = 0x0#1
--       case pos =>
--         have h_inv_x0_nz : ¬ r (StateField.GPR 0#5) si = 0#64 := by
--           -- TODO: missing iff_rule?
--           simp (config := {decide := true}) only
--             [h_cond_holds, minimal_theory] at h_inv_zf_x0
--           assumption
--         -- Begin: Symbolic simulation
--         -- Instruction 1 (branch instruction)
--         rw [rank_decreases_eq]
--         generalize h_run : run 1 si = s1
--         replace h_run := (h_run).symm
--         -- (TODO) Better handling of branch instructions.
--         -- sym_n 1 at si
--         have stepi_si : stepi si = s1 := by simp only [h_run, run]
--         have h_step_1 := @program.stepi_eq_0x4005b4 si
--                           h_inv_program h_inv_pc h_inv_err
--         rw [stepi_si] at h_step_1
--         have h_cut := @program.stepi_0x4005b4_cut si s1
--                        h_inv_program h_inv_pc h_inv_err h_inv_sp_aligned
--                        h_run
--         simp only [h_cond_holds, bitvec_rules, minimal_theory]
--           at h_step_1 h_cut
--         have h_cut' : cut s1 = false := by
--           -- TODO: missing iff_rule?
--           simp (config := {decide := true}) only [minimal_theory] at h_cut
--           simp only [h_cut]
--           done
--         simp only [h_cut', minimal_theory]
--         clear stepi_si h_run
--         (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
--          (all_goals (try assumption)))
--         clear h_cut h_cut'
--         -- Instruction 2
--         sym_i_cassert 1 rank_decreases_eq program.stepi_0x4005a8_cut
--         sym_i_cassert 2 rank_decreases_eq program.stepi_0x4005ac_cut
--         sym_i_cassert 3 rank_decreases_eq program.stepi_0x4005b0_cut
--         -- End: Symbolic simulation
--         simp only [rank,
--                    h_s4_pc, h_inv_pc,
--                    state_simp_rules, bitvec_rules, minimal_theory]
--         -- Aggregate program effects here.
--         simp (config := {ground := true}) only at h_step_4 h_step_3 h_step_2
--         simp only [h_step_4, h_step_3, h_step_2, h_step_1,
--                    state_simp_rules, bitvec_rules, minimal_theory]
--         clear h_step_4 h_step_3 h_step_2 h_step_1
--         rw [AddWithCarry.sub_one_64]
--         have := loop_clock_inv_lemma h_inv_x0_nz
--         omega
--         done
--       case neg =>
--         have h_inv_zf : r (StateField.FLAG PFlag.Z) si = 1#1 := by
--           -- (FIXME) Ugh, tedious.
--           rw [@non_zero_one_bit_is_one (r (StateField.FLAG PFlag.Z) si)]
--           assumption
--         simp only [h_inv_zf, minimal_theory] at h_inv_zf_x0
--         -- Begin: Symbolic simulation
--         -- Instruction 1 (branch instruction)
--         rw [rank_decreases_eq]
--         generalize h_run : run 1 si = s1
--         replace h_run := (h_run).symm
--         -- (TODO) Better handling of branch instructions.
--         -- sym_n 1 at si
--         have stepi_si : stepi si = s1 := by simp only [h_run, run]
--         have h_step_1 := @program.stepi_eq_0x4005b4 si
--                           h_inv_program h_inv_pc h_inv_err
--         rw [stepi_si] at h_step_1
--         have h_cut := @program.stepi_0x4005b4_cut si s1
--                        h_inv_program h_inv_pc h_inv_err h_inv_sp_aligned
--                        h_run
--         simp only [h_cond_holds, h_inv_zf, bitvec_rules, minimal_theory]
--           at h_step_1 h_cut
--         simp only [h_cut, minimal_theory]
--         clear h_cut stepi_si h_run
--         (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
--           all_goals (try assumption))
--         -- End: Symbolic simulation
--         simp only [rank,
--                    h_s1_pc, h_inv_pc, h_inv_zf_x0,
--                    state_simp_rules, bitvec_rules, minimal_theory]
--         simp (config := {ground := true}) only
--         done
--     · -- Next cutpoint from 0x4005b8#64 (first instruction after loop)
--       --
--       -- (FIXME @shilpi) Hack for awful sym_i_cassert tactic which expects a
--       -- numeric suffix for the state variables.
--       generalize h_si_s1 : si = s1; subst si
--       --
--       rename_i h_s1_pc
--       obtain ⟨h_s1_x1, h_s1_err, h_s1_program, h_s1_sp_aligned⟩ := h_assert
--       simp only [state_simp_rules, bitvec_rules, minimal_theory] at *
--       -- Begin: Symbolic simulation
--       sym_i_cassert 1 rank_decreases_eq program.stepi_0x4005b8_cut
--       -- End: Symbolic simulation
--       simp only [rank, h_s2_pc, h_s1_pc,
--                  state_simp_rules, bitvec_rules, minimal_theory]
--       done
--     · -- Next cutpoint from 0x4005bc#64 (last instruction)
--       -- No such cutpoint exists.
--       contradiction
--     · -- No further cutpoints exist.
--       simp_all only
--   done

end AddLoopTandem
