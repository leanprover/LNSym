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
import Tactics.BvOmegaBench

namespace AddLoopTandem

/-
Here is a C snippet that describes this program's behavior.

while (x0 != 0) {
  x1 := x1 + 1
  x0 := x0 - 1
}
x0 := x1
-/
def program : Program :=
    def_program
    [
      /- 00000000004005a4 <incr_test>:                             -/
      (0x4005a4#64, 0x14000003#32), /- b        4005b0 <loop_test> -/

      /- 00000000004005a8 <loop>:                                  -/
      (0x4005a8#64, 0x91000421#32), /- add      x1, x1, #0x1       -/
      (0x4005ac#64, 0xd1000400#32), /- sub      x0, x0, #0x1       -/

      /- 00000000004005b0 <loop_test>:                              -/
      (0x4005b0#64, 0xf100001f#32), /- cmp      x0, #0x0            -/
      (0x4005b4#64, 0x54ffffa1#32), /- b.ne     4005a8 <loop>       -/
      (0x4005b8#64, 0xaa0103e0#32), /- mov      x0, x1              -/
      (0x4005bc#64, 0xd65f03c0#32)  /- ret                          -/
      ]

/-- Precondition for the correctness of the Add program. -/
def pre (s : ArmState) : Prop :=
  read_pc s = 0x4005a4#64 ∧
  s.program = program ∧
  read_err s = StateError.None

/-- Specification function. -/
def spec (x0 x1 : BitVec 64) : BitVec 64 :=
  x0 + x1

def post (s0 sf : ArmState) : Prop :=
  read_gpr 64 0#5 sf = spec (read_gpr 64 0#5 s0) (read_gpr 64 1#5 s0) ∧
  read_pc sf = 0x4005bc#64 ∧
  read_err sf = StateError.None ∧
  sf.program = program

def exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = 0x4005bc#64

def cut (s : ArmState) : Bool :=
  match (read_pc s) with
  -- First instruction
  | 0x4005a4#64
  -- Loop guard (branch instruction)
  | 0x4005b4#64
  -- First instruction following the loop
  | 0x4005b8#64
  -- Last instruction
  | 0x4005bc#64 => true
  | _ => false

def loop_inv (s0 si : ArmState) : Prop :=
  let x0 := read_gpr 64 0#5 s0
  let x1 := read_gpr 64 1#5 s0
  let curr_x0 := read_gpr 64 0#5 si
  let curr_x1 := read_gpr 64 1#5 si
  let curr_zf := r (StateField.FLAG PFlag.Z) si
  (curr_x0 <= x0) ∧
  ((curr_zf = 1#1) ↔ (curr_x0 = 0#64)) ∧
  (curr_x1 = x1 + (x0 - curr_x0)) ∧
  read_err si = .None ∧
  si.program = program

def loop_post (s0 si : ArmState) : Prop :=
  read_gpr 64 1#5 si = spec (read_gpr 64 0#5 s0) (read_gpr 64 1#5 s0) ∧
  read_err si = .None ∧
  si.program = program

def assert (s0 si : ArmState) : Prop :=
  pre s0 ∧
  -- Using `match` is preferable to `if` for the `split` tactic (and for
  -- readability).
  match (read_pc si) with
  | 0x4005a4#64 =>
    -- First instruction
    si = s0
  | 0x4005b4#64 =>
    -- Loop guard
    loop_inv s0 si
  | 0x4005b8#64 =>
    -- First instruction following the loop
    loop_post s0 si
  | 0x4005bc#64 =>
    -- Last instruction
    post s0 si
  | _ => False

instance : Spec' ArmState where
  pre    := pre
  post   := post
  exit   := exit
  cut    := cut
  assert := assert

-------------------------------------------------------------------------------
-- Generating the program effects and non-effects

private theorem AddWithCarry.add_one_64 (x : BitVec 64) :
  (AddWithCarry x 0x1#64 0x0#1).fst = x + 0x1#64 := by
  simp only [AddWithCarry, bitvec_rules]
  bv_omega_bench

private theorem AddWithCarry.sub_one_64 (x : BitVec 64) :
  (AddWithCarry x 0xfffffffffffffffe#64 0x1#1).fst = x - 1#64 := by
  simp only [AddWithCarry]
  bv_decide

private theorem AddWithCarry.all_ones_identity_64 (x : BitVec 64) :
  (AddWithCarry x 0xffffffffffffffff#64 0x1#1).fst = x := by
  simp only [AddWithCarry]
  bv_decide

private theorem AddWithCarry.all_ones_zero_flag_64 (x : BitVec 64) :
  ((AddWithCarry x 0xffffffffffffffff#64 0x1#1).snd.z = 1#1) ↔
  (x = 0#64) := by
  simp only [AddWithCarry, bitvec_rules, state_simp_rules]
  repeat split
  · bv_decide
  · bv_decide
  done

-- (FIXME) Print names of generated theorems.
-- set_option trace.gen_step.debug true in
#genStepEqTheorems program

-- (FIXME) Obtain *_cut theorems for each instruction automatically.

theorem program.stepi_0x4005a4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005a4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r (StateField.GPR 0#5) sn = r (StateField.GPR 0#5) s ∧
  r (StateField.GPR 1#5) sn = r (StateField.GPR 1#5) s ∧
  r (StateField.FLAG PFlag.Z) sn = r (StateField.FLAG PFlag.Z) s ∧
  r StateField.PC sn = 0x4005b0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005a4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005a8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005a8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r (StateField.GPR 0#5) sn = r (StateField.GPR 0#5) s ∧
  r (StateField.GPR 1#5) sn = (r (StateField.GPR 0x1#5) s) + 1#64 ∧
  r StateField.PC sn = 0x4005ac#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005a8 h_program h_pc h_err
  simp only [minimal_theory, bitvec_rules] at this
  simp_all (config := {ground := true}) only
            [run, cut, this, AddWithCarry.add_one_64,
             state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005ac_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005ac#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r (StateField.GPR 0#5) sn = r (StateField.GPR 0#5) s - 1#64 ∧
  r (StateField.GPR 1#5) sn = (r (StateField.GPR 0x1#5) s) ∧
  r StateField.PC sn = 0x4005b0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005ac h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all (config := {ground := true}) only
                 [run, cut, this, AddWithCarry.sub_one_64,
                  state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005b0_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005b0#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  cut sn = true ∧
  -- NOTE: We relate the value of x0 in state s to ZF in state sn here.
  ((r (StateField.GPR 0#5) s = 0#64) ↔
   (r (StateField.FLAG PFlag.Z) sn = 1#1)) ∧
  r (StateField.GPR 0#5) sn = r (StateField.GPR 0#5) s ∧
  r (StateField.GPR 1#5) sn = r (StateField.GPR 1#5) s ∧
  r StateField.PC sn = 0x4005b4#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005b0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all (config := {ground := true}) only
                [run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  rw [AddWithCarry.all_ones_zero_flag_64]
  done

-- Branch instruction when s.zf = 1
theorem program.stepi_0x4005b4_cut_zf_1 (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005b4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_zf_1 : r (StateField.FLAG PFlag.Z) s = 1#1)
  (h_step : sn = run 1 s) :
  cut sn = true ∧
  r StateField.PC sn = 0x4005b8#64 ∧
  r (StateField.GPR 0#5) sn = r (StateField.GPR 0#5) s ∧
  r (StateField.GPR 1#5) sn = r (StateField.GPR 1#5) s ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005b4 h_program h_pc h_err
  simp only [run] at h_step
  simp only [minimal_theory, ←h_step] at this
  simp_all only [-h_step, run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

-- Branch instruction when s.zf = 0
theorem program.stepi_0x4005b4_cut_zf_0 (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005b4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_zf_0 : r (StateField.FLAG PFlag.Z) s = 0#1)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x4005a8#64 ∧
  r (StateField.GPR 0#5) sn = r (StateField.GPR 0#5) s ∧
  r (StateField.GPR 1#5) sn = r (StateField.GPR 1#5) s ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005b4 h_program h_pc h_err
  simp only [run] at h_step
  simp only [minimal_theory, ←h_step] at this
  simp_all only [-h_step, run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005b8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005b8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = run 1 s) :
  cut sn = true ∧
  r (StateField.GPR 0#5) sn = r (StateField.GPR 1#5) s ∧
  r StateField.PC sn = 0x4005bc#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program := by
  have := program.stepi_eq_0x4005b8 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

-- (TODO) program.stepi_0x4005bc_cut elided.
-- theorem program.stepi_0x4005bc_cut (s sn : ArmState)
--   (h_program : s.program = program)
--   (h_pc : r StateField.PC s = 0x4005bc#64)
--   (h_err : r StateField.ERR s = StateError.None)
--   (h_sp_aligned : CheckSPAlignment s)
--   (h_step : sn = run 1 s) :
--   cut sn = false := by
--   have := program.stepi_eq_0x4005bc h_program h_pc h_err
--   simp only [minimal_theory] at this

--   simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
--   done

-------------------------------------------------------------------------------

-- Some helper lemmas to prove obligations stemming from `assert`

-- TODO: Upstream?
@[bitvec_rules]
theorem BitVec.le_refl (x : BitVec n) :
  x <= x := by
  exact BitVec.le_of_eq x x rfl

private theorem non_zero_one_bit_is_one {x : BitVec 1}
  (h : ¬ x = 0#1) :
  x = 1#1 := by
  bv_decide

private theorem non_one_bit_is_zero {x : BitVec 1}
  (h : ¬ x = 1#1) :
  x = 0#1 := by
  bv_decide

private theorem crock_lemma (x y z : BitVec 64) :
  x + (y - z) + 1#64 = x + (y - (z - 1#64)) := by
  -- (FIXME) Without this apply below, bv_omega_bench crashes my editor.
  apply BitVec.eq_sub_iff_add_eq.mp
  bv_omega_bench

private theorem loop_inv_x0_helper_lemma {x y : BitVec 64} (h1 : x ≤ y)
  (h2 : ¬(x = 0#64)) :
  x - 0x1#64 ≤ y := by
  bv_omega_bench

-------------------------------------------------------------------------------

theorem cassert_eq (s0 si : ArmState) (i : Nat) :
  Correctness.cassert s0 si i = if cut si then (i, assert s0 si)
                       else Correctness.cassert s0 (run 1 si) (i + 1) := by
  rw [Correctness.cassert_eq]
  simp only [Sys.next, Spec'.cut, Spec'.assert, run]
  done

def loop_clock (x0 : BitVec 64) : Nat :=
  if h : x0 = 0#64 then
    1
  else
    have : x0 - 0x1#64 < x0 := by
     bv_omega_bench
    4 + loop_clock (x0 - 1)
  termination_by x0.toNat

theorem loop_clock_inv_lemma (h : ¬x = 0x0#64) :
  loop_clock (x - 0x1#64) < loop_clock x := by
  generalize h_xn : x.toNat = xn
  have h_xn_ge_1 : 1 ≤ xn := by bv_omega_bench
  induction xn, h_xn_ge_1 using Nat.le_induction generalizing x
  case base =>
    have h_x_eq_1 : x = 1#64 := by bv_omega_bench
    unfold loop_clock
    simp only [h_x_eq_1, BitVec.sub_self, BitVec.ofNat_eq_ofNat,
               reduceDIte, gt_iff_lt, BitVec.reduceEq]
    omega
  case succ =>
    rename_i xn' h_xn' h_inv
    unfold loop_clock
    simp only [BitVec.ofNat_eq_ofNat, dite_eq_ite, gt_iff_lt]
    have h1 : ¬ x - 0x1#64 = 0x0#64 := by bv_omega_bench
    have h2 : (x - 0x1#64).toNat = xn' := by bv_omega_bench
    simp only [h, h1, h2, h_inv,
               reduceIte, Nat.add_lt_add_iff_left, not_false_eq_true]
  done

def clock (s : ArmState) : Nat :=
  let x0 := r (StateField.GPR 0#5) s
  if x0 = 0#64 then
    2 + 1 + 1
  else
    2 + ((loop_clock x0) + 1)

/--
Our formalization of the rank of a cutpoint for this program is the number of
instructions that remain to be executed from that point.
-/
def rank (si : ArmState) : Nat :=
  match (read_pc si) with
  | 0x4005a4#64 =>
    -- First instruction
    clock si
  | 0x4005b4#64 =>
    -- Loop guard
    (loop_clock (r (StateField.GPR 0#5) si)) + 1
  | 0x4005b8#64 =>
    -- First instruction following the loop
    1
  | 0x4005bc#64 =>
    -- Last instruction
    0
  | _ =>
   -- No cutpoints remain
    0

theorem loop_clk_plus_one_lt_clock :
  (loop_clock (r (StateField.GPR 0x0#5) s)) + 1 < clock s := by
  simp only [clock]
  unfold loop_clock
  split <;> omega

theorem correctness :
  Correctness ArmState := by
  apply Correctness.by_the_method rank
  case v1 =>
    intro s0 h_pre
    simp_all only [Spec.pre, pre, Spec'.assert, assert,
                    minimal_theory]
  case v2 =>
    intro sf h_exit
    simp_all only [Spec.exit, exit, Spec'.cut, cut,
                    state_simp_rules, minimal_theory]
  case v3 =>
    intro s0 sf h_assert h_exit
    -- (FIXME) Remove Spec.post to replicate bug where simp_all somehow
    -- aggressively makes the goal unprovable.
    simp_all only [Spec'.assert, Spec.exit, assert, exit, Spec.post]
  case v4 =>
    intro s0 si h_assert h_exit
    simp only [Correctness.arm_run]
    simp [Spec.exit, exit] at h_exit
    simp only [Spec'.assert, assert, h_exit, minimal_theory] at h_assert
    obtain ⟨h_assert_pre, h_assert⟩ := h_assert
    have h_pre := h_assert_pre
    simp only [pre, state_simp_rules] at h_assert_pre
    simp_all only [Spec'.assert, Spec.exit, assert, exit, Spec'.cut,
                   minimal_theory, state_simp_rules]
    split at h_assert
    · -- Next cutpoint from 0x4005a4#64 (first instruction)
      subst si
      -- Begin: Symbolic simulation
      -- Instruction 1
      generalize h_s0_run_1 : run 1 s0 = s1
      have h_s1 := @program.stepi_0x4005a4_cut s0 s1
                    (by simp only [*])
                    (by simp only [*])
                    (by simp only [*])
                    (by simp only [*])
      rw [cassert_eq]
      simp only [h_s1, Nat.reduceAdd, minimal_theory]
      -- Instruction 2
      generalize h_s1_run_1 : run 1 s1 = s2
      have h_s2 := @program.stepi_0x4005b0_cut s1 s2
                    (by simp only [*])
                    (by simp only [*])
                    (by simp only [*])
                    (by simp only [*])
      rw [cassert_eq]
      simp only [h_s2, Nat.reduceAdd, minimal_theory]
      -- Effects Aggregation
      simp only [h_s1] at h_s2
      clear h_s1
      have h_s2_run : run 2 s0 = s2 := by
        simp only [←h_s1_run_1, ←h_s0_run_1, ←run_plus, Nat.reduceAdd]
      -- End: Symbolic Simulation
      simp only [assert, h_pre, h_s2, loop_inv,
                 state_simp_rules, bitvec_rules, minimal_theory]
      apply Exists.intro 2
      simp only [h_s2_run, h_s2, rank, h_assert_pre,
                 loop_clk_plus_one_lt_clock,
                 state_simp_rules, minimal_theory]
      done
    · -- Next cutpoint from 0x4005b4#64 (loop guard)
      rename_i h_assert_pc
      simp only [loop_inv, state_simp_rules] at h_assert
      -- Begin: Symbolic Simulation
      -- We case-split first because we are at a conditional branch instruction.
      by_cases h_branch : r (StateField.FLAG PFlag.Z) si = 0x1#1
      case pos => -- Branch not taken
        have h_si_x0 : r (StateField.GPR 0#5) si = 0#64 := by
          simp only [h_branch, minimal_theory] at h_assert
          simp only [h_assert]
        -- Instruction 1
        generalize h_si_run_1 : run 1 si = s1
        have h_s1 := @program.stepi_0x4005b4_cut_zf_1 si s1
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
        rw [cassert_eq]
        simp only [h_s1, Nat.reduceAdd, minimal_theory]
        -- End: Symbolic simulation
        simp only [assert, h_pre, h_s1, loop_post, spec, h_assert,
                   h_si_x0, BitVec.add_comm,
                   state_simp_rules, bitvec_rules, minimal_theory]
        apply Exists.intro 1
        simp only [h_si_run_1, h_s1,  rank, h_assert_pc, h_si_x0,
                   state_simp_rules, minimal_theory]
        simp (config := {ground := true}) only
        done
      case neg => -- Branch taken
        have h_si_zf : r (StateField.FLAG PFlag.Z) si = 0#1 := by
          rw [non_one_bit_is_zero h_branch]
        have h_si_x0 : ¬(r (StateField.GPR 0#5) si = 0#64) := by
          simp only [h_branch, minimal_theory] at h_assert
          simp only [h_assert, minimal_theory]
        -- Begin: Symbolic Simulation
        -- Instruction 1
        generalize h_si_run_1 : run 1 si = s1
        have h_s1 := @program.stepi_0x4005b4_cut_zf_0 si s1
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
        rw [cassert_eq]
        simp only [h_s1, Nat.reduceAdd, minimal_theory]
        -- Instruction 2
        generalize h_s1_run_1 : run 1 s1 = s2
        have h_s2 := @program.stepi_0x4005a8_cut s1 s2
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
        rw [cassert_eq]
        simp only [h_s2, Nat.reduceAdd, minimal_theory]
        -- Instruction 3
        generalize h_s2_run_1 : run 1 s2 = s3
        have h_s3 := @program.stepi_0x4005ac_cut s2 s3
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
                      (by simp only [*])
        rw [cassert_eq]
        simp only [h_s3, Nat.reduceAdd, minimal_theory]
        -- Instruction 4
        generalize h_s3_run_1 : run 1 s3 = s4
        have h_s4 := @program.stepi_0x4005b0_cut s3 s4
                     (by simp only [*])
                     (by simp only [*])
                     (by simp only [*])
                     (by simp only [*])
        rw [cassert_eq]
        simp only [h_s4, Nat.reduceAdd, minimal_theory]
        -- Effects Aggregation
        simp only [h_s1, h_s2, h_s3] at h_s4
        clear h_s1 h_s2 h_s3
        have h_s4_run : run 4 si = s4 := by
          simp only [←h_si_run_1, ←h_s3_run_1, ←h_s2_run_1, ←h_s1_run_1,
                     ←run_plus, Nat.reduceAdd]
        -- End: Symbolic Simulation
        simp only [assert, h_pre, h_s4, loop_inv, h_assert,
                   loop_inv_x0_helper_lemma h_assert.left h_si_x0,
                   state_simp_rules, bitvec_rules, minimal_theory]
        rw [crock_lemma]
        simp only [minimal_theory]
        apply Exists.intro 4
        simp only [h_s4_run, h_s4, rank, h_assert_pc,
                   state_simp_rules, minimal_theory]
        have := @loop_clock_inv_lemma _ h_si_x0
        omega
      done
    · -- Next cutpoint at 0x4005b8#64 (first instruction following the loop)
      rename_i h_assert_pc
      simp only [loop_post, state_simp_rules] at h_assert
      -- Begin: Symbolic Simulation
      generalize h_s1_run_1 : run 1 si = s1
      have h_s1 := @program.stepi_0x4005b8_cut si s1
                    (by simp only [*])
                    (by simp only [*])
                    (by simp only [*])
                    (by simp only [*])
      rw [cassert_eq]
      simp only [h_s1, Nat.reduceAdd, minimal_theory]
      -- End: Symbolic Simulation
      simp only [assert, h_pre, h_s1, post, h_assert,
                 state_simp_rules, bitvec_rules, minimal_theory]
      apply Exists.intro 1
      simp only [h_s1_run_1, h_s1, rank, h_assert_pc,
                 Nat.lt_add_one,
                 state_simp_rules, minimal_theory]
      done
    · -- Next cutpoint from 0x4005bc#64 (last instruction)
      -- No such cutpoint exists.
      contradiction
    · -- No further cutpoints exist.
      simp_all only
    done

-------------------------------------------------------------------------------
end AddLoopTandem
