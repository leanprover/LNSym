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
  read_err s = StateError.None ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment s

/-- Specification function. -/
def spec (x0 x1 : BitVec 64) : BitVec 64 :=
  x0 + x1

def post (s0 sf : ArmState) : Prop :=
  read_gpr 64 0#5 sf = spec (read_gpr 64 0#5 s0) (read_gpr 64 1#5 s0) ∧
  read_pc sf = 0x4005bc#64 ∧
  read_err sf = StateError.None ∧
  sf.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment sf

def exit (s : ArmState) : Prop :=
  -- (FIXME) Let's consider the state where we are poised to execute `ret` as an
  -- exit state for now.
  read_pc s = 0x4005bc#64

def cut (s : ArmState) : Bool :=
  -- First instruction
  read_pc s = 0x4005a4#64 ||
  -- Loop guard (branch instruction)
  read_pc s = 0x4005b4#64 ||
  -- First instruction following the loop
  read_pc s = 0x4005b8#64 ||
  -- Last instruction
  read_pc s = 0x4005bc#64

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
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si

def loop_post (s0 si : ArmState) : Prop :=
  read_gpr 64 1#5 si = spec (read_gpr 64 0#5 s0) (read_gpr 64 1#5 s0) ∧
  read_err si = .None ∧
  si.program = program ∧
  -- (FIXME) We don't really need the stack pointer to be aligned, but the
  -- `sym_n` tactic expects this. Can we make this optional?
  CheckSPAlignment si

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

-- (FIXME) Print names of generated theorems.
-- set_option trace.gen_step.debug true in
#genStepEqTheorems program

-- (FIXME) Obtain *_cut theorems for each instruction automatically.

theorem program.stepi_0x4005a4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005a4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false := by
  have := program.stepi_eq_0x4005a4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this,
                 state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005a8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005a8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x4005ac#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005a8 h_program h_pc h_err
  simp only [minimal_theory, bitvec_rules] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005ac_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005ac#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = false ∧
  r StateField.PC sn = 0x4005b0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005ac h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem program.stepi_0x4005b0_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005b0#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = true ∧
  r StateField.PC sn = 0x4005b4#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005b0 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  done

-- Branch instruction!
theorem program.stepi_0x4005b4_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005b4#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = (r (StateField.FLAG PFlag.Z) s = 1#1) ∧
  r StateField.PC sn = (if (r (StateField.FLAG PFlag.Z) s = 1#1) then
                                  0x4005b8#64
                              else
                                  0x4005a8#64) ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
  have := program.stepi_eq_0x4005b4 h_program h_pc h_err
  simp only [minimal_theory] at this
  simp_all only [run, cut, this, state_simp_rules, bitvec_rules, minimal_theory]
  split
  · rename_i h
    simp_all only [state_simp_rules, bitvec_rules, minimal_theory]
  · rename_i h; simp only [minimal_theory] at h
    simp_all only [state_simp_rules, minimal_theory]
    done

theorem program.stepi_0x4005b8_cut (s sn : ArmState)
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x4005b8#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_sp_aligned : CheckSPAlignment s)
  (h_step : sn = run 1 s) :
  cut sn = true ∧
  r StateField.PC sn = 0x4005bc#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
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

private theorem non_zero_one_bit_is_one {x : BitVec 1}
  (h : ¬ x = 0#1) :
  x = 1#1 := by
  bv_decide

private theorem AddWithCarry.sub_one_64 (x : BitVec 64) :
  (AddWithCarry x 0xfffffffffffffffe#64 0x1#1).fst = x - 1#64 := by
  simp only [AddWithCarry]
  bv_decide

private theorem loop_inv_x0_le {x y : BitVec 64}
  (h_assert_x0 : x ≤ y)
  (h_assert_x0_nz : ¬x = 0x0#64) :
  x - 0x1#64 ≤ y := by
  bv_omega

private theorem AddWithCarry.add_one_64 (x : BitVec 64) :
  (AddWithCarry x 0x1#64 0x0#1).fst = x + 0x1#64 := by
  simp only [AddWithCarry, bitvec_rules]
  bv_omega

private theorem crock_lemma (x y z : BitVec 64) :
  x + (y - z) + 1#64 = x + (y - (z - 1#64)) := by
  -- (FIXME) Without this apply below, bv_omega crashes my editor.
  apply BitVec.eq_sub_iff_add_eq.mp
  bv_omega

-- TODO: Upstream?
@[bitvec_rules]
theorem BitVec.le_refl (x : BitVec n) :
  x <= x := by
  exact BitVec.le_of_eq x x rfl

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

theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_assertions
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
    obtain ⟨h_pre, h_assert⟩ := h_assert
    have ⟨h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned⟩ := h_pre
    simp_all only [Spec'.assert, Spec.exit, assert, exit,
                   minimal_theory, state_simp_rules]
    split at h_assert
    · -- Next cutpoint from 0x4005a4#64 (first instruction)
      subst si
      -- Begin: Symbolic simulation
      sym_i_cassert 0 cassert_eq program.stepi_0x4005a4_cut
      sym_i_cassert 1 cassert_eq program.stepi_0x4005b0_cut
      -- End: Symbolic simulation
      simp only [assert, h_pre, loop_inv,
                 h_s2_pc, h_s2_err, h_s2_program, h_s2_sp_aligned,
                 state_simp_rules, bitvec_rules, minimal_theory]
      simp only [h_step_2, h_step_1,
                 state_simp_rules, bitvec_rules, minimal_theory]
      simp (config := {ground := true}) only
      rw [AddWithCarry.all_ones_zero_flag_64]
      done
    · -- Next cutpoint from 0x4005b4#64 (loop guard)
      --
      -- (FIXME @shilpi) Hack for awful sym_i_cassert tactic which expects a
      -- numeric suffix for the state variables.
      -- generalize h_si_s1 : si = s1; subst si
      --
      rename_i h_inv_pc
      obtain ⟨h_inv_x0_lt, h_inv_zf_x0, h_inv_x1,
              h_inv_err, h_inv_program, h_inv_sp_aligned⟩ := h_assert
      simp only [state_simp_rules, bitvec_rules, minimal_theory] at *
      by_cases h_cond_holds : r (StateField.FLAG PFlag.Z) si = 0x0#1
      case pos =>
        have h_inv_x0_nz : ¬ r (StateField.GPR 0#5) si = 0#64 := by
          -- TODO: missing iff_rule?
          simp (config := {decide := true}) only
            [h_cond_holds, minimal_theory] at h_inv_zf_x0
          assumption
        -- Begin: Symbolic simulation
        -- Instruction 1 (branch instruction)
        rw [cassert_eq]
        generalize h_run : run 1 si = s1
        replace h_run := (h_run).symm
        -- (TODO) Better handling of branch instructions.
        -- sym_n 1 at si
        have stepi_si : stepi si = s1 := by simp only [h_run, run]
        have h_step_1 := @program.stepi_eq_0x4005b4 si
                          h_inv_program h_inv_pc h_inv_err
        rw [stepi_si] at h_step_1
        have h_cut := @program.stepi_0x4005b4_cut si s1
                       h_inv_program h_inv_pc h_inv_err h_inv_sp_aligned
                       h_run
        simp only [h_cond_holds, bitvec_rules, minimal_theory]
          at h_step_1 h_cut
        have h_cut' : cut s1 = false := by
          -- TODO: missing iff_rule?
          simp (config := {decide := true}) only [minimal_theory] at h_cut
          simp only [h_cut]
          done
        simp only [h_cut', minimal_theory]
        clear stepi_si h_run
        (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
         (all_goals (try assumption)))
        clear h_cut h_cut'
        -- Instruction 2
        sym_i_cassert 1 cassert_eq program.stepi_0x4005a8_cut
        sym_i_cassert 2 cassert_eq program.stepi_0x4005ac_cut
        sym_i_cassert 3 cassert_eq program.stepi_0x4005b0_cut
        -- End: Symbolic simulation
        simp only [assert, loop_inv, h_pre,
                   h_s4_pc, h_s4_err, h_s4_program, h_s4_sp_aligned,
                   state_simp_rules, bitvec_rules, minimal_theory]
        -- Aggregate program effects here.
        simp (config := {ground := true}) only at h_step_4 h_step_3 h_step_2
        simp only [h_step_4, h_step_3, h_step_2, h_step_1,
                   state_simp_rules, bitvec_rules, minimal_theory]
        clear h_step_4 h_step_3 h_step_2 h_step_1
        rw [AddWithCarry.sub_one_64,
            AddWithCarry.all_ones_zero_flag_64,
            AddWithCarry.add_one_64]
        -- cse (config := { processHyps := .allHyps })
        simp only [h_inv_x1, crock_lemma, minimal_theory]
        apply loop_inv_x0_le h_inv_x0_lt h_inv_x0_nz
        done
      case neg =>
        have h_inv_zf : r (StateField.FLAG PFlag.Z) si = 1#1 := by
          -- (FIXME) Ugh, tedious.
          rw [@non_zero_one_bit_is_one (r (StateField.FLAG PFlag.Z) si)]
          assumption
        simp only [h_inv_zf, minimal_theory] at h_inv_zf_x0
        -- Begin: Symbolic simulation
        -- Instruction 1 (branch instruction)
        rw [cassert_eq]
        generalize h_run : run 1 si = s1
        replace h_run := (h_run).symm
        -- (TODO) Better handling of branch instructions.
        -- sym_n 1 at si
        have stepi_si : stepi si = s1 := by simp only [h_run, run]
        have h_step_1 := @program.stepi_eq_0x4005b4 si
                          h_inv_program h_inv_pc h_inv_err
        rw [stepi_si] at h_step_1
        have h_cut := @program.stepi_0x4005b4_cut si s1
                       h_inv_program h_inv_pc h_inv_err h_inv_sp_aligned
                       h_run
        simp only [h_cond_holds, h_inv_zf, bitvec_rules, minimal_theory]
          at h_step_1 h_cut
        simp only [h_cut, minimal_theory]
        clear h_cut stepi_si h_run
        (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
          all_goals (try assumption))
        -- End: Symbolic simulation
        simp only [assert, loop_post,
                   h_pre, h_s1_pc, h_s1_err, h_s1_program, h_s1_sp_aligned,
                   state_simp_rules, bitvec_rules, minimal_theory]
        -- Aggregate program effects here.
        simp only [h_step_1, state_simp_rules, bitvec_rules, minimal_theory]
        simp only [spec, h_inv_x1, h_inv_zf_x0, bitvec_rules, BitVec.add_comm]
        done
    · -- Next cutpoint from 0x4005b8#64 (first instruction after loop)
      --
      -- (FIXME @shilpi) Hack for awful sym_i_cassert tactic which expects a
      -- numeric suffix for the state variables.
      generalize h_si_s1 : si = s1; subst si
      --
      rename_i h_s1_pc
      obtain ⟨h_s1_x1, h_s1_err, h_s1_program, h_s1_sp_aligned⟩ := h_assert
      simp only [state_simp_rules, bitvec_rules, minimal_theory] at *
      -- Begin: Symbolic simulation
      sym_i_cassert 1 cassert_eq program.stepi_0x4005b8_cut
      -- End: Symbolic simulation
      simp only [assert, post,
                 h_pre, h_s2_pc, h_s2_err, h_s2_sp_aligned, h_s2_program,
                 state_simp_rules, bitvec_rules, minimal_theory]
      simp only [h_step_2, spec, h_s1_x1,
                 state_simp_rules, bitvec_rules, minimal_theory]
      done
    · -- Next cutpoint from 0x4005bc#64 (last instruction)
      -- No such cutpoint exists.
      contradiction
    · -- No further cutpoints exist.
      simp_all only
  done

-------------------------------------------------------------------------------

def loop_clock (x0 : BitVec 64) : Nat :=
  if h : x0 = 0#64 then
    1
  else
    have : x0 - 0x1#64 < x0 := by
     bv_omega
    4 + loop_clock (x0 - 1)
  termination_by x0.toNat

theorem loop_clock_inv_lemma (h : ¬x = 0x0#64) :
  loop_clock (x - 0x1#64) < loop_clock x := by
  generalize h_xn : x.toNat = xn
  have h_xn_ge_1 : 1 ≤ xn := by bv_omega
  induction xn, h_xn_ge_1 using Nat.le_induction generalizing x
  case base =>
    have h_x_eq_1 : x = 1#64 := by bv_omega
    unfold loop_clock
    simp only [h_x_eq_1, BitVec.sub_self, BitVec.ofNat_eq_ofNat,
               reduceDIte, gt_iff_lt, BitVec.reduceEq]
    omega
  case succ =>
    rename_i xn' h_xn' h_inv
    unfold loop_clock
    simp only [BitVec.ofNat_eq_ofNat, dite_eq_ite, gt_iff_lt]
    have h1 : ¬ x - 0x1#64 = 0x0#64 := by bv_omega
    have h2 : (x - 0x1#64).toNat = xn' := by bv_omega
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

theorem rank_decreases_eq (si sn : ArmState) (i : Nat) :
  Correctness.rank_decreases rank si sn i =
    if cut sn then (i, rank sn < rank si)
              else Correctness.rank_decreases rank si (run 1 sn) (i + 1) := by
  rw [Correctness.rank_decreases_eq]
  simp only [Spec'.cut, Sys.next, run]
  done

-- (FIXME) The termination proof looks very similar to the partial correctness
-- one, and we ought to do them in one swoop.
theorem termination :
  Termination ArmState := by
  apply Correctness.termination_from_decreasing_rank rank
  case v1 =>
    intro s0 h_pre
    simp_all only [Spec.pre, pre, Spec'.assert, assert,
                    minimal_theory]
  case v2 =>
    intro s0 si h_assert h_not_exit
    simp only [Correctness.arm_run]
    simp [Spec.exit, exit] at h_not_exit
    simp only [Spec'.assert, assert, h_not_exit, minimal_theory] at h_assert
    obtain ⟨h_pre, h_assert⟩ := h_assert
    have ⟨h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned⟩ := h_pre
    simp_all only [Spec'.assert, Spec.exit, assert, exit,
                   minimal_theory, state_simp_rules]
    split at h_assert
    · -- Next cutpoint from 0x4005a4#64 (first instruction)
      subst si
      -- Begin: Symbolic simulation
      sym_i_cassert 0 rank_decreases_eq program.stepi_0x4005a4_cut
      sym_i_cassert 1 rank_decreases_eq program.stepi_0x4005b0_cut
      -- End: Symbolic simulation
      simp only [rank, h_s0_pc, h_s2_pc, state_simp_rules]
      simp (config := {ground := true}) only at h_step_2
      simp only [h_step_2, h_step_1, loop_clk_plus_one_lt_clock,
                 state_simp_rules, bitvec_rules, minimal_theory]
      done
    · -- Next cutpoint from 0x4005b4#64 (loop guard)
      --
      -- (FIXME @shilpi) Hack for awful sym_i_cassert tactic which expects a
      -- numeric suffix for the state variables.
      -- generalize h_si_s1 : si = s1; subst si
      --
      rename_i h_inv_pc
      obtain ⟨h_inv_x0_lt, h_inv_zf_x0, h_inv_x1,
              h_inv_err, h_inv_program, h_inv_sp_aligned⟩ := h_assert
      simp only [state_simp_rules, bitvec_rules, minimal_theory] at *
      by_cases h_cond_holds : r (StateField.FLAG PFlag.Z) si = 0x0#1
      case pos =>
        have h_inv_x0_nz : ¬ r (StateField.GPR 0#5) si = 0#64 := by
          -- TODO: missing iff_rule?
          simp (config := {decide := true}) only
            [h_cond_holds, minimal_theory] at h_inv_zf_x0
          assumption
        -- Begin: Symbolic simulation
        -- Instruction 1 (branch instruction)
        rw [rank_decreases_eq]
        generalize h_run : run 1 si = s1
        replace h_run := (h_run).symm
        -- (TODO) Better handling of branch instructions.
        -- sym_n 1 at si
        have stepi_si : stepi si = s1 := by simp only [h_run, run]
        have h_step_1 := @program.stepi_eq_0x4005b4 si
                          h_inv_program h_inv_pc h_inv_err
        rw [stepi_si] at h_step_1
        have h_cut := @program.stepi_0x4005b4_cut si s1
                       h_inv_program h_inv_pc h_inv_err h_inv_sp_aligned
                       h_run
        simp only [h_cond_holds, bitvec_rules, minimal_theory]
          at h_step_1 h_cut
        have h_cut' : cut s1 = false := by
          -- TODO: missing iff_rule?
          simp (config := {decide := true}) only [minimal_theory] at h_cut
          simp only [h_cut]
          done
        simp only [h_cut', minimal_theory]
        clear stepi_si h_run
        (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
         (all_goals (try assumption)))
        clear h_cut h_cut'
        -- Instruction 2
        sym_i_cassert 1 rank_decreases_eq program.stepi_0x4005a8_cut
        sym_i_cassert 2 rank_decreases_eq program.stepi_0x4005ac_cut
        sym_i_cassert 3 rank_decreases_eq program.stepi_0x4005b0_cut
        -- End: Symbolic simulation
        simp only [rank,
                   h_s4_pc, h_inv_pc,
                   state_simp_rules, bitvec_rules, minimal_theory]
        -- Aggregate program effects here.
        simp (config := {ground := true}) only at h_step_4 h_step_3 h_step_2
        simp only [h_step_4, h_step_3, h_step_2, h_step_1,
                   state_simp_rules, bitvec_rules, minimal_theory]
        clear h_step_4 h_step_3 h_step_2 h_step_1
        rw [AddWithCarry.sub_one_64]
        have := loop_clock_inv_lemma h_inv_x0_nz
        omega
        done
      case neg =>
        have h_inv_zf : r (StateField.FLAG PFlag.Z) si = 1#1 := by
          -- (FIXME) Ugh, tedious.
          rw [@non_zero_one_bit_is_one (r (StateField.FLAG PFlag.Z) si)]
          assumption
        simp only [h_inv_zf, minimal_theory] at h_inv_zf_x0
        -- Begin: Symbolic simulation
        -- Instruction 1 (branch instruction)
        rw [rank_decreases_eq]
        generalize h_run : run 1 si = s1
        replace h_run := (h_run).symm
        -- (TODO) Better handling of branch instructions.
        -- sym_n 1 at si
        have stepi_si : stepi si = s1 := by simp only [h_run, run]
        have h_step_1 := @program.stepi_eq_0x4005b4 si
                          h_inv_program h_inv_pc h_inv_err
        rw [stepi_si] at h_step_1
        have h_cut := @program.stepi_0x4005b4_cut si s1
                       h_inv_program h_inv_pc h_inv_err h_inv_sp_aligned
                       h_run
        simp only [h_cond_holds, h_inv_zf, bitvec_rules, minimal_theory]
          at h_step_1 h_cut
        simp only [h_cut, minimal_theory]
        clear h_cut stepi_si h_run
        (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
          all_goals (try assumption))
        -- End: Symbolic simulation
        simp only [rank,
                   h_s1_pc, h_inv_pc, h_inv_zf_x0,
                   state_simp_rules, bitvec_rules, minimal_theory]
        simp (config := {ground := true}) only
        done
    · -- Next cutpoint from 0x4005b8#64 (first instruction after loop)
      --
      -- (FIXME @shilpi) Hack for awful sym_i_cassert tactic which expects a
      -- numeric suffix for the state variables.
      generalize h_si_s1 : si = s1; subst si
      --
      rename_i h_s1_pc
      obtain ⟨h_s1_x1, h_s1_err, h_s1_program, h_s1_sp_aligned⟩ := h_assert
      simp only [state_simp_rules, bitvec_rules, minimal_theory] at *
      -- Begin: Symbolic simulation
      sym_i_cassert 1 rank_decreases_eq program.stepi_0x4005b8_cut
      -- End: Symbolic simulation
      simp only [rank, h_s2_pc, h_s1_pc,
                 state_simp_rules, bitvec_rules, minimal_theory]
      done
    · -- Next cutpoint from 0x4005bc#64 (last instruction)
      -- No such cutpoint exists.
      contradiction
    · -- No further cutpoints exist.
      simp_all only
  done

end AddLoopTandem
