/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel

Experimental: Use the Correctness module to prove that this program computes the
following via a naive loop that iterates over `x0`:
`x0 := x0 + x1`
-/
import Arm
import Tactics.StepThms
import Tactics.Sym
import Correctness.ArmSpec

namespace AddLoop

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

theorem AddLoop.csteps_eq (s : ArmState) (i : Nat) :
  Correctness.csteps s i = if cut s then i
                           else Correctness.csteps (run 1 s) (i + 1) := by
  rw [Correctness.csteps_eq]
  simp only [Sys.next, Spec'.cut, run]
  done

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
  cut sn = false ∧
  r StateField.PC sn = 0x4005b0#64 ∧
  r StateField.ERR sn = .None ∧
  sn.program = program ∧
  CheckSPAlignment sn := by
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

theorem program.stepi_eq_0x4005b8_cut (s sn : ArmState)
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

-------------------------------------------------------------------------------

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

theorem nextc_to_run_from_0x4005a4 (h : pre s0) :
  (Correctness.nextc (Sys.run s0 1)) = run 2 s0 := by
  simp only [pre, state_simp_rules] at h
  obtain ⟨h_s0_pc, h_s0_program, h_s0_err⟩ := h
  simp only
    [Correctness.nextc, Correctness.arm_run,
     Spec'.cut, minimal_theory]

  rw [AddLoop.csteps_eq]
  have h_step_1 := program.stepi_0x4005a4_cut s0 (run 1 s0)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s1 : run 1 s0 = s1 at h_step_1

  -- Stop when the *_cut theorem says (cut <state>) = true.
  rw [AddLoop.csteps_eq]
  have h_step_2 := program.stepi_0x4005b0_cut s1 (run 1 s1)
  simp_all only [minimal_theory]
  generalize h_s2 : run 1 s1 = s2 at h_step_2

  simp only [←h_s2, ←h_s1, ←run_plus]
  done

theorem effects_of_nextc_from_0x4005a4
  (h_pre : pre s0)
  (_h_pc : r StateField.PC s0 = 0x4005a4#64)
  (h_run : sf = (Correctness.nextc (Sys.run s0 1))) :
  -- I've elided irrelevant effects and non-effects for now.
  sf.program = program ∧
  r StateField.PC sf = 0x4005b4#64 ∧
  r StateField.ERR sf = .None ∧
  ((r (StateField.FLAG PFlag.Z) sf = 1#1) ↔
   (r (StateField.GPR 0x0#5) s0 = 0x0#64)) ∧
  r (StateField.GPR 0#5) sf = r (StateField.GPR 0#5) s0 ∧
  r (StateField.GPR 1#5) sf = r (StateField.GPR 1#5) s0 ∧
  CheckSPAlignment sf := by
  -- Prelude
  rw [nextc_to_run_from_0x4005a4 h_pre] at h_run
  -- TODO: Tactic to "explode" conjunctions?
  obtain ⟨h_s0_pc, h_s0_program, h_s0_err, h_s0_sp_aligned⟩ := h_pre
  -- Symbolic simulation
  -- (FIXME) sym_n doesn't play well with unconditional branches.
  /-
  application type mismatch
  program.stepi_0x4005a8 s1 s2 h_s1_program h_s1_pc
  argument
  h_s1_pc
  has type
  r StateField.PC s1 = 0x4005b0#64 : Prop
  but is expected to have type
  r StateField.PC s1 = 0x4005a8#64 : Prop
  -/
  -- sym_n 2
  sym_n 1 at s0
  sym_n 1 at s1
  simp (config := {ground := true}) only [*, state_simp_rules, bitvec_rules, minimal_theory]
  rw [AddWithCarry.all_ones_zero_flag_64]
  done

-------------------------------------------------------------------------------

theorem nextc_to_run_from_0x4005b4_cond_holds_true (_h_pre : pre s0)
  (h_pc : r StateField.PC si = 0x4005b4#64)
  (h_cond_holds_true : r (StateField.FLAG PFlag.Z) si = 0#1)
  (h_inv : loop_inv s0 si) :
  (Correctness.nextc (Sys.run si 1)) = run 4 si := by
  simp only [pre, loop_inv, state_simp_rules] at *
  obtain ⟨_h_inv_x0_le, h_inv_z, h_inv_x1, h_inv_err,
          h_inv_program, h_inv_sp_aligned⟩ := h_inv
  simp only
    [Correctness.nextc, Correctness.arm_run,
     Spec'.cut, minimal_theory]

  rw [AddLoop.csteps_eq]
  have h_step_1 := program.stepi_0x4005b4_cut si (run 1 si)
  simp_all only [minimal_theory, bitvec_rules]
  -- (FIXME) Why do we need this decide?
  simp (config := {decide := true}) only [*, minimal_theory] at h_inv_z
  simp_all only [h_inv_z, minimal_theory]
  --
  generalize h_s1 : run 1 si = s1 at h_step_1

  rw [AddLoop.csteps_eq]
  have h_step_2 := program.stepi_0x4005a8_cut s1 (run 1 s1)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s2 : run 1 s1 = s2 at h_step_2

  rw [AddLoop.csteps_eq]
  have h_step_3 := program.stepi_0x4005ac_cut s2 (run 1 s2)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s3 : run 1 s2 = s3 at h_step_3

  -- Stop when the *_cut theorem says (cut <state>) = true.
  rw [AddLoop.csteps_eq]
  have h_step_4 := program.stepi_0x4005b0_cut s3 (run 1 s3)
  simp_all only [minimal_theory, bitvec_rules]
  generalize h_s4 : run 1 s3 = s4 at h_step_4

  -- (FIXME): Ugh, obtaining the intermediate states in terms of each other and
  -- the initial states is such a pain!
  have h_s4_s1 : s4 = run 3 s1 := by
    simp only [←h_s4, ←h_s3, ←run_plus, ←h_s2,
                minimal_theory, bitvec_rules]
  simp only [←h_s4_s1, h_step_4,
              bitvec_rules, minimal_theory]
  simp only [h_s4_s1, ←h_s1, ←run_plus]
  done

private theorem non_zero_one_bit_is_one (x : BitVec 1)
  (h : ¬ x = 0#1) :
  x = 1#1 := by
  bv_decide

theorem nextc_to_run_from_0x4005b4_cond_holds_false (_h_pre : pre s0)
  (h_pc : r StateField.PC si = 0x4005b4#64)
  (h_cond_holds_false : ¬ (r (StateField.FLAG PFlag.Z) si = 0#1))
  (h_inv : loop_inv s0 si) :
  (Correctness.nextc (Sys.run si 1)) = run 1 si := by
  simp only [pre, loop_inv, state_simp_rules] at *
  obtain ⟨_h_inv_x0_le, h_inv_z, h_inv_x1, h_inv_err,
          h_inv_program, h_inv_sp_aligned⟩ := h_inv
  simp only
    [Correctness.nextc, Correctness.arm_run,
     Spec'.cut, minimal_theory]

  -- Stop when the *_cut theorem says (cut <state>) = true.
  rw [AddLoop.csteps_eq]
  have h_step_1 := program.stepi_0x4005b4_cut si (run 1 si)
  simp_all only [non_zero_one_bit_is_one, minimal_theory, bitvec_rules]
  generalize _h_s1 : run 1 si = s1 at h_step_1

  simp only [run, h_step_1, minimal_theory]
  done

private theorem AddWithCarry.sub_one_64 (x : BitVec 64) :
  (AddWithCarry x 0xfffffffffffffffe#64 0x1#1).fst = x - 1#64 := by
  simp only [AddWithCarry]
  bv_decide

theorem effects_of_nextc_from_0x4005b4_cond_holds_true
  (h_pre : pre s0)
  (h_pc : r StateField.PC si = 0x4005b4#64)
  (h_cond_holds_true : r (StateField.FLAG PFlag.Z) si = 0#1)
  (h_inv : loop_inv s0 si)
  (h_run : sf = (Correctness.nextc (Sys.run si 1))) :
  r (StateField.GPR 0#5) sf = r (StateField.GPR 0x0#5) si - 0x1#64 ∧
  r (StateField.GPR 1#5) sf =
      (AddWithCarry (r (StateField.GPR 0x1#5) s0 +
                    (r (StateField.GPR 0x0#5) s0 -
                    r (StateField.GPR 0x0#5) si))
                    0x1#64
                    0x0#1).fst ∧
  r (StateField.FLAG PFlag.Z) sf =
    (AddWithCarry (r (StateField.GPR 0x0#5) si - 0x1#64)
                  0xffffffffffffffff#64 0x1#1).snd.z ∧
  r StateField.PC sf = 0x4005b4#64 ∧
  r StateField.ERR sf = .None ∧
  sf.program = program ∧
  CheckSPAlignment sf := by
  -- Prelude
  rw [nextc_to_run_from_0x4005b4_cond_holds_true
       h_pre h_pc h_cond_holds_true h_inv] at h_run
  simp only [state_simp_rules, loop_inv] at h_inv
  obtain ⟨_h_inv_x0_le, h_inv_z, h_inv_x1, h_inv_err,
          h_inv_program, h_inv_sp_aligned⟩ := h_inv
  simp (config := {decide := true}) only
    [h_cond_holds_true, minimal_theory] at h_inv_z
  -- Symbolic simulation
  -- (TODO) Better handling for branch instructions.
  init_next_step h_run h_step_1 s1
  replace h_step_1 := h_step_1.symm
  rw [program.stepi_eq_0x4005b4] at h_step_1
  simp only [*, bitvec_rules, minimal_theory] at h_step_1
  (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
   all_goals (try assumption))
  --
  sym_n 3 at s1
  -- Aggregating the effects
  simp (config := {ground := true}) only [*, AddWithCarry.sub_one_64,
    state_simp_rules, bitvec_rules, minimal_theory]
  done

theorem effects_of_nextc_from_0x4005b4_cond_holds_false
  (h_pre : pre s0)
  (h_pc : r StateField.PC si = 0x4005b4#64)
  (h_cond_holds_false : ¬ (r (StateField.FLAG PFlag.Z) si = 0#1))
  (h_inv : loop_inv s0 si)
  (h_run : sf = (Correctness.nextc (Sys.run si 1))) :
  r (StateField.GPR 0#5) sf = 0#64 ∧
  r (StateField.GPR 1#5) sf =
      r (StateField.GPR 0x1#5) s0 + r (StateField.GPR 0x0#5) s0 ∧
  r (StateField.FLAG PFlag.Z) sf = 1#1 ∧
  r StateField.PC sf = 0x4005b8#64 ∧
  r StateField.ERR sf = .None ∧
  sf.program = program ∧
  CheckSPAlignment sf := by
  -- Prelude
  rw [nextc_to_run_from_0x4005b4_cond_holds_false
       h_pre h_pc h_cond_holds_false h_inv] at h_run
  simp only [state_simp_rules, loop_inv] at h_inv
  obtain ⟨_h_inv_x0_le, h_inv_z, h_inv_x1, h_inv_err,
          h_inv_program, h_inv_sp_aligned⟩ := h_inv
  simp (config := {decide := true}) only
    [non_zero_one_bit_is_one, h_cond_holds_false, minimal_theory] at h_inv_z
  -- Symbolic simulation
  -- sym_n 1 at si
  -- (TODO) Better handling for branch instructions.
  init_next_step h_run h_step_1 s1
  rw [program.stepi_eq_0x4005b4] at h_step_1
  replace h_step_1 := h_step_1.symm
  simp only [*, non_zero_one_bit_is_one, bitvec_rules, minimal_theory]
    at h_step_1
  (intro_fetch_decode_lemmas h_step_1 h_inv_program "h_inv";
   all_goals (try assumption))
  -- Aggregating the effects
  simp only [run] at h_run
  simp only [*, non_zero_one_bit_is_one,
              state_simp_rules, bitvec_rules, minimal_theory]
  done

-------------------------------------------------------------------------------

theorem nextc_to_run_from_0x4005b8 (_h_pre : pre s0)
  (h_pc : r StateField.PC si = 0x4005b8#64)
  (h_assert : loop_post s0 si) :
  Correctness.nextc (Sys.run si 1) = run 1 si := by
  simp only [pre, loop_post, state_simp_rules] at *
  obtain ⟨_h_inv_x0, h_inv_err, h_inv_program, h_inv_sp_aligned⟩ := h_assert

  simp only
    [Correctness.nextc, Correctness.arm_run,
     Spec'.cut, minimal_theory]

  -- Stop when the *_cut theorem says (cut <state>) = true.
  rw [AddLoop.csteps_eq]
  have h_step_1 := program.stepi_eq_0x4005b8_cut si (run 1 si)
  simp_all only [minimal_theory, bitvec_rules]
  generalize _h_s1 : run 1 si = s1 at h_step_1

  simp only [run_opener_zero, h_step_1, minimal_theory]
  done

theorem effects_of_nextc_from_0x4005b8 (_h_pre : pre s0)
  (h_pc : r StateField.PC si = 0x4005b8#64)
  (h_assert : loop_post s0 si)
  (h_run : sf = Correctness.nextc (Sys.run si 1)) :
  r (StateField.GPR 0#5) sf = r (StateField.GPR 1#5) si ∧
  r StateField.PC sf = 0x4005bc#64 ∧
  r StateField.ERR sf = .None ∧
  sf.program = program ∧
  CheckSPAlignment sf := by
  -- Prelude
  rw [nextc_to_run_from_0x4005b8 _h_pre h_pc h_assert] at h_run
  -- TODO: Tactic to "explode" conjunctions?
  obtain ⟨_h_inv_x0, h_inv_err, h_inv_program, h_inv_sp_aligned⟩ := h_assert
  -- Symbolic simulation
  -- TODO: Why do we need `try assumption` here?
  sym_n 1 at si <;> try assumption
  done

-------------------------------------------------------------------------------

-- TODO: Upstream?
@[bitvec_rules]
theorem BitVec.le_refl (x : BitVec n) :
  x <= x := by
  exact BitVec.le_of_eq x x rfl

private theorem loop_inv_x0_le (x y : BitVec 64)
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

theorem partial_correctness :
  PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_verification_conditions
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
    simp_all only [Spec'.assert, Spec.exit, assert, exit,
                   minimal_theory, state_simp_rules]
    obtain ⟨h_pre, h_assert⟩ := h_assert
    split at h_assert
    · -- Next cutpoint from 0x4005a4#64 (first instruction)
      generalize h_sn : (Correctness.nextc (Sys.run si 1)) = sn
      subst h_assert
      simp_all only [bitvec_rules, minimal_theory]
      have h_effects := @effects_of_nextc_from_0x4005a4 si sn
      simp only [*, minimal_theory] at h_effects
      simp only [h_effects, loop_inv,
                 state_simp_rules, bitvec_rules, minimal_theory]
      done
    · -- Next cutpoint from 0x4005b4#64 (loop guard)
      generalize h_sn : (Correctness.nextc (Sys.run si 1)) = sn
      by_cases h_cond_holds : r (StateField.FLAG PFlag.Z) si = 0x0#1
      case pos =>
        have h_effects :=
          @effects_of_nextc_from_0x4005b4_cond_holds_true s0 si sn
        simp only [*, minimal_theory] at h_effects
        simp only [*, loop_inv,
                   state_simp_rules, bitvec_rules, minimal_theory]
        simp (config := {decide := true}) only
                  [loop_inv, h_cond_holds, non_zero_one_bit_is_one,
                   state_simp_rules, bitvec_rules, minimal_theory]
          at h_assert
        obtain ⟨h_assert_x0, h_assert_x0_nz, _h_assert_x1, _, _, _⟩ := h_assert
        apply And.intro
        · apply loop_inv_x0_le
                (r (StateField.GPR 0x0#5) si) (r (StateField.GPR 0x0#5) s0)
                h_assert_x0 h_assert_x0_nz
        · apply And.intro
          · apply AddWithCarry.all_ones_zero_flag_64
          · simp only [AddWithCarry.add_one_64]
            rw [crock_lemma]
      case neg =>
        have h_effects :=
          @effects_of_nextc_from_0x4005b4_cond_holds_false s0 si sn
        simp only [*, minimal_theory] at h_effects
        simp only [*, loop_post, spec,
                   minimal_theory, bitvec_rules, state_simp_rules]
        ac_rfl
        done
    · -- Next cutpoint from 0x4005b8#64 (first instruction after loop)
      generalize h_sn : (Correctness.nextc (Sys.run si 1)) = sn
      have h_effects := @effects_of_nextc_from_0x4005b8 s0 si sn
      simp only [*, minimal_theory] at h_effects
      simp only [h_effects, post,
                 state_simp_rules, bitvec_rules, minimal_theory]
      simp only [loop_post,
                  state_simp_rules, bitvec_rules, minimal_theory]
        at h_assert
      simp_all only
      done
    · -- Next cutpoint from 0x4005bc#64 (last instruction)
      -- No such cutpoint exists:
      contradiction
    · -- No further cutpoints exist.
      simp_all only
  done

theorem termination :
  Termination ArmState := by
  simp [Termination, Spec.pre, Spec.exit, exit,
        state_simp_rules, bitvec_rules, minimal_theory]
  intro s h_pre
  sorry

end AddLoop
