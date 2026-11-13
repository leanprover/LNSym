/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Correctness.VCGen
import Proofs.Experiments.AddLoop.AddLoop

/-!
# Experimental: `AddLoop.partial_correctness` with Lean's `vcgen`

The same theorem as `AddLoop.partial_correctness` (`Proofs/Experiments/AddLoop/AddLoop.lean`),
by the same cut-point method and with the same `pre`/`post`/`cut`/`assert`, but
with each cut-to-cut obligation proved by `vcgen` instead of the hand-written
per-instruction `_cut`, `nextc_to_run_*` and `effects_of_nextc_*` lemmas there.

1. `#genVCGenSpecs` turns AddLoop's step theorems into one `vcgen` spec per address.
2. `buildSeg` computes, from the program, the segment from each cut point to the
   next ones (`seg_entry`, `seg_guard`, `seg_after`); the loop guard's `b.ne`
   becomes an `ite_pc`, so `seg_guard` covers both the trip around the loop body
   and the loop exit.
3. Each `seg_*_spec` is a triple: from a state satisfying the cut point's
   assertion, the segment ends at a cut point satisfying its assertion.
4. `partial_correctness_vcgen` applies
   `Correctness.partial_correctness_from_verification_conditions`; its per-cut-point
   obligation (`v4`) is `ArmVCGen.nextc_of_triple` applied to the segment specs.
5. `correctness_vcgen` is total correctness (partial correctness and
   termination) by `Correctness.by_the_method`, with segment triples that also
   show a `rank` decrease (`ArmVCGen.by_the_method_v4_of_triple`).
-/

open Std.WP ArmVCGen
set_option experimental.vcgen true

namespace AddLoop

#genVCGenSpecs AddLoop.program

/-- `cmp x, #0` sets Z iff `x = 0` (restated from `AddLoop.lean`, where it is private). -/
theorem zero_flag_of_cmp_zero (x : BitVec 64) :
    ((AddWithCarry x 0xffffffffffffffff#64 0x1#1).snd.z = 1#1) ↔ (x = 0#64) := by
  simp only [AddWithCarry, bitvec_rules, state_simp_rules]
  repeat split
  · bv_decide
  · bv_decide

/-! Loop-body arithmetic, over plain bitvectors (cheap; `bv_omega` over the whole
VC context is not). -/
theorem x0_sub_one_le {x y : BitVec 64} (h : x ≤ y) (hnz : ¬x = 0#64) : x - 1#64 ≤ y := by
  bv_omega

theorem acc_step (a b c : BitVec 64) : a + (b - c) + 1#64 = a + (b - (c - 1#64)) := by
  bv_decide

/-- `cut` as a function of the PC alone. -/
def cutPC (pc : BitVec 64) : Bool :=
  pc = 0x4005a4#64 || pc = 0x4005b4#64 || pc = 0x4005b8#64 || pc = 0x4005bc#64

theorem cut_eq_cutPC (s : ArmState) : Spec'.cut s = cutPC (r StateField.PC s) := rfl

/-! ## Segments, computed from the program by `buildSeg` (stopping at cut points) -/

-- From the entry (`b` at 0x4005a4) through `cmp` (0x4005b0) to the loop guard.
#genVCGenSegment seg_entry := buildSeg AddLoop.program cutPC 100 0x4005a4#64
-- From the loop guard (`b.ne` at 0x4005b4): `ite_pc 0x4005a8` either goes around
-- the body (add, sub, cmp) back to the guard, or stops at 0x4005b8 after the loop.
#genVCGenSegment seg_guard := buildSeg AddLoop.program cutPC 100 0x4005b4#64
-- From the first instruction after the loop (`mov` at 0x4005b8) to the exit.
#genVCGenSegment seg_after := buildSeg AddLoop.program cutPC 100 0x4005b8#64

/-! ## One triple per segment -/

/-- Around the loop body back to the guard (preserving `loop_inv`), or out of the
loop (establishing `loop_post`). -/
theorem seg_guard_spec (s0 : ArmState) :
    ⦃ fun s => pre s0 ∧ loop_inv s0 s ∧ r StateField.PC s = 0x4005b4#64 ⦄
    seg_guard
    ⦃ fun _ s => cut s = true ∧ assert s0 s ⦄ := by
  unfold seg_guard
  vcgen
  -- Each VC: a step's side conditions (from the facts the previous step handed
  -- forward), or a postcondition at the end of one of the two paths.
  all_goals first
    | arm_vc_step
    | (simp only [assert, cut, loop_inv, loop_post, pre, read_pc, read_err, read_gpr] at *
       arm_vc_final)
  -- Left: invariant preservation around the body, and the loop exit.
  all_goals first
    | (simp only [spec]; ac_rfl)
    | (simp only [zero_flag_of_cmp_zero, iff_self, true_and]
       exact ⟨x0_sub_one_le (by simp_all) (by simp_all), acc_step _ _ _⟩)

/-- From the entry to the loop guard, establishing `loop_inv`. -/
theorem seg_entry_spec (s0 : ArmState) :
    ⦃ fun s => pre s0 ∧ s = s0 ⦄
    seg_entry
    ⦃ fun _ s => cut s = true ∧ assert s0 s ⦄ := by
  unfold seg_entry
  vcgen
  all_goals first
    | arm_vc_step
    | (obtain ⟨hpre, rfl⟩ := ‹pre s0 ∧ _ = s0›
       simp only [assert, cut, loop_inv, pre, read_pc, read_err, read_gpr] at *
       arm_vc_final)
  all_goals simp only [zero_flag_of_cmp_zero, BitVec.le_refl, BitVec.sub_self, BitVec.add_zero]

/-- From after the loop to the exit, establishing `post`. -/
theorem seg_after_spec (s0 : ArmState) :
    ⦃ fun s => pre s0 ∧ loop_post s0 s ∧ r StateField.PC s = 0x4005b8#64 ⦄
    seg_after
    ⦃ fun _ s => cut s = true ∧ assert s0 s ⦄ := by
  unfold seg_after
  vcgen
  all_goals first
    | arm_vc_step
    | (simp only [assert, cut, loop_post, post, pre, read_pc, read_err, read_gpr] at *
       arm_vc_final)

/-- `AddLoop.partial_correctness`, with each cut-to-cut obligation discharged by a
`vcgen` segment triple via `ArmVCGen.nextc_of_triple`. -/
theorem partial_correctness_vcgen : PartialCorrectness ArmState := by
  apply Correctness.partial_correctness_from_verification_conditions
  case v1 =>
    intro s0 h_pre
    simp_all only [Spec.pre, pre, Spec'.assert, assert, minimal_theory]
  case v2 =>
    intro sf h_exit
    simp_all only [Spec.exit, exit, Spec'.cut, cut, state_simp_rules, minimal_theory]
  case v3 =>
    intro s0 sf h_assert h_exit
    simp_all only [Spec'.assert, Spec.exit, assert, exit, Spec.post]
  case v4 =>
    intro s0 si h_assert h_exit
    simp only [Spec'.assert, assert] at h_assert
    simp only [Spec.exit, exit, read_pc] at h_exit
    obtain ⟨h_pre, h_assert⟩ := h_assert
    split at h_assert
    next h_pc =>
      exact ArmVCGen.nextc_of_triple cut_eq_cutPC (by simp [seg_entry, seg_guard, seg_after, ArmCmd.pcs, cutPC]) (seg_entry_spec s0) ⟨h_pre, h_assert⟩
    next h_pc =>
      exact ArmVCGen.nextc_of_triple cut_eq_cutPC (by simp [seg_entry, seg_guard, seg_after, ArmCmd.pcs, cutPC]) (seg_guard_spec s0)
        ⟨h_pre, h_assert, by simpa [read_pc] using h_pc⟩
    next h_pc =>
      exact ArmVCGen.nextc_of_triple cut_eq_cutPC (by simp [seg_entry, seg_guard, seg_after, ArmCmd.pcs, cutPC]) (seg_after_spec s0)
        ⟨h_pre, h_assert, by simpa [read_pc] using h_pc⟩
    next h_pc => simp_all [read_pc]
    next => contradiction

/-! ## Total correctness, with `Correctness.by_the_method`

Each segment triple additionally shows that `rank` decreases from one cut point to the next,
and `ArmVCGen.by_the_method_v4_of_triple` turns that into `by_the_method`'s
obligation, giving partial correctness and termination together. -/

/-- Decreases from each cut point to the next: around the loop by `x0` (which
the loop decrements), and by one on the way out. -/
def rank (s : ArmState) : Nat :=
  if r StateField.PC s = 0x4005a4#64 then (r (StateField.GPR 0#5) s).toNat + 3
  else if r StateField.PC s = 0x4005b4#64 then (r (StateField.GPR 0#5) s).toNat + 2
  else if r StateField.PC s = 0x4005b8#64 then 1
  else 0

theorem rank_step {x : BitVec 64} (h : ¬x = 0#64) : (x - 1#64).toNat + 2 < x.toNat + 2 := by
  bv_omega

theorem seg_entry_total (s0 si : ArmState) :
    ⦃ fun s => s = si ∧ (pre s0 ∧ s = s0) ⦄
    seg_entry
    ⦃ fun _ s => cut s = true ∧ assert s0 s ∧ rank s < rank si ⦄ := by
  unfold seg_entry
  vcgen
  all_goals first
    | arm_vc_step
    | (obtain ⟨rfl, hpre, rfl⟩ := ‹_ = si ∧ pre s0 ∧ _ = s0›
       simp only [assert, cut, loop_inv, pre, rank, read_pc, read_err, read_gpr] at *
       arm_vc_final)
  all_goals simp [zero_flag_of_cmp_zero]

theorem seg_guard_total (s0 si : ArmState) :
    ⦃ fun s => s = si ∧ (pre s0 ∧ loop_inv s0 s ∧ r StateField.PC s = 0x4005b4#64) ⦄
    seg_guard
    ⦃ fun _ s => cut s = true ∧ assert s0 s ∧ rank s < rank si ⦄ := by
  unfold seg_guard
  vcgen
  all_goals first
    | arm_vc_step
    | (obtain ⟨rfl, _⟩ := ‹_ = si ∧ _›
       simp only [assert, cut, loop_inv, loop_post, pre, rank, read_pc, read_err, read_gpr] at *
       arm_vc_final)
  all_goals first
    | (simp only [spec]; ac_rfl)
    | (simp only [zero_flag_of_cmp_zero, iff_self, true_and]
       exact ⟨⟨x0_sub_one_le (by simp_all) (by simp_all), acc_step _ _ _⟩, rank_step (by simp_all)⟩)
    | (simp only [spec]; exact ⟨by ac_rfl, by omega⟩)

theorem seg_after_total (s0 si : ArmState) :
    ⦃ fun s => s = si ∧ (pre s0 ∧ loop_post s0 s ∧ r StateField.PC s = 0x4005b8#64) ⦄
    seg_after
    ⦃ fun _ s => cut s = true ∧ assert s0 s ∧ rank s < rank si ⦄ := by
  unfold seg_after
  vcgen
  all_goals first
    | arm_vc_step
    | (obtain ⟨rfl, _⟩ := ‹_ = si ∧ _›
       simp only [assert, cut, loop_post, post, pre, rank, read_pc, read_err, read_gpr] at *
       arm_vc_final)

/-- Total correctness of AddLoop: `PartialCorrectness` and `Termination`. -/
theorem correctness_vcgen : Correctness ArmState := by
  apply Correctness.by_the_method rank
  case v1 =>
    intro s0 h_pre
    simp_all only [Spec.pre, pre, Spec'.assert, assert, minimal_theory]
  case v2 =>
    intro sf h_exit
    simp_all only [Spec.exit, exit, Spec'.cut, cut, state_simp_rules, minimal_theory]
  case v3 =>
    intro s0 sf h_assert h_exit
    simp_all only [Spec'.assert, Spec.exit, assert, exit, Spec.post]
  case v4 =>
    intro s0 si h_assert h_exit
    simp only [Spec'.assert, assert] at h_assert
    simp only [Spec.exit, exit, read_pc] at h_exit
    obtain ⟨h_pre, h_assert⟩ := h_assert
    split at h_assert
    next h_pc =>
      exact ArmVCGen.by_the_method_v4_of_triple cut_eq_cutPC (by simp [seg_entry, seg_guard, seg_after, ArmCmd.pcs, cutPC]) rank
        (seg_entry_total s0 si) ⟨h_pre, h_assert⟩
    next h_pc =>
      exact ArmVCGen.by_the_method_v4_of_triple cut_eq_cutPC (by simp [seg_entry, seg_guard, seg_after, ArmCmd.pcs, cutPC]) rank
        (seg_guard_total s0 si) ⟨h_pre, h_assert, by simpa [read_pc] using h_pc⟩
    next h_pc =>
      exact ArmVCGen.by_the_method_v4_of_triple cut_eq_cutPC (by simp [seg_entry, seg_guard, seg_after, ArmCmd.pcs, cutPC]) rank
        (seg_after_total s0 si) ⟨h_pre, h_assert, by simpa [read_pc] using h_pc⟩
    next h_pc => exact absurd (by simpa [read_pc] using h_pc) h_exit
    next => contradiction

end AddLoop
