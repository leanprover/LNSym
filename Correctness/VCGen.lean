/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tactics.VCGen
import Correctness.ArmSpec

/-!
# `vcgen` segments for LNSym's cut-point method

From a `vcgen` triple about the segment from a cut point to the next ones
(possibly branching), `nextc_of_triple` discharges the per-cut-point obligation
of `Correctness.partial_correctness_from_verification_conditions`, and
`by_the_method_v4_of_triple` that of `Correctness.by_the_method`.

(Kept separate from `Tactics.VCGen` because `Correctness.ArmSpec` changes how
bitvector literals are printed.)
-/

open Std.WP Lean.Order

namespace ArmVCGen

open Correctness in
/-- If no state before step `k` is a cut point and the state after `k` steps is,
then `nextc s` is the state after `k` steps. -/
theorem nextc_eq_of_first_cut [Spec' ArmState] {s : ArmState} {k : Nat}
    (hnot : ∀ j < k, Spec'.cut (Sys.run s j) = false) (hk : Spec'.cut (Sys.run s k) = true) :
    nextc s = Sys.run s k := by
  have key : ∀ m ≤ k, csteps (Sys.run s (k - m)) (k - m) = k := by
    intro m
    induction m with
    | zero => intro _; simpa using csteps_cut hk (k - 0)
    | succ m ih =>
      intro hm
      have hlt : k - (m + 1) < k := by omega
      apply csteps_not_cut (by simp [hnot _ hlt])
      rw [_root_.next_run, show k - (m + 1) + 1 = k - m by omega]
      exact ih (by omega)
  have h0 := key k (Nat.le_refl k)
  simp only [Nat.sub_self] at h0
  simp only [nextc, Sys.run] at h0 ⊢
  simp [h0, hk]

open Correctness in
/-- Bridge to LNSym's cut-point method: if the command `seq (stepAt pc) c`
establishes `P` together with "is a cut point", and no address of `c` is a cut
point (for a `cut` that depends only on the PC), then `P` holds at the next cut
point `nextc (Sys.run si 1)`. This is the obligation that
`Correctness.partial_correctness_from_verification_conditions` asks for. -/
theorem nextc_of_triple [Spec' ArmState] {cutPC : BitVec 64 → Bool}
    (hcut : ∀ s : ArmState, Spec'.cut s = cutPC (r StateField.PC s))
    {pc : BitVec 64} {c : ArmCmd} (hc : ∀ q ∈ c.pcs, cutPC q = false)
    {P pre : ArmState → Prop}
    {inst : BitVec 32}
    (h : Triple (ArmCmd.seq (ArmCmd.stepAt pc inst) c) pre
            (fun _ s => Spec'.cut s = true ∧ P s) epost)
    {si : ArmState} (hsi : pre si) :
    P (nextc (Sys.run si 1)) := by
  have hwp := Triple.le_wp h si hsi
  simp only [wp_seq_eq, wp_stepAt_eq] at hwp
  obtain ⟨_, hrest⟩ := hwp
  obtain ⟨n, ⟨hcutn, hP⟩, hpcs⟩ := wpCmd_run c _ (stepi si) hrest
  have hrun1 : Sys.run si 1 = stepi si := by simp [Sys.run, Sys.next]
  rw [hrun1]
  have heq : nextc (stepi si) = Sys.run (stepi si) n := by
    apply nextc_eq_of_first_cut
    · intro j hj
      rw [hcut, arm_run]
      exact hc _ (hpcs j hj)
    · rw [arm_run]; exact hcutn
  rw [heq, arm_run]; exact hP

open Correctness in
/-- `cassert` at the first cut point: if no state before step `k` is a cut point
and the state after `k` steps is, `cassert` checks `assert` there. -/
theorem snd_cassert_of_first_cut [Spec' ArmState] {s0 s : ArmState} {k : Nat}
    (hnot : ∀ j < k, Spec'.cut (Sys.run s j) = false) (hk : Spec'.cut (Sys.run s k) = true)
    (i : Nat) : (cassert s0 s i).snd = Spec'.assert s0 (Sys.run s k) := by
  induction k generalizing s i with
  | zero => exact snd_cassert_of_cut hk i
  | succ k ih =>
    rw [snd_cassert_of_not_cut (by simpa [Sys.run] using hnot 0 (by omega))]
    apply ih
    · intro j hj; simpa [_root_.run_succ] using hnot (j + 1) (by omega)
    · simpa [_root_.run_succ] using hk

open Correctness in
/-- Bridge to `Correctness.by_the_method` (total correctness): its per-cut-point
obligation `v4` follows from a `vcgen` triple about the segment from the cut
point `si` that establishes, at the next cut point, `assert s0` and a smaller
`rank`. As for `nextc_of_triple`, `cut` must depend only on the PC and no
interior address of the segment may be a cut point. -/
theorem by_the_method_v4_of_triple [Spec' ArmState] {cutPC : BitVec 64 → Bool}
    (hcut : ∀ s : ArmState, Spec'.cut s = cutPC (r StateField.PC s))
    {pc : BitVec 64} {inst : BitVec 32} {c : ArmCmd} (hc : ∀ q ∈ c.pcs, cutPC q = false)
    {s0 si : ArmState} {pre : ArmState → Prop} (rank : ArmState → Nat)
    (h : Triple (ArmCmd.seq (ArmCmd.stepAt pc inst) c) (fun s => s = si ∧ pre s)
            (fun _ s => Spec'.cut s = true ∧ Spec'.assert s0 s ∧ rank s < rank si) epost)
    (hsi : pre si) :
    (cassert s0 (Sys.run si 1) 0).snd ∧
      ∃ n, Spec'.cut (Sys.run si n) ∧ rank (Sys.run si n) < rank si := by
  have hwp := Triple.le_wp h si ⟨rfl, hsi⟩
  simp only [wp_seq_eq, wp_stepAt_eq] at hwp
  obtain ⟨_, hrest⟩ := hwp
  obtain ⟨n, ⟨hcutn, hassert, hrank⟩, hpcs⟩ := wpCmd_run c _ (stepi si) hrest
  have hrun1 : Sys.run si 1 = stepi si := by simp [Sys.run, Sys.next]
  have hnot : ∀ j < n, Spec'.cut (Sys.run (stepi si) j) = false := by
    intro j hj; rw [hcut, arm_run]; exact hc _ (hpcs j hj)
  have hk : Spec'.cut (Sys.run (stepi si) n) = true := by rw [arm_run]; exact hcutn
  refine ⟨?_, n + 1, ?_⟩
  · rw [hrun1, snd_cassert_of_first_cut hnot hk, arm_run]; exact hassert
  · have : Sys.run si (n + 1) = run n (stepi si) := by
      rw [_root_.run_succ, arm_run]; simp [Sys.next]
    rw [this]; exact ⟨hcutn, hrank⟩

end ArmVCGen
