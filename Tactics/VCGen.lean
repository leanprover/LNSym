/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec
import Std.Tactic.Do
import Std.WP
import Std.WP.Triple.SpecLemmas

/-!
# Experimental: Lean's `vcgen` over LNSym's operational semantics

Lean's `vcgen` generates verification conditions for any program type with a
`Std.WP.WP` interpretation. This file gives Arm machine code such a program type
without changing the ISA model: `ArmCmd` describes control flow only, and its
weakest precondition is defined by LNSym's `stepi`.

## The program type

- `ArmCmd.stepAt pc inst`: execute one instruction, which must be at `pc`.
  `inst` is the expected instruction word; it is ghost data (`wpCmd` ignores it).
- `ArmCmd.seq c₁ c₂`, `ArmCmd.skip`.
- `ArmCmd.ite_pc pc c₁ c₂`: continue with `c₁` if the PC is `pc`, else `c₂`
  (after a conditional branch).

`buildSeg prog stop fuel pc` builds the command for the paths from `pc` through
`prog`'s control flow (falling through, following `B`/`BL`, splitting
conditional branches, stopping after `RET` or before a `stop` address);
`#genVCGenSegment name := buildSeg …` evaluates it once and defines `name` as the
literal command. `trace` turns a list of (address, instruction) pairs into a
straight-line command.

## Specs

`#genVCGenSpecs prog` (or `set_option genStepEqTheorems.vcgenSpecs true` before
`#genStepEqTheorems prog`) adds one `@[spec]` per instruction address, derived
from the step theorems that `#genStepEqTheorems` generates. They are *SSA-style*:
they name the next state (`Next f s s'`) instead of substituting it, and hand
the next step its side conditions (`Side`: program, PC, no error, SP
alignment; `SideBr` after a conditional branch; `SideAny` when the successor is
unknown). These facts are proved once per instruction when the spec is
generated, so each step's side condition is a hypothesis in its VC, and the work
per VC stays constant as programs grow. (Consequence: preconditions must assume
`CheckSPAlignment`.)

## Tactics

`arm_vc_step` closes a step's side conditions; `arm_vc_final` handles the
postcondition at the end of a path (expanding the `Next` chain once);
`arm_vc_final_with [lemmas]` does so with extra `simp` lemmas; `arm_vc` tries
`arm_vc_step` and `arm_vc_final`. `arm_pcs [lemmas]` proves that no address of a
command satisfies a predicate (e.g. is a cut point).

## Composing

`triple_seq`, `triple_pre` and `triple_reassoc` compose and adapt segment
triples, so that a long program is verified one segment at a time.

## Bridges

`run_of_triple` turns a triple about a branch-free command into LNSym's usual
`run n s` form. `Correctness/VCGen.lean` connects triples about segments
between cut points to the cut-point method: partial correctness
(`Correctness.partial_correctness_from_verification_conditions`) and total
correctness (`Correctness.by_the_method`).

See `Proofs/Experiments/VCGen/` for Popcount32, AddLoop and SHA512.
-/

open Std.WP Lean.Order

set_option experimental.vcgen true

namespace ArmVCGen

inductive ArmCmd where
  | skip
  /-- Execute one instruction, which must be at address `pc`. `inst` records the
  instruction word expected there: it is *not* part of the semantics (`wpCmd`
  ignores it), so a spec that relies on it must itself require
  `fetch_inst pc s = some inst`. It makes a command a readable control-flow
  graph; the generated specs are keyed on the address. -/
  | stepAt (pc : BitVec 64) (inst : BitVec 32)
  | seq (c₁ c₂ : ArmCmd)
  /-- Continue with `c₁` if the current PC is `pc`, and with `c₂` otherwise; e.g.,
  after a conditional branch, dispatch on where it went. -/
  | ite_pc (pc : BitVec 64) (c₁ c₂ : ArmCmd)

/-- Weakest precondition, by the operational semantics `stepi`. -/
def wpCmd : ArmCmd → (ArmState → Prop) → ArmState → Prop
  | .skip, Q, s => Q s
  | .stepAt pc _, Q, s => r StateField.PC s = pc ∧ Q (stepi s)
  | .seq c₁ c₂, Q, s => wpCmd c₁ (wpCmd c₂ Q) s
  | .ite_pc pc c₁ c₂, Q, s => if r StateField.PC s = pc then wpCmd c₁ Q s else wpCmd c₂ Q s

theorem wpCmd_mono {c : ArmCmd} {Q Q' : ArmState → Prop} (hQ : ∀ s, Q s → Q' s) :
    ∀ s, wpCmd c Q s → wpCmd c Q' s := by
  induction c generalizing Q Q' with
  | skip => exact hQ
  | stepAt pc _ => intro s ⟨hpc, h⟩; exact ⟨hpc, hQ _ h⟩
  | seq c₁ c₂ ih₁ ih₂ => intro s h; exact ih₁ (fun s' => ih₂ hQ s') s h
  | ite_pc pc c₁ c₂ ih₁ ih₂ =>
    intro s h; simp only [wpCmd] at h ⊢; split
    · exact ih₁ hQ s (by simp_all)
    · exact ih₂ hQ s (by simp_all)

abbrev Assn := ArmState → Prop

instance : WP ArmCmd Unit Assn EStack⟨⟩ where
  wpTrans c := ⟨fun Q _epost s => wpCmd c (Q ()) s⟩
  wp_trans_monotone c := by
    intro Q Q' _ _ _ hQ s h
    exact wpCmd_mono (fun s' h' => hQ () s' h') s h

variable {Q : Unit → Assn} {epost : EStack⟨⟩}

private theorem wp_apply (c : ArmCmd) :
    Std.WP.wp c Q epost = fun s => wpCmd c (Q ()) s := rfl

@[simp] theorem wp_skip_eq (s : ArmState) :
    Std.WP.wp ArmCmd.skip Q epost s = Q () s := by simp only [wp_apply, wpCmd]

@[simp] theorem wp_stepAt_eq (pc : BitVec 64) (inst : BitVec 32) (s : ArmState) :
    Std.WP.wp (ArmCmd.stepAt pc inst) Q epost s = (r StateField.PC s = pc ∧ Q () (stepi s)) := by
  simp only [wp_apply, wpCmd]

@[simp] theorem wp_seq_eq (c₁ c₂ : ArmCmd) (s : ArmState) :
    Std.WP.wp (ArmCmd.seq c₁ c₂) Q epost s =
      Std.WP.wp c₁ (fun _ => Std.WP.wp c₂ Q epost) epost s := by
  simp only [wp_apply, wpCmd]

private theorem triple_of_wp {c : ArmCmd} {pre : Assn}
    (h : ∀ s, Std.WP.wp c Q epost s = pre s) : Triple c pre Q epost :=
  Triple.iff.mpr (by rw [funext h]; exact PartialOrder.rel_refl)

@[spec] theorem spec_skip : Triple ArmCmd.skip (Q ()) Q epost := triple_of_wp wp_skip_eq

@[spec] theorem spec_seq (c₁ c₂ : ArmCmd) :
    Triple (ArmCmd.seq c₁ c₂) (Std.WP.wp c₁ (fun _ => Std.WP.wp c₂ Q epost) epost) Q epost :=
  triple_of_wp (wp_seq_eq c₁ c₂)

@[simp] theorem wp_ite_pc_eq (pc : BitVec 64) (c₁ c₂ : ArmCmd) (s : ArmState) :
    Std.WP.wp (ArmCmd.ite_pc pc c₁ c₂) Q epost s =
      if r StateField.PC s = pc then Std.WP.wp c₁ Q epost s else Std.WP.wp c₂ Q epost s := by
  simp only [wp_apply, wpCmd]

/-- The precondition is stated with lattice connectives (`⇨`, `⊓`) rather than
`if`, so that `vcgen` explores both continuations, each under its branch
condition, instead of leaving the `if` as a verification condition. -/
@[spec] theorem spec_ite_pc (pc : BitVec 64) (c₁ c₂ : ArmCmd) :
    Triple (ArmCmd.ite_pc pc c₁ c₂)
      (((fun s => r StateField.PC s = pc) ⇨ Std.WP.wp c₁ Q epost) ⊓
       ((fun s => r StateField.PC s ≠ pc) ⇨ Std.WP.wp c₂ Q epost)) Q epost :=
  Triple.iff.mpr (by
    intro s hs
    simp only [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and, Lean.Order.himp_apply,
      Lean.Order.himp_prop_eq_imp] at hs
    obtain ⟨h₁, h₂⟩ := hs
    simp only [wp_ite_pc_eq]
    split
    · exact h₁ ‹_›
    · exact h₂ ‹_›)

/-- Turn a step theorem from `#genStepEqTheorems`, i.e.
`stepi s = f s` whenever `s` runs `prog`, is at `pc`, and has no error,
into a `vcgen` specification for `stepAt pc inst` (for any `inst`: the step
theorem already pins down the instruction via `s.program = prog`). -/
theorem stepAt_spec_of_stepi_eq {prog : Program} {pc : BitVec 64} {f : ArmState → ArmState}
    (h : ∀ {s : ArmState}, s.program = prog → r StateField.PC s = pc →
      r StateField.ERR s = StateError.None → stepi s = f s) (inst : BitVec 32) :
    Triple (ArmCmd.stepAt pc inst)
      ((fun s => s.program = prog ∧ r StateField.PC s = pc ∧
        r StateField.ERR s = StateError.None) ⊓ (fun s => Q () (f s))) Q epost :=
  -- The precondition is a lattice meet (not `∧`), so that `vcgen` splits off the
  -- side conditions as VCs and keeps generating through `Q () (f s)`.
  Triple.iff.mpr (by
    intro s hs
    simp only [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and] at hs
    obtain ⟨⟨hprog, hpc, herr⟩, hq⟩ := hs
    simp only [wp_stepAt_eq]
    exact ⟨hpc, by rw [h hprog hpc herr]; exact hq⟩)

/-! ## SSA-style step specs

For long programs, the specs that `vcgen` uses name the next state instead of
substituting it, and hand the next step its side conditions:

  `Side prog pc s ⊓ (fun s => ∀ s', Next f s s' → Side prog npc s' → Q () s')`

so the side conditions of every step are hypotheses (closed by `assumption`),
and verification conditions mention short state variables rather than nested
chains of writes. Only the final postcondition needs the chain, once
(`arm_vc_final`). The facts handed forward are proved once per instruction, when
the spec is generated.
-/

/-- The side conditions under which a step theorem applies, plus stack alignment
(which most instructions that access memory through SP check). -/
def Side (prog : Program) (pc : BitVec 64) (s : ArmState) : Prop :=
  s.program = prog ∧ r StateField.PC s = pc ∧ r StateField.ERR s = StateError.None ∧
  CheckSPAlignment s

/-- `Side` after a conditional branch: the PC is the target `t` or the
fall-through `nt`. -/
def SideBr (prog : Program) (t nt : BitVec 64) (s : ArmState) : Prop :=
  s.program = prog ∧ (r StateField.PC s = t ∨ r StateField.PC s = nt) ∧
  r StateField.ERR s = StateError.None ∧ CheckSPAlignment s

/-- What is known after an instruction whose successor is not known statically
(e.g. `RET`): everything in `Side` but the PC. -/
def SideAny (prog : Program) (s : ArmState) : Prop :=
  s.program = prog ∧ r StateField.ERR s = StateError.None ∧ CheckSPAlignment s

theorem Side.err {prog : Program} {pc : BitVec 64} {s : ArmState} (h : Side prog pc s) :
    r StateField.ERR s = StateError.None := h.2.2.1
theorem SideBr.err {prog : Program} {t nt : BitVec 64} {s : ArmState} (h : SideBr prog t nt s) :
    r StateField.ERR s = StateError.None := h.2.2.1
theorem SideAny.err {prog : Program} {s : ArmState} (h : SideAny prog s) :
    r StateField.ERR s = StateError.None := h.2.1

/-- The side conditions of a plain (non-SSA) spec, from `Side`. -/
theorem Side.plain {prog : Program} {pc : BitVec 64} {s : ArmState} (h : Side prog pc s) :
    s.program = prog ∧ r StateField.PC s = pc ∧ r StateField.ERR s = StateError.None :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem Side.of_br {prog : Program} {t nt : BitVec 64} {s : ArmState}
    (h : SideBr prog t nt s) (hpc : r StateField.PC s = t) : Side prog t s :=
  ⟨h.1, hpc, h.2.2⟩

theorem Side.of_br_ne {prog : Program} {t nt : BitVec 64} {s : ArmState}
    (h : SideBr prog t nt s) (hpc : r StateField.PC s ≠ t) : Side prog nt s :=
  ⟨h.1, h.2.1.resolve_left hpc, h.2.2⟩

/-- `s'` is the state after a step with effect `f` from `s`. Irreducible, so
that `simp`/`simp_all` do not substitute it (see `arm_vc_final`). -/
@[irreducible] def Next (f : ArmState → ArmState) (s s' : ArmState) : Prop := s' = f s

theorem Next.eq {f : ArmState → ArmState} {s s' : ArmState} (h : Next f s s') : s' = f s := by
  unfold Next at h; exact h

private theorem Next.self (f : ArmState → ArmState) (s : ArmState) : Next f s (f s) := by
  unfold Next; rfl

/-- SSA spec from a step theorem `h`, for an instruction that continues at `npc`:
`hside` (proved once, when the spec is generated) hands the next step its side
conditions. -/
theorem stepAt_ssa_spec {prog : Program} {pc npc : BitVec 64} {f : ArmState → ArmState}
    (h : ∀ {s : ArmState}, s.program = prog → r StateField.PC s = pc →
      r StateField.ERR s = StateError.None → stepi s = f s)
    (hside : ∀ s, Side prog pc s → Side prog npc (f s)) (inst : BitVec 32) :
    Triple (ArmCmd.stepAt pc inst)
      ((fun s => Side prog pc s) ⊓
       (fun s => ∀ s', Next f s s' → Side prog npc s' → Q () s')) Q epost :=
  Triple.iff.mpr (by
    intro s hs
    simp only [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and] at hs
    obtain ⟨hsd, hq⟩ := hs
    obtain ⟨hprog, hpc, herr, _⟩ := hsd
    simp only [wp_stepAt_eq]
    refine ⟨hpc, ?_⟩
    rw [h hprog hpc herr]
    exact hq _ (Next.self f s) (hside s ⟨hprog, hpc, herr, ‹_›⟩))

/-- SSA spec for an instruction whose successor is not known statically. -/
theorem stepAt_ssa_any_spec {prog : Program} {pc : BitVec 64} {f : ArmState → ArmState}
    (h : ∀ {s : ArmState}, s.program = prog → r StateField.PC s = pc →
      r StateField.ERR s = StateError.None → stepi s = f s)
    (hside : ∀ s, Side prog pc s → SideAny prog (f s)) (inst : BitVec 32) :
    Triple (ArmCmd.stepAt pc inst)
      ((fun s => Side prog pc s) ⊓
       (fun s => ∀ s', Next f s s' → SideAny prog s' → Q () s')) Q epost :=
  Triple.iff.mpr (by
    intro s hs
    simp only [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and] at hs
    obtain ⟨hsd, hq⟩ := hs
    obtain ⟨hprog, hpc, herr, _⟩ := hsd
    simp only [wp_stepAt_eq]
    refine ⟨hpc, ?_⟩
    rw [h hprog hpc herr]
    exact hq _ (Next.self f s) (hside s ⟨hprog, hpc, herr, ‹_›⟩))

/-- SSA spec for a conditional branch to `t`, falling through to `nt`. -/
theorem stepAt_ssa_br_spec {prog : Program} {pc t nt : BitVec 64} {f : ArmState → ArmState}
    (h : ∀ {s : ArmState}, s.program = prog → r StateField.PC s = pc →
      r StateField.ERR s = StateError.None → stepi s = f s)
    (hside : ∀ s, Side prog pc s → SideBr prog t nt (f s)) (inst : BitVec 32) :
    Triple (ArmCmd.stepAt pc inst)
      ((fun s => Side prog pc s) ⊓
       (fun s => ∀ s', Next f s s' → SideBr prog t nt s' → Q () s')) Q epost :=
  Triple.iff.mpr (by
    intro s hs
    simp only [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and] at hs
    obtain ⟨hsd, hq⟩ := hs
    obtain ⟨hprog, hpc, herr, _⟩ := hsd
    simp only [wp_stepAt_eq]
    refine ⟨hpc, ?_⟩
    rw [h hprog hpc herr]
    exact hq _ (Next.self f s) (hside s ⟨hprog, hpc, herr, ‹_›⟩))

/-- The straight-line trace through the given `(address, instruction)` pairs. -/
def trace : List (BitVec 64 × BitVec 32) → ArmCmd
  | [] => .skip
  | (pc, inst) :: rest => .seq (.stepAt pc inst) (trace rest)

/-- The number of instructions a branch-free command executes, or `none` if it
contains an `ite_pc`. -/
def ArmCmd.steps? : ArmCmd → Option Nat
  | .skip => some 0
  | .stepAt _ _ => some 1
  | .seq c₁ c₂ => do return (← c₁.steps?) + (← c₂.steps?)
  | .ite_pc .. => none

/-- Bridge to LNSym's `run` for branch-free commands: if `c` executes `n`
instructions and establishes `Q` from `s`, then `Q` holds of `run n s`. -/
theorem wp_run_of_steps (c : ArmCmd) {n : Nat} (hn : c.steps? = some n)
    (Q : ArmState → Prop) (s : ArmState) :
    Std.WP.wp c (fun _ => Q) epost s → Q (run n s) := by
  show wpCmd c Q s → _
  induction c generalizing n Q s with
  | skip => simp only [ArmCmd.steps?, Option.some.injEq] at hn; subst hn; exact id
  | stepAt pc _ =>
    simp only [ArmCmd.steps?, Option.some.injEq] at hn; subst hn
    exact fun ⟨_, h⟩ => by simpa [run] using h
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [ArmCmd.steps?, Option.bind_eq_bind] at hn
    cases h₁ : c₁.steps? <;> cases h₂ : c₂.steps? <;> simp_all
    rename_i n₁ n₂
    subst hn
    intro h
    rw [run_plus]
    exact ih₂ Q _ (ih₁ _ s h)
  | ite_pc => simp [ArmCmd.steps?] at hn

/-- `Triple` form of `wp_run_of_steps`. -/
theorem run_of_triple {c : ArmCmd} {n : Nat} (hn : c.steps? = some n) {P Q : ArmState → Prop}
    (h : Triple c P (fun _ => Q) epost) {s : ArmState} (hs : P s) :
    Q (run n s) :=
  wp_run_of_steps c hn Q s (Triple.le_wp h s hs)

/-! ## Composing triples

`vcgen` proves one triple per segment; these compose them, so that each segment's
verification conditions see only its own instructions. -/

theorem triple_seq {c₁ c₂ : ArmCmd} {P R : Assn} {Q : Unit → Assn} {e : EStack⟨⟩}
    (h₁ : Triple c₁ P (fun _ => R) e) (h₂ : Triple c₂ R Q e) :
    Triple (ArmCmd.seq c₁ c₂) P Q e :=
  Triple.iff.mpr (by
    intro s hs
    rw [wp_seq_eq]
    exact (show wpCmd c₁ R s → wpCmd c₁ (fun s' => wpCmd c₂ (Q ()) s') s from
      wpCmd_mono (fun s' hR => Triple.le_wp h₂ s' hR) s) (Triple.le_wp h₁ s hs))

theorem triple_pre {c : ArmCmd} {P P' : Assn} {Q : Unit → Assn} {e : EStack⟨⟩}
    (h : Triple c P Q e) (hP : ∀ s, P' s → P s) : Triple c P' Q e :=
  Triple.iff.mpr (fun s hs => Triple.le_wp h s (hP s hs))

theorem triple_reassoc {a b c : ArmCmd} {P : Assn} {Q : Unit → Assn} {e : EStack⟨⟩}
    (h : Triple (ArmCmd.seq (ArmCmd.seq a b) c) P Q e) : Triple (ArmCmd.seq a (ArmCmd.seq b c)) P Q e :=
  Triple.iff.mpr (fun s hs => Triple.le_wp h s hs)

/-- The instruction addresses of the `stepAt`s in a command. -/
def ArmCmd.pcs : ArmCmd → List (BitVec 64)
  | .skip => []
  | .stepAt pc _ => [pc]
  | .seq c₁ c₂ => c₁.pcs ++ c₂.pcs
  | .ite_pc _ c₁ c₂ => c₁.pcs ++ c₂.pcs

theorem ArmCmd.forall_pcs_seq {p : BitVec 64 → Prop} {a b : ArmCmd} (ha : ∀ q ∈ a.pcs, p q)
    (hb : ∀ q ∈ b.pcs, p q) : ∀ q ∈ (ArmCmd.seq a b).pcs, p q := by
  intro q hq
  simp only [ArmCmd.pcs, List.mem_append] at hq
  exact hq.elim (ha q) (hb q)

theorem ArmCmd.forall_pcs_ite_pc {p : BitVec 64 → Prop} {pc : BitVec 64} {a b : ArmCmd}
    (ha : ∀ q ∈ a.pcs, p q) (hb : ∀ q ∈ b.pcs, p q) : ∀ q ∈ (ArmCmd.ite_pc pc a b).pcs, p q := by
  intro q hq
  simp only [ArmCmd.pcs, List.mem_append] at hq
  exact hq.elim (ha q) (hb q)

/-- Prove `∀ q ∈ c.pcs, p q` one instruction at a time (for long commands, where
`decide` or a single `simp` exceed the recursion limit); `simp` with the given
lemmas closes each instruction's goal. -/
syntax "arm_pcs " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| arm_pcs [$ls,*]) => `(tactic|
      repeat' (first
        | apply ArmVCGen.ArmCmd.forall_pcs_seq
        | apply ArmVCGen.ArmCmd.forall_pcs_ite_pc
        | simp [ArmVCGen.ArmCmd.pcs, $ls,*]))

/-- If `wpCmd c Q s`, then `Q` holds after some number `n` of steps, and the
state before each of those steps is at one of `c.pcs`. -/
theorem wpCmd_run (c : ArmCmd) (Q : ArmState → Prop) (s : ArmState) (h : wpCmd c Q s) :
    ∃ n, Q (run n s) ∧ ∀ j < n, r StateField.PC (run j s) ∈ c.pcs := by
  induction c generalizing Q s with
  | skip => exact ⟨0, h, by simp⟩
  | stepAt pc _ =>
    obtain ⟨hpc, hq⟩ := h
    refine ⟨1, by simpa [run] using hq, ?_⟩
    intro j hj; obtain rfl : j = 0 := by omega
    simp [run, ArmCmd.pcs, hpc]
  | seq c₁ c₂ ih₁ ih₂ =>
    obtain ⟨n₁, h₁, hpc₁⟩ := ih₁ _ s h
    obtain ⟨n₂, h₂, hpc₂⟩ := ih₂ _ _ h₁
    refine ⟨n₁ + n₂, by rwa [run_plus], ?_⟩
    intro j hj
    simp only [ArmCmd.pcs, List.mem_append]
    by_cases hj₁ : j < n₁
    · exact .inl (hpc₁ j hj₁)
    · have := hpc₂ (j - n₁) (by omega)
      rw [← run_plus, Nat.add_sub_cancel' (by omega)] at this
      exact .inr this
  | ite_pc pc c₁ c₂ ih₁ ih₂ =>
    simp only [wpCmd] at h
    split at h
    · obtain ⟨n, hq, hpcs⟩ := ih₁ Q s h
      exact ⟨n, hq, fun j hj => by simp only [ArmCmd.pcs, List.mem_append]; exact .inl (hpcs j hj)⟩
    · obtain ⟨n, hq, hpcs⟩ := ih₂ Q s h
      exact ⟨n, hq, fun j hj => by simp only [ArmCmd.pcs, List.mem_append]; exact .inr (hpcs j hj)⟩

/-! ## Building commands from a program's control flow -/

/-- Build the command for the path(s) from address `pc` through `prog`:
fall through to `pc + 4`, follow `B` and `BL` (into the callee; a call does not
return to `pc + 4`), split conditional branches (`B.cond`, `CBZ`, `CBNZ`) with
`ite_pc` on the taken target, and stop after a branch to a register (`RET`,
`BR`, `BLR`), before an address `q` with `stop q`, or at an address not in
`prog`; a path that runs out of fuel or leaves `prog` just ends, so its
verification conditions are about the state where it ends.
The first instruction is always executed, even if `stop pc`, so a segment can
start at a cut point. `fuel` bounds the length of each path. -/
def buildSeg (prog : Program) (stop : BitVec 64 → Bool) : Nat → BitVec 64 → ArmCmd
  | 0, _ => .skip
  | fuel + 1, pc =>
    match prog.find? pc with
    | none => .skip
    | some inst =>
      let cont (q : BitVec 64) : ArmCmd := if stop q then .skip else buildSeg prog stop fuel q
      let rest : ArmCmd :=
        open ArmInst BranchInst in
        match decode_raw_inst inst with
        | some (BR (Uncond_branch_imm i)) => cont (BR.Uncond_branch_imm_inst.branch_taken_pc i pc)
        | some (BR (Cond_branch_imm i)) =>
          let t := BR.Cond_branch_imm_inst.branch_taken_pc i pc
          .ite_pc t (cont t) (cont (pc + 4#64))
        | some (BR (Compare_branch i)) =>
          let t := BR.Compare_branch_inst.branch_taken_pc i pc
          .ite_pc t (cont t) (cont (pc + 4#64))
        | some (BR (Uncond_branch_reg _)) => .skip
        | _ => cont (pc + 4#64)
      .seq (.stepAt pc inst) rest

open Lean in
/-- Quote a command as a literal term. -/
def ArmCmd.toExprImpl : ArmCmd → Expr
  | .skip => mkConst ``ArmCmd.skip
  | .stepAt pc inst => mkApp2 (mkConst ``ArmCmd.stepAt) (toExpr pc) (toExpr inst)
  | .seq c₁ c₂ => mkApp2 (mkConst ``ArmCmd.seq) c₁.toExprImpl c₂.toExprImpl
  | .ite_pc pc c₁ c₂ =>
    mkApp3 (mkConst ``ArmCmd.ite_pc) (toExpr pc) c₁.toExprImpl c₂.toExprImpl

open Lean in
instance : ToExpr ArmCmd where
  toExpr := ArmCmd.toExprImpl
  toTypeExpr := mkConst ``ArmCmd

open Lean Elab Command Term Meta in
/-- `#genVCGenSegment name := e` evaluates `e : ArmCmd` (typically a call to
`buildSeg`) once, at elaboration time, and defines `name` as the resulting
literal command, so that `vcgen` never has to unfold `buildSeg`. -/
elab "#genVCGenSegment " name:ident " := " e:term : command => do
  let declName := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    let ty := Lean.mkConst ``ArmCmd
    let ex ← elabTermEnsuringType e ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let ex ← instantiateMVars ex
    let cmd ← unsafe evalExpr ArmCmd ty ex
    addDecl <| .defnDecl {
      name := declName, levelParams := [], type := ty, value := toExpr cmd,
      hints := .abbrev, safety := .safe }
    -- Let `simp`/`unfold` derive equation lemmas for it.
    enableRealizationsForConst declName

open Lean Elab Term Meta in
/-- `arm_lit% e` evaluates the closed term `e : BitVec 64` at elaboration time and
elaborates to the resulting literal, e.g. `arm_lit% (entry + 0x40#64)` for an
address computed from a program's layout. Specs and `simp` then see a literal. -/
elab:max "arm_lit% " t:term:max : term => do
  let ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let e ← elabTermEnsuringType t ty
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr (BitVec 64) ty e
  return toExpr v

end ArmVCGen

initialize Lean.registerTraceClass `Tactic.vcgen_specs

register_option genStepEqTheorems.vcgenSpecs : Bool := {
  defValue := false
  descr := "(experimental) also generate a `vcgen` `@[spec]` for `ArmVCGen.ArmCmd.stepAt` \
    from each step theorem (see `Tactics/VCGen.lean`)"
}

namespace ArmVCGen
open Lean Elab Command Term Meta

/-- Tag `specName` `@[spec]`, scoped to the current namespace (so that specs of
different programs, which are keyed on addresses, do not meet unless both
namespaces are open); global if there is no current namespace. -/
def addSpecAttr (specName : Name) : TermElabM Unit := do
  let kind := if (← getCurrNamespace).isAnonymous then AttributeKind.global else .scoped
  Term.applyAttributes specName #[{ name := `spec, kind }]

/-- Add `specName : ∀ Q e, Triple (stepAt pc) (side ⊓ Q ∘ f) Q e`, derived from
the step theorem `stepThm` by `stepAt_spec_of_stepi_eq`, and tag it `@[spec]`. -/
def addVCGenSpec (stepThm specName : Name) : TermElabM Unit := do
  let (type, value) ← withLocalDeclD `Q (← mkArrow (mkConst ``Unit) (mkConst ``ArmVCGen.Assn)) fun q => do
    withLocalDeclD `e (← elabType (← `(EStack⟨⟩))) fun e => do
      let pf ← mkAppOptM ``stepAt_spec_of_stepi_eq #[q, e, none, none, none, mkConst stepThm]
      let ty ← instantiateMVars (← inferType pf)
      let val ← instantiateMVars pf
      return (← mkForallFVars #[q, e] ty, ← mkLambdaFVars #[q, e] val)
  addDecl <| .thmDecl { name := specName, levelParams := [], type, value }
  addSpecAttr specName

/-- Close `∀ s, Side prog pc s → Side prog npc (f s)` (or `SideBr …`, `SideAny …`) for one
step's effect `f`: a `simp` over a single layer of writes. -/
macro "arm_ssa_side" : tactic => `(tactic| (
  intro s hs
  simp only [Side, SideBr, SideAny] at hs ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hs
  simp only [CheckSPAlignment, state_simp_rules] at h4 ⊢
  simp (config := { decide := true }) only
    [state_simp_rules, minimal_theory, bitvec_rules, Aligned_BitVecSub_64_4,
     Aligned_BitVecAdd_64_4, ↓reduceIte, h1, h2, h3, h4]
  try (split <;> simp_all)))

/-- How control continues after the instruction `inst` at `pc`. -/
inductive Succ where
  | next (npc : BitVec 64)
  | branch (t nt : BitVec 64)
  | unknown

def succOf (pc : BitVec 64) (inst : BitVec 32) : Succ :=
  open ArmInst BranchInst in
  match decode_raw_inst inst with
  | some (BR (Uncond_branch_imm i)) => .next (BR.Uncond_branch_imm_inst.branch_taken_pc i pc)
  | some (BR (Cond_branch_imm i)) => .branch (BR.Cond_branch_imm_inst.branch_taken_pc i pc) (pc + 4#64)
  | some (BR (Compare_branch i)) => .branch (BR.Compare_branch_inst.branch_taken_pc i pc) (pc + 4#64)
  | some (BR (Uncond_branch_reg _)) => .unknown
  | some _ => .next (pc + 4#64)
  | none => .unknown

/-- Try to add the SSA spec `specName` for the step theorem `stepThm` (at `pc`,
continuing as `succ`). Returns `false`, restoring the elaboration state, if its
side-condition obligation cannot be discharged by `arm_ssa_side` within
`maxHeartbeats`. -/
def addSSASpec (stepThm specName : Name) (succ : Succ) : TermElabM Bool := do
  let lit (x : BitVec 64) : TSyntax `term :=
    Syntax.mkApp (mkIdent ``BitVec.ofNat) #[Syntax.mkNumLit "64", Syntax.mkNumLit (toString x.toNat)]
  let thmId := mkIdent stepThm
  let q := mkIdent `Q
  let e := mkIdent `e
  let stx? : Option (TSyntax `term) ← match succ with
    | .next npc => some <$> `(fun ($q : Unit → Assn) ($e : EStack⟨⟩) =>
        @ArmVCGen.stepAt_ssa_spec $q $e _ _ $(lit npc) _ $thmId (by arm_ssa_side))
    | .branch t nt => some <$> `(fun ($q : Unit → Assn) ($e : EStack⟨⟩) =>
        @ArmVCGen.stepAt_ssa_br_spec $q $e _ _ $(lit t) $(lit nt) _ $thmId (by arm_ssa_side))
    | .unknown => some <$> `(fun ($q : Unit → Assn) ($e : EStack⟨⟩) =>
        @ArmVCGen.stepAt_ssa_any_spec $q $e _ _ _ $thmId (by arm_ssa_side))
  let some stx := stx? | return false
  let saved ← saveState
  let fail : TermElabM Bool := do saved.restore; return false
  -- Each attempt gets its own heartbeat budget (`maxHeartbeats`), and a timeout
  -- (a runtime exception) falls back like any other failure.
  tryCatchRuntimeEx (withCurrHeartbeats do
    let val ← Term.withoutErrToSorry do
      let v ← elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      pure v
    let val ← instantiateMVars val
    let ty ← instantiateMVars (← inferType val)
    if val.hasMVar || ty.hasMVar || val.hasSorry || (← Core.getMessageLog).hasErrors then
      return (← fail)
    addDecl <| .thmDecl { name := specName, levelParams := [], type := ty, value := val }
    addSpecAttr specName
    return true) (fun _ => fail)

/-- For every address of `prog` with a step theorem `prog.stepi_eq_0x<addr>`, add a
`vcgen` spec for `stepAt 0x<addr> _`: the SSA spec `prog.vcgen_spec_0x<addr>`
when its side-condition obligation can be discharged, otherwise the plain spec
(see `addVCGenSpec`) under the same name. -/
def addVCGenSpecsFor (progName : Name) : TermElabM Unit := do
  let prog ← unsafe evalExpr Program (mkConst ``Program) (mkConst progName)
  let mut plain := #[]
  for (pc, inst) in prog do
    -- The names `#genStepEqTheorems` gives its step theorems.
    let hex := pc.toHexWithoutLeadingZeroes
    let thm := Name.str progName ("stepi_eq_0x" ++ hex)
    unless (← getEnv).contains thm do continue
    let specName := progName ++ Name.mkSimple ("vcgen_spec_0x" ++ hex)
    if (← getEnv).contains specName then continue
    let succ := succOf pc inst
    -- Fall back to the PC-less SSA spec, then to the plain spec.
    unless (← addSSASpec thm specName succ) || (← addSSASpec thm specName .unknown) do
      plain := plain.push hex
      addVCGenSpec thm specName
  trace[Tactic.vcgen_specs] "plain (non-SSA) specs at: {plain}"

/-- `#genVCGenSpecs prog` adds `vcgen` specifications for the step theorems of
`prog` that already exist. Usually, `set_option genStepEqTheorems.vcgenSpecs true`
before `#genStepEqTheorems prog` is more convenient. -/
elab "#genVCGenSpecs " prog:ident : command => do
  let progName ← liftCoreM <| realizeGlobalConstNoOverload prog
  liftTermElabM <| addVCGenSpecsFor progName

end ArmVCGen

namespace ArmVCGen

/-- `arm_vc_simp` simplifies a verification condition left by `vcgen` on an
`ArmCmd` program: it splits the hypotheses and uses their parts as rewrite
rules, reads fields through the chain of state writes (`state_simp_rules`), and
discharges stack-alignment checks (`if ¬Aligned (sp ± c) 4 then <fault> else …`)
from `CheckSPAlignment` and the alignment of the literal offsets. -/
macro "arm_vc_simp" : tactic => `(tactic|
  simp_all (config := { decide := true }) only
    [CheckSPAlignment, Side, SideBr, SideAny, state_simp_rules, minimal_theory, bitvec_rules,
     Aligned_BitVecSub_64_4, Aligned_BitVecAdd_64_4, ↓reduceIte])

/-- Close the side conditions of a step from the facts the previous step's SSA
spec handed forward (`O(1)` per step). -/
macro "arm_vc_step" : tactic => `(tactic|
  first
    | assumption
    | exact ArmVCGen.Side.plain ‹_›
    | exact ArmVCGen.Side.of_br ‹_› ‹_›
    | exact ArmVCGen.Side.of_br_ne ‹_› ‹_›)

open Lean Elab Tactic Meta in
/-- Prepare the final verification condition: drop the side facts about
intermediate states, then substitute the chain `Next f s s'` of states, so the
goal is about the initial state and the composed effect. -/
elab "arm_vc_expand" : tactic => do
  liftMetaTactic fun (goal0 : MVarId) => goal0.withContext do
    let target ← instantiateMVars (← goal0.getType)
    -- 1. Clear `Side`/`SideBr` facts about states that do not occur in the target.
    let mut goal := goal0
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOf ``ArmVCGen.Side || ty.isAppOf ``ArmVCGen.SideBr ||
         ty.isAppOf ``ArmVCGen.SideAny then
        let st := ty.appArg!
        if st.isFVar && !target.containsFVar st.fvarId! then
          goal ← goal.clear d.fvarId
    -- 2. Turn each `Next f s s'` into `s' = f s` and substitute `s'`.
    let mut progress := true
    while progress do
      progress := false
      let lctx ← goal.withContext getLCtx
      for d in lctx do
        if d.isImplementationDetail then continue
        let ty ← goal.withContext <| instantiateMVars d.type
        if ty.isAppOf ``ArmVCGen.Next then
          let (eqFVar, goal') ← goal.withContext do
            let pf ← mkAppM ``ArmVCGen.Next.eq #[d.toExpr]
            let goal' ← goal.assert `h_next (← inferType pf) pf
            let goal' ← goal'.clear d.fvarId
            goal'.intro1P
          goal ← subst goal' eqFVar
          progress := true
          break
    return [goal]

/-- The postcondition at the end of a segment: expand the state chain once
(`arm_vc_expand`), then simplify as `arm_vc_simp` does, case-splitting on branch
conditions left in the state. -/
macro "arm_vc_final" : tactic => `(tactic|
  (arm_vc_expand
   arm_vc_simp
   try (repeat' (split <;> try arm_vc_simp))))

/-- `arm_vc_final` with extra `simp` lemmas, used when simplifying after the
expansion (e.g. facts about values that only appear once the chain is expanded). -/
syntax "arm_vc_final_with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| arm_vc_final_with [$ls,*]) => `(tactic| (
      arm_vc_expand
      simp_all (config := { decide := true }) only
        [CheckSPAlignment, Side, SideBr, SideAny, state_simp_rules, minimal_theory, bitvec_rules,
         Aligned_BitVecSub_64_4, Aligned_BitVecAdd_64_4, ↓reduceIte, $ls,*]
      try (repeat' (split <;> try simp_all (config := { decide := true }) only
        [CheckSPAlignment, Side, SideBr, SideAny, state_simp_rules, minimal_theory, bitvec_rules,
         Aligned_BitVecSub_64_4, Aligned_BitVecAdd_64_4, ↓reduceIte, $ls,*]))))

/-- Close what can be closed in a verification condition: a step's side
conditions (`arm_vc_step`), else the postcondition (`arm_vc_final`). What
remains is left for e.g. `bv_decide` or `simp_mem`.

For long programs, keep per-VC work constant: do not rewrite the whole context of
every VC (e.g. `subst` a ghost initial state in `all_goals`); that is quadratic.
Do such steps only in the VCs that `arm_vc_step` does not close. -/
macro "arm_vc" : tactic => `(tactic| first | arm_vc_step | arm_vc_final)

end ArmVCGen
