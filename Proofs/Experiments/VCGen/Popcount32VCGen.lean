/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tactics.VCGen
import Proofs.Popcount32

/-!
# Experimental: `popcount32_sym_meets_spec` with Lean's `vcgen`

The same specification as `Proofs/Popcount32.lean`, proved with Lean's `vcgen`
over the `ArmVCGen.ArmCmd` embedding (see `Tactics/VCGen.lean`) instead of
`sym_n`.

1. `popcount32_cmd` is the program's control flow as an `ArmCmd`: here a
   straight line of 27 `stepAt pc inst` nodes, built from the program by
   `buildSeg`.
2. `#genVCGenSpecs` turns the step theorems that `Proofs/Popcount32.lean`
   generated with `#genStepEqTheorems` into one `vcgen` spec per address.
3. `popcount32_vcgen` is the specification as a Hoare triple
   `⦃ pre ⦄ popcount32_cmd ⦃ post ⦄`; `vcgen` reduces it to verification
   conditions, `arm_vc` closes all but the final postcondition, and the usual
   `bv_decide` / register-frame / `simp_mem` steps close that.
4. `popcount32_vcgen_run` restates it in LNSym's usual form, about `run 27`;
   its statement is exactly that of `popcount32_sym_meets_spec`.
-/

open Std.WP ArmVCGen
set_option experimental.vcgen true

namespace Popcount32VCGen

#genVCGenSpecs popcount32_program

-- The control flow of `popcount32_program` from its entry: the 27
-- instructions in order, ending at the `ret`.
#genVCGenSegment popcount32_cmd :=
  buildSeg popcount32_program (fun _ => false) 1000 0x4005b4#64

/-- How to read the triple: if the precondition holds of the start state `s`,
then after executing `popcount32_cmd` the postcondition holds of the final
state `sf` (the `_` is the command's unit result). The precondition's conjuncts
are the hypotheses of `popcount32_sym_meets_spec`; the postcondition is its
conclusion. `s0` is a ghost copy of the initial state (`s = s0`), so that the
postcondition can refer to the initial state, e.g. in the frame conditions. -/
theorem popcount32_vcgen (s0 : ArmState) :
    ⦃ fun s => s = s0 ∧ s.program = popcount32_program ∧ r StateField.PC s = 0x4005b4#64 ∧
               r StateField.ERR s = StateError.None ∧ CheckSPAlignment s ⦄
    popcount32_cmd
    ⦃ fun _ sf => r StateField.ERR sf = StateError.None ∧
                  ArmState.w0 sf = popcount32_spec (ArmState.w0 s0) ∧
                  REGS_UNCHANGED_EXCEPT [(.GPR 0), (.GPR 1), .SP, .PC] (sf, s0) ∧
                  MEM_UNCHANGED_EXCEPT [((r .SP s0 - 16#64), 16)] (sf, s0) ⦄ := by
  unfold popcount32_cmd
  vcgen
  -- One VC per instruction (its side conditions) and one for the postcondition.
  -- `arm_vc_step` closes the former from the facts each step hands forward. The
  -- latter alone substitutes the ghost `s0` (doing so in every VC would make the
  -- cost quadratic) and is reduced by `arm_vc_final` to the three parts below.
  all_goals first
    | arm_vc_step
    | (obtain ⟨rfl, _⟩ := ‹_ = s0 ∧ _›; arm_vc_final)
  refine ⟨?_, ?_, ?_⟩
  · -- Functional correctness
    simp only [popcount32_spec, popcount32_spec_rec]
    bv_decide
  · -- Register frame condition
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
    obtain ⟨h0, h1, h31, hpc⟩ := hf
    simp only [state_simp_rules, h0, h1, h31, hpc, ne_eq, not_false_eq_true]
  · -- Memory frame condition
    intro n addr h_separate
    simp only [memory_rules] at *
    repeat simp_mem
    rfl

/-- `popcount32_sym_meets_spec`, derived from the triple. -/
theorem popcount32_vcgen_run (s0 sf : ArmState)
    (h_s0_pc         : read_pc s0 = 0x4005b4#64)
    (h_s0_program    : s0.program = popcount32_program)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_s0_err        : read_err s0 = StateError.None)
    (h_run           : sf = run 27 s0) :
    read_err sf = StateError.None ∧
    ArmState.w0 sf = popcount32_spec (ArmState.w0 s0) ∧
    REGS_UNCHANGED_EXCEPT [(.GPR 0), (.GPR 1), .SP, .PC] (sf, s0) ∧
    MEM_UNCHANGED_EXCEPT [((r .SP s0 - 16#64), 16)] (sf, s0) := by
  subst h_run
  exact run_of_triple (c := popcount32_cmd) rfl (popcount32_vcgen s0)
    ⟨rfl, h_s0_program, h_s0_pc, h_s0_err, h_s0_sp_aligned⟩

end Popcount32VCGen
