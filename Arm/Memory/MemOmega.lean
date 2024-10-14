/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

In this file, we define proof automation for separation conditions of memory.

References:
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/OmegaM.lean
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/Frontend.lean
-/
import Arm
import Arm.Memory.MemoryProofs
import Arm.BitVec
import Arm.Memory.Attr
import Arm.Memory.AddressNormalization
import Lean
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Conv.Basic
import Tactics.Simp
import Tactics.BvOmegaBench
import Arm.Memory.Common

open Lean Meta Elab Tactic Memory

namespace MemOmega

structure Config where
  /--
    If true, then MemOmega will explode uses of pairwiseSeparate [mem₁, ... memₙ]
    into O(n^2) separation conditions.
  -/
  explodePairwiseSeparate : Bool := false

/-- Edit the config for mem_omega! -/
def Config.mkBang (c : Config) : Config :=
  { c with explodePairwiseSeparate := true }

/-- Context for the `SimpMemM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `simp_mem`. -/
  cfg : Config
  /-- Cache of `bv_toNat` simp context. -/
  bvToNatSimpCtx : Simp.Context
  /-- Cache of `bv_toNat` simprocs. -/
  bvToNatSimprocs : Array Simp.Simprocs


namespace Context

def init (cfg : Config) : MetaM Context := do
  let (bvToNatSimpCtx, bvToNatSimprocs) ←
    LNSymSimpContext
      (config := {failIfUnchanged := false})
      -- Also use `mem_{legal', subset', separate'}.iff_omega to unfold definitions that
      -- occur inside compound expressions, such as (mem_subset' .. ∨ mem_subset' ..)
      -- (thms := #[``mem_legal'.iff_omega, ``mem_subset'.iff_omega, ``mem_separate'.iff_omega])
      (simp_attrs := #[`bv_toNat])
      (useDefaultSimprocs := false)
  return {cfg, bvToNatSimpCtx, bvToNatSimprocs}
end Context

abbrev MemOmegaM := (ReaderT Context MetaM)

namespace MemOmegaM
  def run (ctx : Context) (x : MemOmegaM α) : MetaM α := ReaderT.run x ctx
end MemOmegaM

def memOmega (g : MVarId) : MemOmegaM Unit := do
  g.withContext do
    /- We need to explode all pairwise separate hyps -/
    let rawHyps ← getLocalHyps
    let mut hyps := #[]
    -- extract out structed values for all hyps.
    for h in rawHyps do
      hyps ← hypothesisOfExpr h hyps

    -- only enable pairwise constraints if it is enabled.
    let isPairwiseEnabled := (← readThe Context).cfg.explodePairwiseSeparate
    hyps := hyps.filter (!·.isPairwiseSeparate || isPairwiseEnabled)

    -- used specialized procedure that doesn't unfold everything for the easy case.
    if ← closeMemSideCondition g (← readThe Context).bvToNatSimpCtx (← readThe Context).bvToNatSimprocs hyps then
      return ()
    else
      -- in the bad case, just rip through everything.
      let (_, g) ← Hypothesis.addOmegaFactsOfHyps g hyps.toList #[]

      TacticM.withTraceNode' m!"Reducion to omega" do
        try
          TacticM.traceLargeMsg m!"goal (Note: can be large)"  m!"{g}"
          omega g (← readThe Context).bvToNatSimpCtx (← readThe Context).bvToNatSimprocs
          trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
        catch e =>
          trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"

/--
Allow elaboration of `MemOmegaConfig` arguments to tactics.
-/
declare_config_elab elabMemOmegaConfig MemOmega.Config

/--
Implement the `mem_omega` tactic, which unfolds information about memory
in terms of
-/
syntax (name := mem_omega) "mem_omega" (Lean.Parser.Tactic.config)? : tactic

/--
Implement the `mem_omega` tactic frontend.
-/
syntax (name := mem_omega_bang) "mem_omega!" (Lean.Parser.Tactic.config)? : tactic

@[tactic mem_omega]
def evalMemOmega : Tactic := fun
  | `(tactic| mem_omega $[$cfg]?) => do
    let cfg ← elabMemOmegaConfig (mkOptionalNode cfg)
    liftMetaFinishingTactic fun g => do
      memOmega g |>.run (← Context.init cfg)
  | _ => throwUnsupportedSyntax

@[tactic mem_omega_bang]
def evalMemOmegaBang : Tactic := fun
  | `(tactic| mem_omega! $[$cfg]?) => do
    let cfg ← elabMemOmegaConfig (mkOptionalNode cfg)
    liftMetaFinishingTactic fun g => do
      memOmega g |>.run (← Context.init cfg.mkBang)
  | _ => throwUnsupportedSyntax

end MemOmega
