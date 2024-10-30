/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat
-/
/-
This module implements `bv_omega_bench`, which writes benchmarking results of `bv_omega`
into a user-defined file. This is used for extracting out calls to `bv_omega` that are slow,
and allows us to send bug reports to the Lean developers.
-/
import Tactics.Attr
import Lean
import Lean.Elab.Tactic.Omega.Frontend
import Lean.Elab.Tactic.Omega
import Tactics.Simp

open Lean Elab Meta Tactic Omega

namespace BvOmegaBench


-- Adapted mkSimpContext:
-- from https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean#L287
def bvOmegaSimpCtx : MetaM (Simp.Context ×  Array Simp.Simprocs) := do
  let mut simprocs := #[]
  let mut simpTheorems := #[]

  let some ext ← (getSimpExtension? `bv_toNat)
    | throwError m!"[omega] Error: unable to find `bv_toNat"
  simpTheorems := simpTheorems.push (← ext.getTheorems)

  if let some ext ← (Simp.getSimprocExtension? `bv_toNat) then
    let s ← ext.getSimprocs
    simprocs := simprocs.push s

  let congrTheorems ← Meta.getSimpCongrTheorems
  let config : Simp.Config := { failIfUnchanged := false }
  let ctx : Simp.Context := { config, simpTheorems, congrTheorems }
  return (ctx, simprocs)

/--
Run bv_omega, gather the results, and then store them at the value that is given by the option.
By default, it's stored at `pwd`, with filename `omega-bench`. The file is appended to,
with the goal state that is being run, and the time elapsed to solve the goal is written.

Code adapted from: 
- https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean#L406
- https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Omega/Frontend.lean#L685
-/
def run (g : MVarId) : MetaM Unit := do
  let minMs ← getBvOmegaBenchMinMs
  let goalStr ← ppGoal g
  let startTime ← IO.monoMsNow
  let filePath ← getBvOmegaBenchFilePath
  try
      g.withContext do
        let (bvToNatSimpCtx, bvToNatSimprocs) ← bvOmegaSimpCtx
        let nonDepHyps ← g.getNondepPropHyps
        let mut g := g

        try
          let (result?, _stats) ← 
            simpGoal g bvToNatSimpCtx bvToNatSimprocs
              (simplifyTarget := true) (discharge? := .none) nonDepHyps
          let .some (_, g') := result? | return ()
          g := g'
        catch e => 
          trace[simp_mem.info] "in BvOmega, ran `simp only [bv_toNat]` and got error: {indentD e.toMessageData}"
          throw e

        g.withContext do 
          let some g ← g.falseOrByContra | return ()
          g.withContext do
            let hyps := (← getLocalHyps).toList
            omega hyps g {}
            let endTime ← IO.monoMsNow
            let delta := endTime - startTime
            if (← getBvOmegaBenchIsEnabled) && delta ≥ minMs then 
              IO.FS.withFile filePath IO.FS.Mode.append fun h => do
                  h.putStrLn "\n---\n"
                  h.putStrLn s!"goal"
                  h.putStrLn goalStr.pretty
                  h.putStrLn s!"endgoal"
                  h.putStrLn s!"time"
                  h.putStrLn s!"{delta}"
                  h.putStrLn s!"endtime"
  catch e =>
    let endTime ← IO.monoMsNow
    let delta := endTime - startTime
    if (← getBvOmegaBenchIsEnabled) && delta ≥ minMs then 
      IO.FS.withFile filePath IO.FS.Mode.append fun h => do
          h.putStrLn "\n---\n"
          h.putStrLn s!"goal"
          h.putStrLn goalStr.pretty
          h.putStrLn s!"endgoal"
          h.putStrLn s!"time"
          h.putStrLn s!"{delta}"
          h.putStrLn s!"endtime"
          h.putStrLn s!"error"
          h.putStrLn s!"{← e.toMessageData.toString}"
          h.putStrLn s!"enderror"
    throw e

end BvOmegaBench

syntax (name := bvOmegaBenchTac) "bv_omega_bench" : tactic

@[tactic bvOmegaBenchTac]
def bvOmegaBenchImpl : Tactic
| `(tactic| bv_omega_bench) =>
    liftMetaFinishingTactic fun g => do
      BvOmegaBench.run g
| _ => throwUnsupportedSyntax
