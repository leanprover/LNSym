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

/-
Make the `SimpContext` that corresponds to using `bv_toNat` 
Adapted mkSimpContext:
from https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean#L287
-/
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
def run (g : MVarId) (hyps : Array Expr) (bvToNatSimpCtx : Simp.Context) (bvToNatSimprocs : Array Simp.Simprocs) : MetaM Unit := do
  let minMs ← getBvOmegaBenchMinMs
  let goalStr ← ppGoal g
  let startTime ← IO.monoMsNow
  let filePath ← getBvOmegaBenchFilePath
  let mut g := g
  let mut hypFVars : Array FVarId := hyps.filterMap (fun e => if e.isFVar then some e.fvarId! else none)
  try
     /- Wow, this is gross. I need to filter out the fvars, and keep track of which ones I use for simplification. -/
     try
       let (result?, _stats) ← g.withContext <| simpGoal g bvToNatSimpCtx bvToNatSimprocs (simplifyTarget := true) (discharge? := .none) hypFVars
       let .some (hypFVars', g') := result? | return ()
       g := g'
       let hypsOldRetained ← g.withContext <| pure (← getLCtx).getFVarIds
       let hypsOldRetained := hypsOldRetained.filter (fun fvar => hypFVars.contains fvar)
       -- hypFVars := hypFVars'
     catch e => 
       trace[simp_mem.info] "in BvOmega, ran `simp only [bv_toNat]` and got error: {indentD e.toMessageData}"
       throw e
     let some g' ← g.withContext <| g.falseOrByContra | return ()
     g := g'
     g.withContext do
       -- omega (hypExprs ++ hypFVars.map (Expr.fvar)).toList g {}
       omega (← getLocalHyps).toList g {}
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

/-- Build the default simp context (bv_toNat) and run omega -/
def runWithDefaultSimpContext (g : MVarId) : MetaM Unit := do
  let (bvToNatSimpCtx, bvToNatSimprocs) ← bvOmegaSimpCtx
  g.withContext do
    run g ((← g.getNondepPropHyps).map Expr.fvar) bvToNatSimpCtx bvToNatSimprocs

end BvOmegaBench

syntax (name := bvOmegaBenchTac) "bv_omega_bench" : tactic

@[tactic bvOmegaBenchTac]
def bvOmegaBenchImpl : Tactic
| `(tactic| bv_omega_bench) =>
    liftMetaFinishingTactic fun g => do
      BvOmegaBench.runWithDefaultSimpContext g
| _ => throwUnsupportedSyntax
