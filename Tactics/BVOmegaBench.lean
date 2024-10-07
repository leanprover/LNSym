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
open Lean Elab Meta Tactic

syntax (name := bvOmegaBench) "bv_omega_bench" : tactic

namespace BvOmegaBench

/--
Run bv_omega, gather the results, and then store them at the value that is given by the option.
By default, it's stored at `pwd`, with filename `omega-bench`. The file is appended to,
with the goal state that is being run, and the time elapsed to solve the goal if the goal
was solved, and a 'failed to solve goal' if the goal was left unsolved.
-/
def run : TacticM Unit := do
  let goal ← getMainGoal
  let startTime ← IO.monoMsNow
  try
    withoutRecover do
    evalTactic (← `(tactic| bv_omega))
    let endTime ← IO.monoMsNow
    let delta := endTime - startTime
    let filePath ← getBvOmegaBenchFilePath
    IO.FS.withFile filePath IO.FS.Mode.append fun h => do
      if delta >= 1000 then
        h.putStrLn "\n---\n"
        h.putStrLn s!"time"
        h.putStrLn s!"{delta}"
        h.putStrLn s!"endtime"
        h.putStrLn s!"goal"
        h.putStrLn (← m!"{goal}".toString)
        h.putStrLn s!"endgoal"
  catch e =>
    throw e
  return ()

end BvOmegaBench


@[tactic bvOmegaBench]
def bvOmegaBenchTac : Tactic
| `(tactic| bv_omega_bench) =>
   BvOmegaBench.run
| _ => throwUnsupportedSyntax
