/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean

open Lean Parser.Command Elab.Command

elab "benchmark" id:ident declSig:optDeclSig val:declVal : command => do
  let stx ← `(command| example $declSig:optDeclSig $val:declVal )

  let n := 5
  let mut runTimes := #[]
  let mut totalRunTime := 0
  for _ in List.range n do
    let start ← IO.monoMsNow
    elabCommand stx
    let endTime ← IO.monoMsNow
    let runTime := endTime - start
    runTimes := runTimes.push runTime
    totalRunTime := totalRunTime + runTime

  let avg := totalRunTime.toFloat / n.toFloat / 1000
  logInfo m!"\
{id}:
  average runtime over {n} runs:
    {avg}s

  indidividual runtimes:
    {runTimes}
"
