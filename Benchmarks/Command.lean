/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean

open Lean Parser.Command Elab.Command

initialize
  registerTraceClass `Benchmark

#check withHeartbeats

elab "benchmark" id:ident declSig:optDeclSig val:declVal : command => do
  logInfo m!"Running {id} benchmark\n"

  let stx ← `(command|
    set_option trace.benchmark true in
    example $declSig:optDeclSig $val:declVal
  )

  let n := 5
  let mut runTimes := #[]
  let mut totalRunTime := 0
  for _ in [0:n] do
    let start ← IO.monoMsNow
    elabCommand stx
    let endTime ← IO.monoMsNow
    let runTime := endTime - start
    runTimes := runTimes.push runTime
    totalRunTime := totalRunTime + runTime

  let avg := totalRunTime.toFloat / n.toFloat / 1000
  let geomean := (totalRunTime.toFloat.pow (1.0 / n.toFloat)) / 1000.0
  logInfo m!"\
{id}:
  average runtime over {n} runs:
    {avg}s
  geomean over {n} runs:
    {geomean}s

  indidividual runtimes:
    {runTimes}
"

/-- The default `maxHeartbeats` setting.

NOTE: even if the actual default value changes at some point in the future,
this value should *NOT* be updated, to ensure the percentages we've reported
in previous versions remain comparable. -/
private def defaultMaxHeartbeats : Nat := 200000

private def percentOfDefaultMaxHeartbeats (heartbeats : Nat) : Nat :=
  heartbeats / (defaultMaxHeartbeats * 10)

open Elab.Tactic in
elab "logHeartbeats" tac:tactic : tactic => do
  let ((), heartbeats) ← withHeartbeats <|
    evalTactic tac
  let percent := percentOfDefaultMaxHeartbeats heartbeats

  logInfo m!"used {heartbeats / 1000} heartbeats ({percent}% of the default maximum)"

variable {m} [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [MonadOptions m] [MonadTrace m] [MonadRef m] [AddMessageContext m] in
/-- `withBenchmark x` is a combinator that will trace the time and heartbeats
used by `x` to the `benchmark` trace class, in a message like:
  `{header} took {x}s and {y} heartbeats ({z}% of the default maximum)`

NOTE: the maximum reffered to in the message is `defaultMaxHeartbeats`,
deliberately *not* the currently confiugred `maxHeartbeats` option, to keep the
numbers comparable across different values of that option. It's thus entirely
possible to see more than 100% being reported here. -/
def withBenchmark (header : String) (x : m α) : m α := do
  let start ← IO.monoMsNow
  let (a, heartbeats) ← withHeartbeats x
  let t := ((← IO.monoMsNow) - start)
  let percent := percentOfDefaultMaxHeartbeats heartbeats
  trace[Benchmark] m!"{header} took {t}ms and {heartbeats} heartbeats \
    ({percent}% of the default maximum)"
  return a
