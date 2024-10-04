/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean

open Lean Parser.Command Elab.Command

initialize
  registerOption `benchmark {
    defValue := false
    descr := "enables/disables benchmarking in `withBenchmark` combinator"
  }
  registerOption `benchmark.runs {
    defValue := (5 : Nat)
    descr := "controls how many runs the `benchmark` command does. \
    NOTE: this value is ignored when the `profiler` option is set to true"
  }
  /- Shouldn't be set directly, instead, use the `benchmark` command -/
  registerTraceClass `benchmark

variable {m} [Monad m] [MonadLiftT BaseIO m] in
/-- Measure the heartbeats and time (in milliseconds) taken by `x` -/
def withHeartbeatsAndMilliseconds (x : m α) : m (α × Nat × Nat) := do
  let start ← IO.monoMsNow
  let (a, heartbeats) ← withHeartbeats x
  let endTime ← IO.monoMsNow
  return ⟨a, heartbeats, endTime - start⟩

/-- Adds a trace node with the `benchmark` class, but only if the profiler
option is *not* set.

We deliberately suppress benchmarking nodes when profiling, since it generally
only adds noise
-/
def withBenchTraceNode (msg : MessageData) (x : CommandElabM α )
    : CommandElabM α := do
  if (← getBoolOption `profiler) then
    x
  else
    withTraceNode `benchmark (fun _ => pure msg) x (collapsed := false)

/--
Run a benchmark for a set number of times, and report the average runtime.

If the `profiler` option is set true, we run the benchmark only once, with:
- `trace.profiler` to true, and
- `trace.profiler.output` set based on the `benchmark.profilerDir` and the
    id of the benchmark
-/
elab "benchmark" id:ident declSig:optDeclSig val:declVal : command => do
  let originalOpts ← getOptions
  let mut n := originalOpts.getNat `benchmark.runs 5
  let mut opts := originalOpts
  opts := opts.setBool `benchmark true
  let stx ← `(command|
    example $declSig:optDeclSig $val:declVal
  )

  if (← getBoolOption `profiler) then
    opts := opts.setBool `trace.profiler true
    opts := opts.setNat `trace.profiler.threshold 1
    n := 1 -- only run once, if `profiler` is set to true
  else
    opts := opts.setBool `trace.benchmark true

  if n = 0 then
    return ()

  -- Set options
  modifyScope fun scope => { scope with opts }

  withBenchTraceNode m!"Running {id} benchmark" <| do
    let mut totalRunTime := 0
    -- geomean = exp(log((a₁ a₂ ... aₙ)^1/n)) =
    -- exp(1/n * (log a₁ + log a₂ + log aₙ)).
    let mut totalRunTimeLog : Float := 0
    for i in [0:n] do
      let runTime ← withBenchTraceNode m!"Run {i+1} (out of {n}):" <| do
        let ((), _, runTime) ← withHeartbeatsAndMilliseconds <|
          elabCommand stx

        trace[benchmark] m!"Proof took {runTime / 1000}s in total"
        pure runTime
      totalRunTime := totalRunTime + runTime
      totalRunTimeLog := totalRunTimeLog + Float.log runTime.toFloat

    let avg := totalRunTime.toFloat / n.toFloat / 1000
    let geomean := (Float.exp (totalRunTimeLog / n.toFloat)) / 1000.0
    trace[benchmark] m!"\
  {id}:
    average runtime over {n} runs:
      {avg}s
    geomean over {n} runs:
      {geomean}s
  "
    -- Restore options
    modifyScope fun scope => { scope with opts := originalOpts }

/-- Set various options to disable linters -/
macro "disable_linters" "in" cmd:command : command => `(command|
set_option linter.constructorNameAsVariable false in
set_option linter.deprecated false in
set_option linter.missingDocs false in
set_option linter.omit false in
set_option linter.suspiciousUnexpanderPatterns false in
set_option linter.unnecessarySimpa false in
set_option linter.unusedRCasesPattern false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
$cmd
)

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

section withBenchmark
variable {m} [Monad m] [MonadLiftT BaseIO m] [MonadOptions m] [MonadLog m]
  [AddMessageContext m]

/-- if the `benchmark` option is true, execute `x` and call `f` with the amount
of heartbeats and milliseconds (in that order!) taken by `x`.

Otherwise, just execute `x` without measurements. -/
private def withBenchmarkAux (x : m α) (f : Nat → Nat → m Unit)  : m α := do
  if (← getBoolOption `benchmark) = false then
    x
  else
    let (a, heartbeats, t) ← withHeartbeatsAndMilliseconds x
    f heartbeats t
    return a


/-- `withBenchmark header x` is a combinator that will, if the `benchmark`
option is set to `true`, log the time and heartbeats used by `x`,
in a message like:
  `{header} took {x}s and {y} heartbeats ({z}% of the default maximum)`

Otherwise, if `benchmark` is set to false, `x` is returned as-is.

NOTE: the maximum reffered to in the message is `defaultMaxHeartbeats`,
deliberately *not* the currently confiugred `maxHeartbeats` option, to keep the
numbers comparable across different values of that option. It's thus entirely
possible to see more than 100% being reported here. -/
def withBenchmark (header : String) (x : m α) : m α := do
  withBenchmarkAux x fun heartbeats t => do
    let percent := percentOfDefaultMaxHeartbeats heartbeats
    logInfo m!"{header} took: {t}ms and {heartbeats} heartbeats \
      ({percent}% of the default maximum)"

/-- Benchmark the time and heartbeats taken by a tactic, if the `benchmark`
option is set to `true` -/
elab "with_benchmark" t:tactic : tactic => do
  withBenchmark "{t}" <| Elab.Tactic.evalTactic t

end withBenchmark

/-!
## Aggregated benchmark statistics
We define `withAggregatedBenchmark`, which functions like `withBenchmark`,
except it will store a running average of the statistics in a `BenchmarkState`
which will be reported in one go when `reportAggregatedBenchmarks` is called.
-/
section

structure BenchmarkState.Stats where
  totalHeartbeats : Nat := 0
  totalTimeInMs : Nat := 0
  samples : Nat := 0

structure BenchmarkState where
  insertionOrder : List String := []
  stats : Std.HashMap String BenchmarkState.Stats := .empty

variable {m} [Monad m] [MonadStateOf BenchmarkState m] [MonadLiftT BaseIO m]
  [MonadOptions m]

/-- `withAggregatedBenchmark header x` is a combinator that will,
if the `benchmark` option is set to `true`,
measure the time and heartbeats to the benchmark state in a way that aggregates
different measurements with the same `header`.

See `reportAggregatedBenchmarks` to log the collected data.

Otherwise, if `benchmark` is set to false, `x` is returned as-is.
-/
def withAggregatedBenchmark (header : String) (x : m α) : m α := do
  withBenchmarkAux x fun heartbeats t => do
    modify fun state =>
      let s := state.stats.getD header {}
      { insertionOrder :=
          if s.samples = 0 then
            header :: state.insertionOrder
          else
            state.insertionOrder
        stats := state.stats.insert header {
          totalHeartbeats := s.totalHeartbeats + heartbeats
          totalTimeInMs   := s.totalTimeInMs + t
          samples         := s.samples + 1
      }}

variable [MonadLog m] [AddMessageContext m] in
/--
if the `benchmark` option is set to `true`, report the data collected by
`withAggregatedBenchmark`, and reset the state (so that the next call to
`reportAggregatedBenchmarks` will report only new data).
-/
def reportAggregatedBenchmarks : m Unit := do
  if (← getBoolOption `benchmark) = false then
    return

  let { insertionOrder, stats } ← get
  for header in insertionOrder do
    let stats := stats.getD header {}
    let heartbeats := stats.totalHeartbeats
    let percent := percentOfDefaultMaxHeartbeats heartbeats
    let t := stats.totalTimeInMs
    let n := stats.samples
    logInfo m!"{header} took: {t}ms and {heartbeats} heartbeats \
      ({percent}% of the default maximum) in total over {n} samples"

  set ({} : BenchmarkState)

abbrev BenchT := StateT BenchmarkState

variable [MonadLog m] [AddMessageContext m] in
/--
Execute `x` with the default `BenchmarkState`, and report the benchmarks after
(see `reportAggregatedBenchmarks`).
-/
def withBenchmarksReport (x : BenchT m α) : m α :=
  (Prod.fst <$> ·) <| StateT.run (s := {}) do
    let a ← x
    reportAggregatedBenchmarks
    return a

end
