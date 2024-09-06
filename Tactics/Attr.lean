import Lean

open Lean
initialize
  registerTraceClass `Tactic.cse.collection -- CSE phase that collects expressions.
  registerTraceClass `Tactic.cse.summary -- CSE phase that summaries information after collection.
  registerTraceClass `Tactic.cse.generalize -- CSE phase that attempts reperated generalization.

  -- enable tracing for `sym_n` tactic and related components
  registerTraceClass `Tactic.sym

  -- enable tracing for heartbeat usage of `sym_n`
  registerTraceClass `Tactic.sym.heartbeats

  -- enable extra checks for debugging `sym_n`,
  -- see `AxEffects.validate` for more detail on what is being type-checked
  registerOption `Tactic.sym.debug {
    defValue := true
    descr := "enable/disable type-checking of internal state during execution \
      of the `sym_n` tactic, throwing an error if mal-formed expressions were \
      created, indicating a bug in the implementation of `sym_n`.

      This is an internal option for debugging purposes, end users should \
      generally not set this option, unless they are reporting a bug with \
      `sym_n`"
  }
