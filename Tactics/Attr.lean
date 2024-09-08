import Lean

open Lean
initialize
  -- CSE tactic's non-verbose summary logging.
  registerTraceClass `Tactic.cse.summary 
  -- enable tracing for `sym_n` tactic and related components
  registerTraceClass `Tactic.sym

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
