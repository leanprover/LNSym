import Lean

open Lean
initialize
  -- CSE tactic's non-verbose summary logging.
  registerTraceClass `Tactic.cse.summary 
  -- enable tracing for `sym_n` tactic and related components
  registerTraceClass `Tactic.sym
