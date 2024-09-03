import Lean

open Lean
initialize
  registerTraceClass `Tactic.cse.collection -- CSE phase that collects expressions.
  registerTraceClass `Tactic.cse.summary -- CSE phase that summaries information after collection.
  registerTraceClass `Tactic.cse.generalize -- CSE phase that attempts reperated generalization.

  -- enable tracing for `sym_n` tactic and related components
  registerTraceClass `Tactic.sym

  registerOption `Tactic.sym.debug {
    defValue := true
    descr := "enable/disable type-checking of internal state during execution \
      of the `sym_n` tactic, throwing an error if mal-formed expressions were \
      created"
  }
