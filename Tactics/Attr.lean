import Lean

open Lean
initialize
  registerTraceClass `Tactic.cse.collection -- CSE phase that collects expressions.
  registerTraceClass `Tactic.cse.summary -- CSE phase that summaries information after collection.
  registerTraceClass `Tactic.cse.generalize -- CSE phase that attempts reperated generalization.

  registerTraceClass `Tactic.sym
