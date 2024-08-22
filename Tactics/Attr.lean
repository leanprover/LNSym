import Lean

open Lean
initialize
  registerTraceClass `Tactic.cse.summary -- CSE phase that summaries information after collection.
