import Lean

open Lean

/-- Provides tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `simp_mem

/-- Provides extremely verbose tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `simp_mem.info
