import Lean

open Lean

/-- Provides tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `simp_mem

/-- Provides extremely verbose tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `simp_mem.info

-- Rules for simprocs that mine the state to extract information for `omega`
-- to run.
register_simp_attr memory_omega
