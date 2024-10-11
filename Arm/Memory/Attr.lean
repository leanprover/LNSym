/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat
-/

import Lean

open Lean

/-- Provides tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `simp_mem

/-- Provides extremely verbose tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `simp_mem.info

/-- Provides even more verbose tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `simp_mem.expr_walk_trace

/-- Provides extremely verbose tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `Tactic.address_normalization

-- Rules for simprocs that mine the state to extract information for `omega`
-- to run.
register_simp_attr memory_omega

-- Simprocs for address normalization
register_simp_attr address_normalization
