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

/-- Provides extremely verbose tracing for the `simp_mem` tactic. -/
initialize Lean.registerTraceClass `Tactic.address_normalization

-- Rules for simprocs that mine the state to extract information for `omega`
-- to run.
register_simp_attr memory_omega

-- Simprocs for address normalization
register_simp_attr address_normalization

register_option simp_mem.omegaTimeoutMs : Nat := {
  defValue := 1000
  descr := "maximum amount of time per omega invocation in milliseconds before `simp_mem` times out. `0` for no timeout."
}

register_option simp_mem.omegaNumIgnoredTimeouts: Nat := {
  defValue := 0
  descr := "number of times omega is allowed to timeout before an error is thrown."
}


def getOmegaTimeoutMs [Monad m] [MonadOptions m] : m Nat := do
  return simp_mem.omegaTimeoutMs.get (← getOptions)

def getOmegaNumIgnoredTimeouts [Monad m] [MonadOptions m] : m Nat := do
  return simp_mem.omegaNumIgnoredTimeouts.get (← getOptions)
