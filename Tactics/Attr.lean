/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat, Alex Keizer
-/
import Lean

open Lean
initialize
  -- CSE tactic's non-verbose summary logging.
  registerTraceClass `Tactic.cse.summary

  -- enable tracing for `prune_updates` tactic
  registerTraceClass `Tactic.prune_updates
  -- show the pruned updates in a form that the user can copy/paste into the
  -- theorem's conclusion
  registerTraceClass `Tactic.prune_updates.answer

  registerOption `Tactic.prune_updates.validate {
    defValue := false
    descr := "enable/disable type-checking of internal state during execution \
      of the `prune_updates` tactic.

      This is an internal option for debugging purposes, end users should \
      generally not set this option, unless they are reporting a bug with \
      `prune_updates`"
  }

  -- enable tracing for `sym_n` tactic and related components
  registerTraceClass `Tactic.sym
  -- enable verbose tracing
  registerTraceClass `Tactic.sym.info

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

  -- enable extra checks for debugging `sym_n`,
  -- see `AxEffects.validate` for more detail on what is being type-checked

  register_option Tactic.bv_omega_bench.filePath : String := {
    defValue := "/tmp/omega-bench.txt"
    descr := "File path that `omega-bench` writes its results to."
  }

  register_option Tactic.bv_omega_bench.enabled : Bool := {
    defValue := true,
    descr := "Enable `bv_omega_bench`'s logging, which writes benchmarking data to `Tactic.bv_omega_bench.filePath`."
  }

  register_option Tactic.bv_omega_bench.minMs : Nat := {
    defValue := 1000,
    descr := "Log into `Tactic.bv_omega_bench.filePath` if the time spent in milliseconds is greater than or equal to `Tactic.bv_omega_bench.minMs`."
  }

def getBvOmegaBenchFilePath [Monad m] [MonadOptions m] : m String := do
  return Tactic.bv_omega_bench.filePath.get (← getOptions)


def getBvOmegaBenchIsEnabled [Monad m] [MonadOptions m] : m Bool := do
  return Tactic.bv_omega_bench.enabled.get (← getOptions)

def getBvOmegaBenchMinMs [Monad m] [MonadOptions m] : m Nat := do
  return Tactic.bv_omega_bench.minMs.get (← getOptions)
