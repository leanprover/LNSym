/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean

open Lean

namespace Sym

/-! ## Trace Nodes -/
section Tracing
variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadLiftT IO m]
  [MonadRef m] [AddMessageContext m] [MonadOptions m] {ε : Type}
  [MonadAlwaysExcept ε m] [MonadLiftT BaseIO m]

/-- Add a trace node with the `Tactic.sym` trace class -/
def withTraceNode (msg : MessageData) (k : m α)
    (collapsed : Bool := true)
    (tag : String := "")
    : m α := do
  Lean.withTraceNode `Tactic.sym (fun _ => pure msg) k collapsed tag

/-- Add a trace node with the `Tactic.sym.info` trace class -/
def withInfoTraceNode (msg : MessageData) (k : m α)
    (collapsed : Bool := true)
    (tag : String := "")
    : m α := do
  Lean.withTraceNode `Tactic.sym.info (fun _ => pure msg) k collapsed tag

/-- Create a trace note that folds `header` with `(NOTE: can be large)`,
and prints `msg` under such a trace node.
-/
def traceLargeMsg (header : MessageData) (msg : MessageData) : MetaM Unit :=
    withTraceNode m!"{header} (NOTE: can be large)" do
      trace[Tactic.sym] msg

end Tracing

end Sym
