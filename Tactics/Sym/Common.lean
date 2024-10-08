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

def withTraceNode (msg : MessageData) (k : m α)
    (collapsed : Bool := true)
    (tag : String := "")
    : m α := do
  Lean.withTraceNode `Tactic.sym (fun _ => pure msg) k collapsed tag

def withVerboseTraceNode (msg : MessageData) (k : m α)
    (collapsed : Bool := true)
    (tag : String := "")
    : m α := do
  Lean.withTraceNode `Tactic.sym.verbose (fun _ => pure msg) k collapsed tag

end Tracing

end Sym
