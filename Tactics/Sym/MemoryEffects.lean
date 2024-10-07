/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer, Siddharth Bhat
-/

import Arm.State
import Tactics.Common
import Tactics.Attr
import Tactics.Simp
import Tactics.Sym.Common

import Std.Data.HashMap

open Lean Meta

structure MemoryEffects where
  /-- An expression of a (potentially empty) sequence of `write_mem`s
  to the initial state, which describes the effects on memory.
  See `memoryEffectProof` for more detail -/
  effects : Expr
  /-- An expression that contains the proof of:
    ```lean
    ∀ n addr,
      read_mem_bytes n addr <currentState>
      = read_mem_bytes n addr <all memory effects so far, e.g. (write_mem_bytes n addr val s₀)>
    ``` -/
  proof : Expr
deriving Repr

instance : ToMessageData MemoryEffects where
  toMessageData eff :=
    m!"\
    \{ effects := {eff.effects},
      proof := {eff.proof
    }"

namespace MemoryEffects

/-! ## Initial Reflected State -/

/-- An initial `MemoryEffects`, representing no memory changes to the
initial `state` -/
def initial (state : Expr) : MemoryEffects where
  effects := state
  proof :=
    -- `fun n addr => rfl`
    mkLambda `n .default (mkConst ``Nat) <|
      let bv64 := mkApp (mkConst ``BitVec) (toExpr 64)
      mkLambda `addr .default bv64 <|
        mkApp2 (.const ``Eq.refl [1])
          (mkApp (mkConst ``BitVec) <| mkNatMul (.bvar 1) (toExpr 8))
          (mkApp3 (mkConst ``read_mem_bytes) (.bvar 1) (.bvar 0) state)

/-- Update the memory effects with a memory write -/
def updateWriteMem (eff : MemoryEffects) (currentState : Expr)
    (n addr val : Expr) :
    MetaM MemoryEffects := do
  let effects := mkApp4 (mkConst ``write_mem_bytes) n addr val eff.effects
  let proof :=
    -- `read_mem_bytes_write_mem_bytes_of_read_mem_eq <memoryEffectProof> ...`
    mkAppN (mkConst ``read_mem_bytes_write_mem_bytes_of_read_mem_eq)
      #[currentState, eff.effects, eff.proof, n, addr, val]
  return { effects, proof }

/-- Update the memory effects with a register write.

This doesn't change the actual effect, but since the `currentState` has changed,
we need to update proofs -/
def updateWrite (eff : MemoryEffects) (currentState : Expr)
    (fld val : Expr) :
    MetaM MemoryEffects := do
  let proof := -- `read_mem_bytes_w_of_read_mem_eq ...`
    mkAppN (mkConst ``read_mem_bytes_w_of_read_mem_eq)
      #[currentState, eff.effects, eff.proof, fld, val]
  return { eff with proof }

/-- Transport all proofs along an equality `eq : <currentState> = s`,
so that `s` is the new `currentState` -/
def adjustCurrentStateWithEq (eff : MemoryEffects) (eq : Expr) :
    MetaM MemoryEffects := do
  let proof ← rewriteType eff.proof eq
    -- ^^ TODO: what happens if `memoryEffect` is the same as `currentState`?
    --    Presumably, we would *not* want to encapsulate `memoryEffect` here
  return { eff with proof }

/-- Convert a `MemoryEffects` into a `MessageData` for logging. -/
def toMessageData (eff : MemoryEffects) : MetaM MessageData := do
  let out := m!"effects: {eff.effects}"
  return out

/-- Trace the current state of `MemoryEffects`. -/
def traceCurrentState (eff : MemoryEffects) : MetaM Unit := do
  Sym.traceLargeMsg "memoryEffects" (← eff.toMessageData)



/-- type check all expressions stored in `eff`,
throwing an error if one is not type-correct.

In principle, the various `MemoryEffects` definitions should return only
well-formed expressions, making `validate` a no-op.
In practice, however, running `validate` is helpful for catching bugs in those
definitions. Do note that typechecking might be a bit expensive, so we generally
only call `validate` while debugging, not during normal execution.
See also the `Tactic.sym.debug` option, which controls whether `validate` is
called for each step of the `sym_n` tactic.

NOTE: does not necessarily validate *which* type an expression has,
validation will still pass if types are different to those we claim in the
docstrings
-/
def validate (eff : MemoryEffects) : MetaM Unit := do
  let msg := "validating that the axiomatic effects are well-formed"
  Sym.withTraceNode msg do
    eff.traceCurrentState
    check eff.effects
    assertHasType eff.effects mkArmState

    check eff.proof

end MemoryEffects
