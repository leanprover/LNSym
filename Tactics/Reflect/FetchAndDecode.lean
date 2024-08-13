/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Arm.State
import Tactics.Common
import Tactics.Reflect.ProgramInfo

open Lean Meta
open Elab.Tactic Elab.Term

initialize
  Lean.registerTraceClass `Sym.reduceFetchInst

def reduceFetchInst? (addr : Expr) (s : Expr) :
    MetaM (BitVec 32 × Expr) := do
  let e := mkApp2 (mkConst ``fetch_inst) addr s

  let addr ← reflectBitVecLiteral 64 addr
  let ⟨programHyp, program⟩ ← findProgramHyp s
  let programInfo ← try ProgramInfo.lookupOrGenerate program catch err =>
    throwErrorAt
      err.getRef
      "Could not generate ProgramInfo for {program}:\n\n{err.toMessageData}"

  let some rawInst := programInfo.getRawInstrAt? addr
    | throwError "No instruction found at address {addr}"

  trace[Sym.reduceFetchInst] "{Lean.checkEmoji} reduced to: {rawInst}"

  -- Now, construct the proof
  let eqType ← mkEq e (toExpr (some rawInst))
  trace[Sym.reduceFetchInst] "⚙️ deriving a proof of:\n\t{eqType}"

  let h_program := mkIdent programHyp.userName
  let eqProofStx ← `(term| by
    unfold fetch_inst; rw [$h_program:ident]; decide
  )
  let proof ← TermElabM.run' <| do
    let h ← elabTermEnsuringType eqProofStx eqType
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars h

  trace[Sym.reduceFetchInst] "{Lean.checkEmoji} found a proof:\n\t{proof}"
  return ⟨rawInst, proof⟩

simproc reduceFetchInst (fetch_inst _ _) := fun e => do
  trace[Sym.reduceFetchInst] "⚙️ simplifying {e}"
  let_expr fetch_inst addr s := e
    | return .continue

  try
    let ⟨x, proof?⟩ ← reduceFetchInst? addr s
    return .done {expr := toExpr (some x), proof?}
  catch err =>
    trace[Sym.reduceFetchInst] "{Lean.crossEmoji} {err.toMessageData}"
    return .continue
