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

theorem fetch_inst_eq_of_prgram_eq_of_map_find
    {state : ArmState} {program : Program}
    {addr : BitVec 64} {inst? : Option (BitVec 32)}
    (h_program : state.program = program)
    (h_map : program.find? addr = inst?) :
    fetch_inst addr state = inst? := by
  rw [fetch_inst, h_program, h_map]

def reduceFetchInst? (addr : Expr) (s : Expr) :
    MetaM (BitVec 32 × Expr) := do
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
  let proof := mkAppN (mkConst ``fetch_inst_eq_of_prgram_eq_of_map_find) #[
    s,
    mkConst program,
    toExpr addr,
    toExpr (some rawInst),
    programHyp.toExpr,
    mkApp2 (.const ``Eq.refl [1])
      (mkApp (.const ``Option [0]) <|
        mkApp (.const ``BitVec []) (toExpr 32))
      (toExpr (some rawInst))
  ]
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
