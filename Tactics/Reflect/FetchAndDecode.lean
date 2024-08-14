/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Arm.State
import Arm.Decode
import Tactics.Common
import Tactics.Reflect.ProgramInfo

open Lean Meta
open Elab.Tactic Elab.Term

initialize
  Lean.registerTraceClass `Sym.reduceFetchDecode

/-! ## `reduceFetchInst?` -/

theorem fetch_inst_eq_of_prgram_eq_of_map_find
    {state : ArmState} {program : Program}
    {addr : BitVec 64} {inst? : Option (BitVec 32)}
    (h_program : state.program = program)
    (h_map : program.find? addr = inst?) :
    fetch_inst addr state = inst? := by
  rw [fetch_inst, h_program, h_map]

/-- Reduce an expression `fetch_inst $addr $s` to a concrete bitvector `x`,
assuming we have some hypothesis `$s.program = ?concreteProgram` in the local
context, while also returning a proof that `toExpr (some x)` is equal to
the original expression -/
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

  trace[Sym.reduceFetchDecode] "{Lean.checkEmoji} reduced to: {rawInst}"

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
  trace[Sym.reduceFetchDecode] "{Lean.checkEmoji} found a proof:\n\t{proof}"
  return ⟨rawInst, proof⟩



/-! ## `reduceDecodeInst?` -/

/-- `canonicalizeBitVec e` recursively walks over expression `e` to convert any
occerences of:
  `BitVec.ofFin w (Fin.mk x _)`
to the canonical form:
  `BitVec.ofNat w x` (i.e., `x#w`)
 -/
-- TODO: should this canonicalize to `BitVec.ofNatLt` instead,
--       as the current transformation loses information?
partial def canonicalizeBitVec (e : Expr) : MetaM Expr := do
  match_expr e with
    | BitVec.ofFin w i =>
        let_expr Fin.mk _ x _h := i | fallback
        let w ←
          if w.hasFVar || w.hasMVar then
            pure w
          else
            withTransparency .all <| reduce w -- NOTE: potentially expensive reduction
        return mkApp2 (mkConst ``BitVec.ofNat) w x
    | _ => fallback
  where
    fallback : MetaM Expr := do
      let fn   := e.getAppFn
      let args  ← e.getAppArgs.mapM canonicalizeBitVec
      return mkAppN fn args

/-- Given an expr `rawInst` of type `BitVec 32`,
return an expr of type `Option ArmInst` representing what `rawInst` decodes to.
The resulting expr is guaranteed to be def-eq to `fetch_inst $rawInst` -/
def reduceDecodeInst? (rawInst : Expr) : MetaM Expr := do
  let expr := mkApp (mkConst ``decode_raw_inst) rawInst
  let expr ← withTransparency .all <| reduce expr
  canonicalizeBitVec expr

/-! ## Simprocs -/

simproc reduceFetchInst (fetch_inst _ _) := fun e => do
  trace[Sym.reduceFetchDecode] "⚙️ simplifying {e}"
  let_expr fetch_inst addr s := e
    | return .continue

  try
    let ⟨x, proof?⟩ ← reduceFetchInst? addr s
    return .done {expr := toExpr (some x), proof?}
  catch err =>
    trace[Sym.reduceFetchDecode] "{Lean.crossEmoji} {err.toMessageData}"
    return .continue

simproc reduceDecodeInst (decode_raw_inst _) := fun e => do
  trace[Sym.reduceFetchDecode] "⚙️ simplifying {e}"
  let_expr decode_raw_inst rawInst := e
    | trace[Sym.reduceFetchDecode] "{Lean.crossEmoji} did not match pattern"
      return .continue
  let expr ← reduceDecodeInst? rawInst
  trace[Sym.reduceFetchDecode] "{Lean.checkEmoji} simplified to: {expr}"
  return .visit {expr}
