/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Arm.Map
import Tactics.Common

/-!
# ProgramInfo
We establish a `ProgramInfo` structure,
which stores (reflected) information about Arm programs.

Furthermore, we define a persistent env extension to store `ProgramInfo` in.

-/

open Lean Meta Elab.Term

initialize
  registerTraceClass `ProgramInfo

structure ProgramInfo where
  name : Name
  rawProgram : HashMap (BitVec 64) (BitVec 32)

namespace ProgramInfo

def getRawInstrAt? (pi : ProgramInfo) (addr : BitVec 64) :
    Option (BitVec 32) :=
  pi.rawProgram.find? addr

/-- Given the name and defining expression of a `Program`,
generate the basic `ProgramInfo` -/
partial def generateFromExpr (name : Name) (e : Expr) : MetaM ProgramInfo := do
  trace[ProgramInfo] "Generating program info for `{name}` from definition:\n\t{e}"
  let type ← inferType e
  if !(←isDefEq type (mkConst ``Program)) then
    throwError "type mismatch: {e} {← mkHasTypeButIsExpectedMsg type (mkConst ``Program)}"

  let rec go (rawProgram : HashMap _ _) (e : Expr) : MetaM (HashMap _ _) := do
    let e ← whnfD e
    match_expr e with
    | List.cons _ hd tl => do
        trace[ProgramInfo] "found address/instruction pair: {hd}"

        let hd' ← reduce hd
        let_expr Prod.mk _ _ addr inst := hd'
          | throwError "expected `{hd}` to reduce to an application of `Prod.mk`, found:\n\t{hd'}"

        let addr ← reflectBitVecLiteral 64 (← instantiateMVars addr)
        let inst ← reflectBitVecLiteral 32 (← instantiateMVars inst)

        let rawProgram := rawProgram.insert addr inst
        go rawProgram tl
    | List.nil _ => return rawProgram
    | _ => throwError "expected `List.cons _ _` or `List.nil`, found:\n\t{e}"

  return {
    name,
    rawProgram := ← go ∅ e
  }

/-- Given the `Name` of a constant of type `Program`,
generate the basic `ProgramInfo` -/
def generateFromConstName (program : Name) : MetaM ProgramInfo := do
  let .defnInfo defnInfo ← getConstInfo program
    | throwError "expected a definition, but {program} is not"
  generateFromExpr program defnInfo.value

/-! ## Env Extension -/

initialize programInfoExt : PersistentEnvExtension (ProgramInfo) (ProgramInfo) (NameMap ProgramInfo) ←
  registerPersistentEnvExtension {
    name            := `programInfo
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun s p => s.insert p.name p
    exportEntriesFn := fun m =>
      let r : Array (ProgramInfo) :=
        m.fold (fun a name p => a.push {p with name}) #[]
      r.qsort (fun a b => Name.quickLt a.name b.name)
    statsFn         := fun s =>
      "program info extension" ++ Format.line
      ++ "number of local entries: " ++ format s.size
  }

/-- store a `PogramInfo` in the environment -/
private def store [Monad m] [MonadEnv m] (pi : ProgramInfo) : m Unit := do
  modifyEnv (programInfoExt.addEntry · pi)

/-- look up the `ProgramInfo` for a given `program` in the environment,
returns `None` if not found -/
def lookup? [Monad m] [MonadEnv m] (program : Name) :
    m (Option ProgramInfo) := do
  let env ← getEnv
  let state := programInfoExt.getState env
  return state.find? program

/-- look up the `ProgramInfo` for a given `program` in the environment,
or, if none was found, generate (and cache) new program info.

If you pass in a value for `expr?`, that is assumed to be the definition for
`program` when generating new program info.
If you don't pass in an expr, the definition is found in the environment -/
def lookupOrGenerate (program : Name) (expr? : Option Expr := none) :
    MetaM ProgramInfo := do
  if let some pi ← lookup? program then
    return pi
  else
    let pi ← match expr? with
      | some expr => generateFromExpr program expr
      | none      => generateFromConstName program
    store pi
    return pi
