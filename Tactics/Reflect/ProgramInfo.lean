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

-- TODO: upstream this instance
instance {w} : Hashable (BitVec w) where
  hash x := hash x.toNat

structure ProgramInfo where
  rawProgram : HashMap (BitVec 64) (BitVec 32)

def ProgramInfo.getRawInstrAt? (pi : ProgramInfo) (addr : BitVec 64) :
    Option (BitVec 32) :=
  pi.rawProgram.find? addr

/-- Given an `Expr` of type `Program`, generate the basic `ProgramInfo` -/
partial def ProgramInfo.generateFromExpr (e : Expr) : MetaM ProgramInfo := do
  let type ← inferType e
  if !(←isDefEq type (mkConst ``Program)) then
    throwError "type mismatch: {e} {← mkHasTypeButIsExpectedMsg type (mkConst ``Program)}"

  let rec go (rawProgram : HashMap _ _) (e : Expr) : MetaM (HashMap _ _) := do
    let e ← whnfD e
    match_expr e with
    | List.cons _ hd tl => do
        let hd' ← reduce hd
        let_expr Prod.mk _ _ addr inst := hd'
          | throwError "expected `{hd}` to reduce to an application of `Prod.mk`, found:\n\t{hd'}"

        let addr ← reflectBitVecLiteral 64 addr
        let inst ← reflectBitVecLiteral 32 inst

        let rawProgram := rawProgram.insert addr inst
        go rawProgram tl
    | List.nil _ => return rawProgram
    | _ => throwError "expected `List.cons _ _` or `List.nil`, found:\n\t{e}"

  return {
    rawProgram := ← go ∅ e
  }

/-- Given the `Name` of a constant of type `Program`,
generate the basic `ProgramInfo` -/
def ProgramInfo.generateFromConstName (program : Name) : MetaM ProgramInfo := do
  let .defnInfo defnInfo ← getConstInfo program
    | throwError "expected a definition, but {program} is not"
  generateFromExpr defnInfo.value

/-! ## Env Extension -/

initialize programInfoExt : PersistentEnvExtension (Name × ProgramInfo) (Name × ProgramInfo) (NameMap ProgramInfo) ←
  registerPersistentEnvExtension {
    name            := `programInfo
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun s p => s.insert p.1 p.2
    exportEntriesFn := fun m =>
      let r : Array (Name × _) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1)
    statsFn         := fun s =>
      "program info extension" ++ Format.line
      ++ "number of local entries: " ++ format s.size
  }

/-- store a `PogramInfo` for the given `program` in the environment -/
private def ProgramInfo.store [Monad m] [MonadEnv m]
    (program : Name) (pi : ProgramInfo) : m Unit := do
  modifyEnv (programInfoExt.addEntry · ⟨program, pi⟩)

/-- look up the `ProgramInfo` for a given `program` in the environment,
returns `None` if not found -/
def ProgramInfo.lookup? [Monad m] [MonadEnv m] (program : Name) :
    m (Option ProgramInfo) := do
  let env ← getEnv
  let state := programInfoExt.getState env
  return state.find? program

/-- look up the `ProgramInfo` for a given `program` in the environment,
or, if none was found, generate (and cache) new program info -/
def ProgramInfo.lookupOrGenerate (program : Name) : MetaM ProgramInfo := do
  if let some pi ← lookup? program then
    return pi
  else
    let pi ← generateFromConstName program
    store program pi
    return pi
