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

structure InstInfo where
  /-- the raw instruction, as a bitvector -/
  rawInst : BitVec 32

  /-- the decoded instruction, as a normalized(!) `Expr` of type `ArmInst`.
  That is, `decode_raw_inst <rawInst>` should be def-eq to `some <decodeInst>`.

  NOTE: a `none` value indicates that this expression has not been computed yet,
  *not* that `decode_raw_inst` returned `none`-- we assume that
  all instructions for which we generate an `InstInfo` are well-formed -/
  decodedInst? : Option Expr

  /-- if `instSemantics?` is `some ⟨sem, proof⟩`, then
  - `sem` is the instruction semantics, as a normalized(!) expression of type
      `ArmState → ArmState`, and
  - `proof` holds the proof that
    ```lean
    ∀ s (h_program : s.program = <program>) (h_pc : read_pc s = <PC>)
        (h_err : read_err s = .None),
      exec_inst s = <sem> s
    ```

  Otherwise, if the field is `none`, this indicates that the relevant
  expressions have not been computed/cached yet. -/
  instSemantics? : Option (Expr × Expr)

structure ProgramInfo where
  name : Name
  instructions : HashMap (BitVec 64) InstInfo

namespace ProgramInfo

/-- The expression `mkConst pi.name`,
i.e., an expression of this program referred to by name -/
def expr (pi : ProgramInfo) : Expr := mkConst pi.name

def getInstInfoAt? (pi : ProgramInfo) (addr : BitVec 64) :
    Option InstInfo :=
  pi.instructions.find? addr

def getRawInstAt? (pi : ProgramInfo) (addr : BitVec 64) :
    Option (BitVec 32) :=
  (·.rawInst) <$> pi.getInstInfoAt? addr

-- TODO: this instance could be upstreamed (after cleaning it up)
instance [BEq α] [Hashable α] : ForIn m (HashMap α β) (α × β) where
  forIn map acc f := do
    let f := fun (acc : ForInStep _) key val => do
      match acc with
        | .yield acc  => f ⟨key, val⟩ acc
        | .done _     => return acc
    match ← map.foldM f (ForInStep.yield acc) with
     | .done x | .yield x => return x

/-! ## ProgramInfo Generation -/

/-- Given the name and defining expression of a `Program`,
generate the basic `ProgramInfo` -/
partial def generateFromExpr (name : Name) (e : Expr) : MetaM ProgramInfo := do
  trace[ProgramInfo] "Generating program info for `{name}` from definition:\n\t{e}"
  let type ← inferType e
  if !(←isDefEq type (mkConst ``Program)) then
    throwError "type mismatch: {e} {← mkHasTypeButIsExpectedMsg type (mkConst ``Program)}"

  let rec go (instructions : HashMap _ _) (e : Expr) : MetaM (HashMap _ _) := do
    let e ← whnfD e
    match_expr e with
    | List.cons _ hd tl => do
        trace[ProgramInfo] "found address/instruction pair: {hd}"

        let hd' ← reduce hd
        let_expr Prod.mk _ _ addr inst := hd'
          | throwError "expected `{hd}` to reduce to an application of `Prod.mk`, found:\n\t{hd'}"

        let addr ← reflectBitVecLiteral 64 (← instantiateMVars addr)
        let inst ← reflectBitVecLiteral 32 (← instantiateMVars inst)

        let rawProgram := instructions.insert addr ⟨inst, none, none⟩
        go rawProgram tl
    | List.nil _ => return instructions
    | _ => throwError "expected `List.cons _ _` or `List.nil`, found:\n\t{e}"

  return {
    name,
    instructions := ← go ∅ e
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

/-- persistently store a `PogramInfo` in the environment -/
def persistToEnv [Monad m] [MonadEnv m] (pi : ProgramInfo) : m Unit := do
  modifyEnv (programInfoExt.addEntry · pi)

/-- look up the `ProgramInfo` for a given `program` in the environment,
returns `None` if not found -/
def lookup? [Monad m] [MonadEnv m] (program : Name) :
    m (Option ProgramInfo) := do
  let env ← getEnv
  let state := programInfoExt.getState env
  return state.find? program

/-- look up the `ProgramInfo` for a given `program` in the environment,
or, if none was found, generate new program info.

If you pass in a value for `expr?`, that is assumed to be the definition for
`program` when generating new program info.
If you don't pass in an expr, the definition is found in the environment

If `persist` is set to true (the default), then the newly generated program info
will be persistently cached in the environment (see `persistToEnv`) -/
def lookupOrGenerate (program : Name) (expr? : Option Expr := none)
    (persist : Bool := true) :
    MetaM ProgramInfo := do
  if let some pi ← lookup? program then
    return pi
  else
    let pi ← match expr? with
      | some expr => generateFromExpr program expr
      | none      => generateFromConstName program
    if persist then
      persistToEnv pi
    return pi

end ProgramInfo

/-! ## `ProgramInfoT` Monad Transformer -/

abbrev ProgramInfoT (m : Type → Type) := StateT ProgramInfo m

namespace ProgramInfoT
variable [Monad m] [MonadEnv m] [MonadError m]

/-! ### run -/
section Run
variable [MonadLiftT MetaM m]

protected def run' (programName : Name) (expr? : Option Expr) (persist : Bool)
    (k : ProgramInfoT m α) : m α := do
  let pi ← ProgramInfo.lookupOrGenerate programName expr?
  let ⟨a, pi⟩ ← StateT.run k pi
  if persist then
    pi.persistToEnv
  return a

/-- run a `ProgramInfoT m` by looking up, or generating new program info,
by name.

If `persist` is set to true, then the program info state after
executing `k` will be persistently cached in the environment
(see `persistToEnv`). -/
def run (programName : Name) (persist : Bool := false)
    (k : ProgramInfoT m α) : m α :=
  ProgramInfoT.run' programName none persist k

/-- run a `ProgramInfoT m` by looking up, or generating new program info.
The passed expression is assumed to be the definition of the program.

If `persist` is set to true (the default), then the program info state after
executing `k` will be persistently cached in the environment
(see `persistToEnv`). -/
def runE (programName : Name) (expr : Expr) (persist : Bool := false)
    (k : ProgramInfoT m α) : m α :=
  ProgramInfoT.run' programName expr persist k

end Run

/-! ### MonadError instance -/

instance [Monad m] [i : MonadError m] : MonadError (ProgramInfoT m) where
  throw e       := i.throw e
  tryCatch k f  := fun s => i.tryCatch (k s) (fun e => f e s)
  getRef        := i.getRef
  withRef stx k := fun s => i.withRef stx (k s)
  add stx msg   := i.add stx msg

/-! ### Wrappers -/

/-- Persistently store the `ProgramInfo` state in the environment,
so that cached information will be available in downstream files as wells -/
def persistToEnv : ProgramInfoT m Unit := do
  (← StateT.get).persistToEnv
end ProgramInfoT
