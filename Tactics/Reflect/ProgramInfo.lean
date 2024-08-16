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

/-- `OnDemand α` is morally an `Option α`,
we use it for values that are computed, and cached, on demand. -/
inductive InstInfo.OnDemand (α : Type)
  /-- a value has not yet been cached,
  you should run the relevant computation -/
  | notYetComputed
  /-- a value has been cached -/
  | value (value : α)
open InstInfo (OnDemand)

structure InstInfo where
  /-- the raw instruction, as a bitvector -/
  rawInst : BitVec 32

  /-- the decoded instruction, as a normalized(!) `Expr` of type `ArmInst`.
  That is, `decode_raw_inst <rawInst>` should be def-eq to `some <decodeInst>`.
  -/
  decodedInst? : OnDemand Expr :=
    .notYetComputed

  /-- if `instSemantics?` is `⟨sem, type, proof⟩`, then
  - `sem` is the instruction semantics, as a simplified expression of type
      `ArmState → ArmState`.

    That is, we've ran `simp` on `sem` with our dedicated simp-sets in the hopes
    of obtaining only a sequence of `w` and `write_mem`s to the initial state.
    However, note that some instructions might have conditional behaviour,
    in which case `sem` might still contain `if`s
  - `type` is the expression
    ```lean
    ∀ s (h_program : s.program = <program>) (h_pc : read_pc s = <PC>)
        (h_err : read_err s = .None),
      exec_inst s = <sem> s
    ```
  - `proof` is a proof of type `type`
  -/
  instSemantics? : OnDemand (Expr × Expr × Expr) :=
    .notYetComputed

structure ProgramInfo where
  name : Name
  instructions : HashMap (BitVec 64) InstInfo

--------------------------------------------------------------------------------

/-! ## InstInfoT -/

/-- A monad transformer with `InstInfo` state -/
abbrev InstInfoT := StateT InstInfo

namespace InstInfoT
variable {m} [Monad m]

/-- Return `InstInfo.rawInst` from the state -/
def getRawInst : InstInfoT m (BitVec 32) := do
  return (← get).rawInst

/-- Return `InstInfo.decodedInst?` from the state if it is `some _`,
or use `f` to compute the relevant expression if it is missing -/
def getDecodedInst (f : Unit → InstInfoT m Expr) : InstInfoT m Expr := do
  let info ← get
  match info.decodedInst? with
    | .value val => return val
    | .notYetComputed =>
        let val ← f ()
        set {info with decodedInst? := .value val}
        return val

/-- Return `InstInfo.instSemantics?` from the state if it is `some _`,
or use `f` to compute the relevant expressions if they are missing -/
def getInstSemantics (f : Unit → InstInfoT m (Expr × Expr × Expr)) :
    InstInfoT m (Expr × Expr × Expr) := do
  let info ← get
  match info.instSemantics? with
    | .value val => return val
    | .notYetComputed =>
        let val ← f ()
        set {info with instSemantics? := .value val}
        return val

end InstInfoT

def InstInfo.ofRawInst (rawInst : BitVec 32) : InstInfo :=
  { rawInst }

--------------------------------------------------------------------------------

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
        let rawInst ← reflectBitVecLiteral 32 (← instantiateMVars inst)
        let rawProgram :=
          let info := InstInfo.ofRawInst rawInst
          instructions.insert addr info

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

/-- A monad transformer with `ProgramInfo` state -/
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
def run (programName : Name) (k : ProgramInfoT m α)
    (persist : Bool := false) :
    m α :=
  ProgramInfoT.run' programName none persist k

/-- run a `ProgramInfoT m` by looking up, or generating new program info.
The passed expression is assumed to be the definition of the program.

If `persist` is set to true (the default), then the program info state after
executing `k` will be persistently cached in the environment
(see `persistToEnv`). -/
def runE (programName : Name) (expr : Expr) (k : ProgramInfoT m α)
    (persist : Bool := false)
     : m α :=
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

/-- Access the info for the instruction at a given address,
or throw an error if none is found -/
def getInstInfoAt (addr : BitVec 64) : ProgramInfoT m InstInfo := do
  let some x := (← StateT.get).getInstInfoAt? addr
    | let addr := addr.toHexWithoutLeadingZeroes
      throwError "No instruction found at address {addr}"
  return x

/-- Set the instruction info for a particular address -/
def setInstInfoAt (addr : BitVec 64) (info : InstInfo) :
    ProgramInfoT m Unit := do
  let pi ← StateT.get
  StateT.set {pi with instructions := pi.instructions.insert addr info}

/-- Run `k` with the instruction info for the given address as initial state,
and store the resulting state at that same address.
Returns the value produced by `k`. Throws an error if the address is invalid -/
def modifyInstInfoAt (addr : BitVec 64) (k : InstInfoT m α) :
    ProgramInfoT m α := do
  let info ← getInstInfoAt addr
  let ⟨val, info⟩ ← monadLift (StateT.run k info)
  setInstInfoAt addr info
  return val

/-! ### InstInfo Accessors -/

def getRawInstAt (addr : BitVec 64) : ProgramInfoT m (BitVec 32) := do
  return (← getInstInfoAt addr).rawInst

/-- if `decodedInst?` is `some _` for the instruction info at the given address,
return the cached value.
Otherwise, use `k` to compute the decoded instruction, then
cache and return that new value.
See `InstInfo.decodInst?` for the meaning of this field.

NOTE: the computed value is only cached in the `ProgramInfoT` monad state,
not yet in the environment. -/
def getDecodedInstAt (addr : BitVec 64) (k : InstInfo → ProgramInfoT m Expr) :
    ProgramInfoT m Expr := do
  let info ← getInstInfoAt addr
  match info.decodedInst? with
    | .value e => return e
    | .notYetComputed =>
      let decodedInst ← k info
      setInstInfoAt addr {info with decodedInst? := .value decodedInst}
      return decodedInst

/-- if `instSemantics?` is `some _` for the instruction info at the given address,
return the cached value.
Otherwise, use `k` to compute the decoded instruction, then
cache and return that new value.
See `InstInfo.instSemantics?` for the meaning of this field.

NOTE: the computed value is only cached in the `ProgramInfoT` monad state,
not yet in the environment. -/
def getInstSemanticsAt (addr : BitVec 64)
    (k : InstInfo → ProgramInfoT m (Expr × Expr × Expr)) :
    ProgramInfoT m (Expr × Expr × Expr) := do
  let info ← getInstInfoAt addr
  match info.instSemantics? with
    | .value e => return e
    | .notYetComputed =>
      let instSemantics ← k info
      setInstInfoAt addr {info with instSemantics? := .value instSemantics}
      return instSemantics


end ProgramInfoT
