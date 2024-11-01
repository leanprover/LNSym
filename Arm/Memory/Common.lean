/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

In this file, we define common datastructures for proof automation for separation conditions of memory.

References:
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/OmegaM.lean
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/Frontend.lean
-/
import Arm
import Arm.Memory.MemoryProofs
import Arm.BitVec
import Arm.Memory.Attr
import Arm.Memory.AddressNormalization
import Lean
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Conv.Basic
import Tactics.Simp
import Tactics.BvOmegaBench

open Lean Meta Elab Tactic

namespace Tactic.Memory

/-- a Proof of `e : α`, where `α` is a type such as `MemLegalProp`. -/
structure Proof (α : Type) (e : α) where
  /-- `h` is an expression of type `e`. -/
  h : Expr

/-- Get the prop `e` for which this is a proof of. -/
def Proof.proposition (_p : Proof α e → α) := e

def WithProof.e {α : Type} {e : α} (_p : Proof α e) : α := e

instance [ToMessageData α] : ToMessageData (Proof α e) where
  toMessageData proof := m! "{proof.h}: {e}"

structure MemSpanExpr where
  base : Expr
  n : Expr
deriving Inhabited

/-- info: Memory.Region.mk (a : BitVec 64) (n : Nat) : Memory.Region -/
#guard_msgs in #check Memory.Region.mk

def MemSpanExpr.toExpr (span : MemSpanExpr) : Expr :=
  mkAppN (Expr.const ``Memory.Region.mk []) #[span.base, span.n]

def MemSpanExpr.toTypeExpr  : Expr :=
    (Expr.const ``Memory.Region [])

instance : ToMessageData MemSpanExpr where
  toMessageData span := m! "[{span.base}..{span.n})"

/-- info: mem_legal' (a : BitVec 64) (n : Nat) : Prop -/
#guard_msgs in #check mem_legal'

/-- a term of the form `mem_legal' a` -/
structure MemLegalProp  where
  span : MemSpanExpr

/-- convert this back to an Expr -/
def MemLegalProp.toExpr (legal : MemLegalProp) : Expr :=
  mkAppN (Expr.const ``mem_legal' []) #[legal.span.base, legal.span.n]

instance : ToMessageData MemLegalProp where
  toMessageData e := m!"{e.span}.legal"

/-- Coerce a span into a `span.legal` hypothesis. -/
instance : Coe MemSpanExpr MemLegalProp where
  coe := MemLegalProp.mk


/-- info: mem_subset' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop -/
#guard_msgs in #check mem_subset'

/-- a proposition `mem_subset' a an b bn`. -/
structure MemSubsetProp where
  sa : MemSpanExpr
  sb : MemSpanExpr

instance : ToMessageData MemSubsetProp where
  toMessageData e := m!"{e.sa}⊆{e.sb}"

abbrev MemSubsetProof := Proof MemSubsetProp

def MemSubsetProof.mk {e : MemSubsetProp} (h : Expr) : MemSubsetProof e :=
  { h }

/-- info: mem_separate' (a : BitVec 64) (an : Nat) (b : BitVec 64) (bn : Nat) : Prop -/
#guard_msgs in #check mem_separate'

/-- A proposition `mem_separate' a an b bn`. -/
structure MemSeparateProp where
  sa : MemSpanExpr
  sb : MemSpanExpr

instance : ToMessageData MemSeparateProp where
  toMessageData e := m!"{e.sa}⟂{e.sb}"

abbrev MemSeparateProof := Proof MemSeparateProp

def MemSeparateProof.mk {e : MemSeparateProp} (h : Expr) : MemSeparateProof e :=
  { h }

abbrev MemLegalProof := Proof MemLegalProp

def MemLegalProof.mk {e : MemLegalProp} (h : Expr) : MemLegalProof e :=
  { h }


/-- info: Memory.Region.pairwiseSeparate (mems : List Memory.Region) : Prop -/
#guard_msgs in #check Memory.Region.pairwiseSeparate

/--
A proposition `Memory.Region.pairwiseSeparate [x1, x2, ..., xn]`.
-/
structure MemPairwiseSeparateProp where
  xs : Array MemSpanExpr

/-- info: List.nil.{u} {α : Type u} : List α -/
#guard_msgs in #check List.nil

/-- info: List.cons.{u} {α : Type u} (head : α) (tail : List α) : List α -/
#guard_msgs in #check List.cons

/-- Given `Memory.Region.pairwiseSeparate [x1, ..., xn]`,
get the expression corresponding `[x1, ..., xn]`. -/
def MemPairwiseSeparateProp.getMemSpanListExpr
    (e : MemPairwiseSeparateProp) : Expr := Id.run do
  let memoryRegionTy : Expr := mkConst ``Memory.Region
  let mut out := mkApp (mkConst  ``List.nil [0]) memoryRegionTy
  for i in [0:e.xs.size] do
    let x := e.xs[e.xs.size - i - 1]!
    out := mkAppN (mkConst ``List.cons [0]) #[memoryRegionTy, x.toExpr, out]
  return out

/-- Get the expression `Memory.Region.pairwiseSeparate [x1, ..., xn]` -/
def MemPairwiseSeparateProp.toExpr (e : MemPairwiseSeparateProp) : Expr :=
  mkApp (mkConst ``Memory.Region.pairwiseSeparate) e.getMemSpanListExpr

instance : ToMessageData MemPairwiseSeparateProp where
  toMessageData e := m!"pairwiseSeparate {e.xs.toList}"

abbrev MemPairwiseSeparateProof := Proof MemPairwiseSeparateProp

/-- info: Memory.read_bytes (n : Nat) (addr : BitVec 64) (m : Memory) : BitVec (n * 8) -/
#guard_msgs in #check Memory.read_bytes

/-- an occurrence of `Memory.read_bytes`. -/
structure ReadBytesExpr where
  span : MemSpanExpr
  mem : Expr

/-- match an expression `e` to `Memory.read_bytes`. -/
def ReadBytesExpr.ofExpr? (e : Expr) : Option (ReadBytesExpr) :=
  match_expr e with
  | Memory.read_bytes n addr m =>
    some { span := { base := addr, n := n }, mem := m }
  | _ => none

-- TODO: try to use `pp.deepTerms` to make the memory expressions more readable.
instance : ToMessageData ReadBytesExpr where
  toMessageData e := m!"{e.mem}[{e.span}]"

/--
info: Memory.write_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (m : Memory) : Memory
-/
#guard_msgs in #check Memory.write_bytes

structure WriteBytesExpr where
  span : MemSpanExpr
  val : Expr
  mem : Expr

instance : ToMessageData WriteBytesExpr where
  toMessageData e := m!"{e.mem}[{e.span} := {e.val}]"

def WriteBytesExpr.ofExpr? (e : Expr) : Option WriteBytesExpr :=
  match_expr e with
  | Memory.write_bytes n addr val m =>
    some { span := { base := addr, n := n }, val := val, mem := m }
  | _ => none


/--
A proof of the form `h : val = Mem.read_bytes ...`.
Note that we expect the canonical ordering of `val` on the left hand side.
If `val` was on the right hand, we build `h` wih an `Eq.symm` to
enforce this canonical form.

TODO: there must be a better way to handle this?
 -/
structure ReadBytesEqProof  where
  val : Expr
  read : ReadBytesExpr
  h : Expr

instance : ToMessageData ReadBytesEqProof where
  toMessageData proof := m!"{proof.h} : {proof.val} = {proof.h}"

/--
we can have some kind of funny situation where both LHS and RHS are ReadBytes.
For example, `mem1.read base1 n = mem2.read base2 n`.
In such a scenario, we should record both reads.
-/
def ReadBytesEqProof.ofExpr? (eval : Expr) (etype : Expr) : MetaM (Array ReadBytesEqProof) := do
  let mut out := #[]
  if let .some ⟨_ty, lhs, rhs⟩ := etype.eq? then do
    let lhs := lhs
    let rhs := rhs
    if let .some read := ReadBytesExpr.ofExpr? lhs then
      out := out.push { val := rhs, read := read, h := eval }

    if let .some read := ReadBytesExpr.ofExpr? rhs then
      out:= out.push { val := lhs, read := read, h := ← mkEqSymm eval }
  return out

inductive Hypothesis
| separate (proof : MemSeparateProof e)
| subset (proof : MemSubsetProof e)
| legal (proof : MemLegalProof e)
| pairwiseSeparate (proof : MemPairwiseSeparateProof e)
| read_eq (proof : ReadBytesEqProof)

def Hypothesis.isPairwiseSeparate : Hypothesis → Bool
| .pairwiseSeparate _ => true
| _ => false

def Hypothesis.proof : Hypothesis → Expr
| .pairwiseSeparate proof  => proof.h
| .separate proof => proof.h
| .subset proof => proof.h
| .legal proof => proof.h
| .read_eq proof => proof.h

instance : ToMessageData Hypothesis where
  toMessageData
  | .subset proof => toMessageData proof
  | .separate proof => toMessageData proof
  | .legal proof => toMessageData proof
  | .read_eq proof => toMessageData proof
  | .pairwiseSeparate proof => toMessageData proof

/-- create a trace node in trace class (i.e. `set_option traceClass true`),
with header `header`, whose default collapsed state is `collapsed`. -/
def TacticM.withTraceNode'
    [Monad m]
    [MonadTrace m]
    [MonadLiftT IO m]
    [MonadRef m]
    [AddMessageContext m]
    [MonadOptions m]
    [always : MonadAlwaysExcept ε m]
    [MonadLiftT BaseIO m]
    (header : MessageData) (k : m α)
    (collapsed : Bool := false)
    (traceClass : Name := `simp_mem.info) : m α :=
  Lean.withTraceNode traceClass (fun _ => return header) k (collapsed := collapsed)

/-- Create a trace note that folds `header` with `(NOTE: can be large)`,
and prints `msg` under such a trace node. Collapsed by default.
-/
def TacticM.traceLargeMsg
    [Monad m]
    [MonadTrace m]
    [MonadLiftT IO m]
    [MonadRef m]
    [AddMessageContext m]
    [MonadOptions m]
    [always : MonadAlwaysExcept ε m]
    [MonadLiftT BaseIO m]
    (header : MessageData)
    (msg : MessageData) : m Unit := do
    withTraceNode' m!"{header} (NOTE: can be large)" (collapsed := true) do
      trace[simp_mem.info] msg


/-- TacticM's omega invoker -/
def omega (g : MVarId) (hyps : Array Expr) (bvToNatSimpCtx : Simp.Context) (bvToNatSimprocs : Array Simp.Simprocs) : MetaM Unit := do
    BvOmegaBench.run g hyps bvToNatSimpCtx bvToNatSimprocs

/-
Introduce a new definition into the local context, simplify it using `simp`,
and return the FVarId of the new definition in the goal.
-/
def simpAndIntroDef (name : String) (hdefVal : Expr) : TacticM FVarId  := do
  withMainContext do
    let name ← mkFreshUserName <| .mkSimple name
    let goal ← getMainGoal
    let hdefTy ← inferType hdefVal

    /- Simp to gain some more juice out of the defn.. -/
    let mut simpTheorems : Array SimpTheorems := #[]
    for a in #[`minimal_theory, `bitvec_rules, `bv_toNat] do
      let some ext ← (getSimpExtension? a)
        | throwError m!"[simp_mem] Internal error: simp attribute {a} not found!"
      simpTheorems := simpTheorems.push (← ext.getTheorems)

    -- unfold `state_value.
    simpTheorems := simpTheorems.push <| ← ({} : SimpTheorems).addDeclToUnfold `state_value
    let simpCtx : Simp.Context := {
      simpTheorems,
      config := { decide := true, failIfUnchanged := false },
      congrTheorems := (← Meta.getSimpCongrTheorems)
    }
    let (simpResult, _stats) ← simp hdefTy simpCtx (simprocs := #[])
    let hdefVal ← simpResult.mkCast hdefVal
    let hdefTy ← inferType hdefVal

    let goal ← goal.assert name hdefTy hdefVal
    let (fvar, goal) ← goal.intro1P
    replaceMainGoal [goal]
    return fvar

def simpAndIntroDef' (g : MVarId) (name : String) (hdefVal : Expr) : MetaM (FVarId × MVarId)  := do
  g.withContext do
    let name ← mkFreshUserName <| .mkSimple name
    let hdefTy ← inferType hdefVal

    /- Simp to gain some more juice out of the defn.. -/
    let mut simpTheorems : Array SimpTheorems := #[]
    for a in #[`minimal_theory, `bitvec_rules, `bv_toNat] do
      let some ext ← (getSimpExtension? a)
        | throwError m!"[simp_mem] Internal error: simp attribute {a} not found!"
      simpTheorems := simpTheorems.push (← ext.getTheorems)

    -- unfold `state_value.
    simpTheorems := simpTheorems.push <| ← ({} : SimpTheorems).addDeclToUnfold `state_value
    let simpCtx : Simp.Context := {
      simpTheorems,
      config := { decide := true, failIfUnchanged := false },
      congrTheorems := (← Meta.getSimpCongrTheorems)
    }
    let (simpResult, _stats) ← simp hdefTy simpCtx (simprocs := #[])
    let hdefVal ← simpResult.mkCast hdefVal
    let hdefTy ← inferType hdefVal

    let g ← g.assert name hdefTy hdefVal
    let (fvar, g) ← g.intro1P
    return (fvar, g)

section Hypotheses

/--
info: mem_separate'.ha {a : BitVec 64} {an : Nat} {b : BitVec 64} {bn : Nat} (self : mem_separate' a an b bn) :
  mem_legal' a an
-/
#guard_msgs in #check mem_separate'.ha

def MemSeparateProof.mem_separate'_ha (self : MemSeparateProof sep) :
    MemLegalProof sep.sa :=
  let h := mkAppN (Expr.const ``mem_separate'.ha []) #[sep.sa.base, sep.sa.n, sep.sb.base, sep.sb.n, self.h]
  MemLegalProof.mk h

/--
info: mem_separate'.hb {a : BitVec 64} {an : Nat} {b : BitVec 64} {bn : Nat} (self : mem_separate' a an b bn) :
  mem_legal' b bn
-/
#guard_msgs in #check mem_separate'.hb

def MemSeparateProof.mem_separate'_hb (self : MemSeparateProof sep) :
    MemLegalProof sep.sb :=
  let h := mkAppN (Expr.const ``mem_separate'.hb []) #[sep.sa.base, sep.sa.n, sep.sb.base, sep.sb.n, self.h]
  MemLegalProof.mk h

/--
info: mem_subset'.ha {a : BitVec 64} {an : Nat} {b : BitVec 64} {bn : Nat} (self : mem_subset' a an b bn) : mem_legal' a an
-/
#guard_msgs in #check mem_subset'.ha

def MemSubsetProof.mem_subset'_ha (self : MemSubsetProof sub) :
    MemLegalProof sub.sa :=
  let h := mkAppN (Expr.const ``mem_subset'.ha [])
    #[sub.sa.base, sub.sa.n, sub.sb.base, sub.sb.n, self.h]
  MemLegalProof.mk h

/--
info: mem_subset'.hb {a : BitVec 64} {an : Nat} {b : BitVec 64} {bn : Nat} (self : mem_subset' a an b bn) : mem_legal' b bn
-/
#guard_msgs in #check mem_subset'.hb

def MemSubsetProof.mem_subset'_hb (self : MemSubsetProof sub) :
    MemLegalProof sub.sb :=
  let h := mkAppN (Expr.const ``mem_subset'.hb [])
      #[sub.sa.base, sub.sa.n, sub.sb.base, sub.sb.n, self.h]
  MemLegalProof.mk h

/-- match an expression `e` to a `mem_legal'`. -/
def MemLegalProp.ofExpr? (e : Expr) : Option (MemLegalProp) :=
  match_expr e with
  | mem_legal' a n => .some { span := { base := a, n := n } }
  | _ => none

/-- match an expression `e` to a `mem_subset'`. -/
def MemSubsetProp.ofExpr? (e : Expr) : Option (MemSubsetProp) :=
  match_expr e with
  | mem_subset' a na b nb =>
    let sa : MemSpanExpr := { base := a, n := na }
    let sb : MemSpanExpr := { base := b, n := nb }
    .some { sa, sb }
  | _ => none

/-- match an expression `e` to a `mem_separate'`. -/
def MemSeparateProp.ofExpr? (e : Expr) : Option MemSeparateProp :=
  match_expr e with
  | mem_separate' a na b nb =>
    let sa : MemSpanExpr := ⟨a, na⟩
    let sb : MemSpanExpr := ⟨b, nb⟩
    .some { sa, sb }
  | _ => none

/-- info: Prod.mk.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) : α × β -/
#guard_msgs in #check Prod.mk

/-- info: List.cons.{u} {α : Type u} (head : α) (tail : List α) : List α -/
#guard_msgs in #check List.cons

/-- info: List.nil.{u} {α : Type u} : List α -/
#guard_msgs in #check List.nil

/-- match an expression `e` to a `Memory.Region.pairwiseSeparate`. -/
partial def MemPairwiseSeparateProof.ofExpr? (e : Expr) : Option MemPairwiseSeparateProp :=
  match_expr e with
  | Memory.Region.pairwiseSeparate xs => do
      let .some xs := go xs #[] | none
      some { xs := xs }
  | _ => none
  where
    go (e : Expr) (xs : Array MemSpanExpr) : Option (Array MemSpanExpr) :=
      match_expr e with
      | List.cons _α ex exs =>
        match_expr ex with
        | Prod.mk _ta _tb a n =>
          let x : MemSpanExpr := ⟨a, n⟩
          go exs (xs.push x)
        | _ => none
      | List.nil _α => some xs
      | _ => none


/-- Match an expression `h` to see if it's a useful hypothesis. -/
def hypothesisOfExpr (h : Expr) (hyps : Array Hypothesis) : MetaM (Array Hypothesis) := do
  let ht ← inferType h
  trace[simp_mem.info] "{processingEmoji} Processing '{h}' : '{ht}'"
  if let .some sep := MemSeparateProp.ofExpr? ht then
    let proof : MemSeparateProof sep := ⟨h⟩
    let hyps := hyps.push (.separate proof)
    let hyps := hyps.push (.legal proof.mem_separate'_ha)
    let hyps := hyps.push (.legal proof.mem_separate'_hb)
    return hyps
  else if let .some sub := MemSubsetProp.ofExpr? ht then
    let proof : MemSubsetProof sub := ⟨h⟩
    let hyps := hyps.push (.subset proof)
    let hyps := hyps.push (.legal proof.mem_subset'_ha)
    let hyps := hyps.push (.legal proof.mem_subset'_hb)
    return hyps
  else if let .some legal := MemLegalProp.ofExpr? ht then
    let proof : MemLegalProof legal := ⟨h⟩
    let hyps := hyps.push (.legal proof)
    return hyps
  else if let .some pairwiseSep := MemPairwiseSeparateProof.ofExpr? ht then
    let proof : MemPairwiseSeparateProof pairwiseSep := ⟨h⟩
    let hyps := hyps.push (.pairwiseSeparate proof)
    return hyps
  else
    let mut hyps := hyps
    for eqProof in ← ReadBytesEqProof.ofExpr? h ht do
      let proof : Hypothesis := .read_eq eqProof
      hyps := hyps.push proof
    return hyps

/--
info: mem_legal'.omega_def {a : BitVec 64} {n : Nat} (h : mem_legal' a n) : a.toNat + n ≤ 2 ^ 64
-/
#guard_msgs in #check mem_legal'.omega_def


/-- Build a term corresponding to `mem_legal'.omega_def`. -/
def MemLegalProof.omega_def (h : MemLegalProof e) : Expr :=
  mkAppN (Expr.const ``mem_legal'.omega_def []) #[e.span.base, e.span.n, h.h]

/-- Add the omega fact from `mem_legal'.def`. -/
def MemLegalProof.addOmegaFacts (h : MemLegalProof e) (g : MVarId) (args : Array Expr) :
    MetaM (Array Expr × MVarId) := do
  let (fvar, g) ← simpAndIntroDef' g "hmemLegal_omega" h.omega_def
  trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
  return (args.push (Expr.fvar fvar), g)

/--
info: mem_subset'.omega_def {a : BitVec 64} {an : Nat} {b : BitVec 64} {bn : Nat} (h : mem_subset' a an b bn) :
  a.toNat + an ≤ 2 ^ 64 ∧ b.toNat + bn ≤ 2 ^ 64 ∧ b.toNat ≤ a.toNat ∧ a.toNat + an ≤ b.toNat + bn
-/
#guard_msgs in #check mem_subset'.omega_def

/--
Build a term corresponding to `mem_subset'.omega_def` which has facts written
in a style that is exploitable by omega.
-/
def MemSubsetProof.omega_def (h : MemSubsetProof e) : Expr :=
  mkAppN (Expr.const ``mem_subset'.omega_def [])
    #[e.sa.base, e.sa.n, e.sb.base, e.sb.n, h.h]

/-- Add the omega fact from `mem_legal'.omega_def` into the main goal. -/
def MemSubsetProof.addOmegaFacts (h : MemSubsetProof e) (g : MVarId) (args : Array Expr) :
    MetaM (Array Expr × MVarId) := do
  let (fvar, g) ← simpAndIntroDef' g "hmemSubset_omega" h.omega_def
  trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
  return (args.push (Expr.fvar fvar), g)

/--
Build a term corresponding to `mem_separate'.omega_def` which has facts written
in a style that is exploitable by omega.
-/
def MemSeparateProof.omega_def (h : MemSeparateProof e) : Expr :=
  mkAppN (Expr.const ``mem_separate'.omega_def [])
    #[e.sa.base, e.sa.n, e.sb.base, e.sb.n, h.h]

/-- Add the omega fact from `mem_legal'.omega_def`. -/
def MemSeparateProof.addOmegaFacts (h : MemSeparateProof e) (g : MVarId) (args : Array Expr) :
    MetaM (Array Expr × MVarId) := do
  let (fvar, g) ← simpAndIntroDef' g "hmemSeparate_omega" h.omega_def
  trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
  return (args.push (Expr.fvar fvar), g)



/-- info: Ne.{u} {α : Sort u} (a b : α) : Prop -/
#guard_msgs in #check Ne

/-- info: List.get?.{u} {α : Type u} (as : List α) (i : Nat) : Option α -/
#guard_msgs in #check List.get?

/-- Make the expression `mems.get? i = some a`. -/
def mkListGetEqSomeTy (mems : MemPairwiseSeparateProp) (i : Nat) (a : MemSpanExpr) : TacticM Expr := do
  let lhs ← mkAppOptM ``List.get? #[.none, mems.getMemSpanListExpr, mkNatLit i]
  let rhs ← mkSome MemSpanExpr.toTypeExpr a.toExpr
  mkEq lhs rhs

/--
info: Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem {mems : List Memory.Region}
  (h : Memory.Region.pairwiseSeparate mems) (i j : Nat) (hij : i ≠ j) (a b : Memory.Region) (ha : mems.get? i = some a)
  (hb : mems.get? j = some b) : mem_separate' a.fst a.snd b.fst b.snd
-/
#guard_msgs in #check Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem

/-- make `Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem i j (by decide) a b rfl rfl`. -/
def MemPairwiseSeparateProof.mem_separate'_of_pairwiseSeparate_of_mem_of_mem
    (self : MemPairwiseSeparateProof mems) (i j : Nat) (a b : MemSpanExpr)  :
    MetaM <| MemSeparateProof ⟨a, b⟩ := do
  let iexpr := mkNatLit i
  let jexpr := mkNatLit j
    -- i ≠ j
  let hijTy := mkAppN (mkConst ``Ne [1]) #[(mkConst ``Nat), mkNatLit i, mkNatLit j]
  -- mems.get? i = some a
  let hijVal ← mkDecideProof hijTy
  let haVal ← mkEqRefl <| ← mkSome MemSpanExpr.toTypeExpr a.toExpr
  let hbVal ← mkEqRefl <| ← mkSome MemSpanExpr.toTypeExpr b.toExpr
  let h := mkAppN (Expr.const ``Memory.Region.separate'_of_pairwiseSeprate_of_mem_of_mem [])
    #[mems.getMemSpanListExpr,
      self.h,
      iexpr,
      jexpr,
      hijVal,
      a.toExpr,
      b.toExpr,
      haVal,
      hbVal]
  return ⟨h⟩
/--
Currently, if the list is syntacticaly of the form [x1, ..., xn],
 we create hypotheses of the form `mem_separate' xi xj` for all i, j..
This can be generalized to pairwise separation given hypotheses x ∈ xs, x' ∈ xs.
-/
def MemPairwiseSeparateProof.addOmegaFacts (h : MemPairwiseSeparateProof e) (g : MVarId) (args : Array Expr) :
    MetaM (Array Expr × MVarId) := do
  -- We need to loop over i, j where i < j and extract hypotheses.
  -- We need to find the length of the list, and return an `Array MemRegion`.
  let mut args := args
  let mut g := g
  for i in [0:e.xs.size] do
    for j in [i+1:e.xs.size] do
      let a := e.xs[i]!
      let b := e.xs[j]!
      (args, g) ← TacticM.withTraceNode' m!"Exploiting ({i}, {j}) : {a} ⟂ {b}" do
        let proof ← h.mem_separate'_of_pairwiseSeparate_of_mem_of_mem i j a b
        TacticM.traceLargeMsg m!"added {← inferType proof.h}" m!"{proof.h}"
        proof.addOmegaFacts g args
  return (args, g)
/--
Given a hypothesis, add declarations that would be useful for omega-blasting
-/
def Hypothesis.addOmegaFactsOfHyp (g : MVarId) (h : Hypothesis) (args : Array Expr) : 
    MetaM (Array Expr × MVarId) :=
  match h with
  | Hypothesis.legal h => h.addOmegaFacts g args
  | Hypothesis.subset h => h.addOmegaFacts g args
  | Hypothesis.separate h => h.addOmegaFacts g args
  | Hypothesis.pairwiseSeparate h => h.addOmegaFacts g args
  | Hypothesis.read_eq _h => return (args, g) -- read has no extra `omega` facts.

/--
Accumulate all omega defs in `args`.
-/
def Hypothesis.addOmegaFactsOfHyps (g : MVarId) (hs : List Hypothesis) (args : Array Expr)
    : MetaM (Array Expr × MVarId) := do
  TacticM.withTraceNode' m!"Adding omega facts from hypotheses" do
    let mut args := args
    let mut g := g
    for h in hs do
      (args, g) ← h.addOmegaFactsOfHyp g args
    return (args, g)

end Hypotheses



section Simplify

structure SimplifyResult where
  eNew : Expr
  eqProof : Expr
deriving Inhabited

/-- Rewrite expression `e` with rewrite `rw` -/
def rewriteWithEquality (rw : Expr) (e : Expr) (msg : MessageData) : TacticM SimplifyResult := do
  TacticM.withTraceNode' msg do
    withMainContext do
      -- TacticM.traceLargeMsg m!"rewrite" m!"{← inferType rw}"
      let goal ← getMainGoal
      let result ← goal.rewrite e rw
      -- let mvarId' ← (← getMainGoal).replaceTargetEq result.eNew result.eqProof
      trace[simp_mem.info] "{checkEmoji} rewritten goal {e}"
      check result.eNew
      check result.eqProof
      return { eNew := result.eNew, eqProof := result.eqProof }

/--
info: Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat}
  {mem : Memory} (hsep : mem_separate' x xn y yn) (val : BitVec (yn * 8)) :
  Memory.read_bytes xn x (Memory.write_bytes yn y val mem) = Memory.read_bytes xn x mem
-/
#guard_msgs in #check Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'

/-- given that `e` is a read of the write, perform a rewrite,
using `Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'`. -/
def MemSeparateProof.rewriteReadOfSeparatedWrite
    (er : ReadBytesExpr) (ew : WriteBytesExpr)
    (separate : MemSeparateProof { sa := er.span, sb := ew.span })
    (e : Expr) : TacticM SimplifyResult := do
  let call :=
    mkAppN (Expr.const ``Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' [])
      #[er.span.base, er.span.n,
        ew.span.base, ew.span.n,
        ew.mem,
        separate.h,
        ew.val]
  rewriteWithEquality call e m!"rewriting read({er})⟂write({ew})"

/--
info: Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset' {bn : Nat} {b : BitVec 64} {val : BitVec (bn * 8)}
  {a : BitVec 64} {an : Nat} {mem : Memory} (hread : Memory.read_bytes bn b mem = val)
  (hsubset : mem_subset' a an b bn) : Memory.read_bytes an a mem = val.extractLsBytes (a.toNat - b.toNat) an
-/
#guard_msgs in #check Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'

def MemSubsetProof.rewriteReadOfSubsetRead
    (er : ReadBytesExpr)
    (hread : ReadBytesEqProof)
    (hsubset : MemSubsetProof { sa := er.span, sb := hread.read.span })
    (e : Expr)
  : TacticM SimplifyResult := do
  let call := mkAppN (Expr.const ``Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset' [])
    #[hread.read.span.n, hread.read.span.base,
      hread.val,
      er.span.base, er.span.n,
      er.mem,
      hread.h,
      hsubset.h]
  rewriteWithEquality call e m!"rewriting read({er})⊆read({hread.read})"

/--
info: Memory.read_bytes_write_bytes_eq_of_mem_subset' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat} {mem : Memory}
  (hsep : mem_subset' x xn y yn) (val : BitVec (yn * 8)) :
  Memory.read_bytes xn x (Memory.write_bytes yn y val mem) = val.extractLsBytes (x.toNat - y.toNat) xn
-/
#guard_msgs in #check Memory.read_bytes_write_bytes_eq_of_mem_subset'

def MemSubsetProof.rewriteReadOfSubsetWrite
    (er : ReadBytesExpr) (ew : WriteBytesExpr)
    (hsubset : MemSubsetProof { sa := er.span, sb := ew.span }) 
    (e : Expr) :
    TacticM SimplifyResult := do
  let call := mkAppN (Expr.const ``Memory.read_bytes_write_bytes_eq_of_mem_subset' [])
    #[er.span.base, er.span.n,
      ew.span.base, ew.span.n,
      ew.mem,
      hsubset.h,
      ew.val]
  rewriteWithEquality call e m!"rewriting read({er})⊆write({ew})"

end Simplify

section ReductionToOmega

/--
Given a `a : α` (for example, `(a = legal) : (α = mem_legal)`),
produce an `Expr` whose type is `<omega fact> → α`.
For example, `mem_legal.of_omega` is a function of type:
  `(h : a.toNat + n ≤ 2 ^ 64) → mem_legal a n`.
-/
class OmegaReducible (α : Type) where
  reduceToOmega : α → Expr

/--
info: mem_legal'.of_omega {n : Nat} {a : BitVec 64} (h : a.toNat + n ≤ 2 ^ 64) : mem_legal' a n
-/
#guard_msgs in #check mem_legal'.of_omega

instance : OmegaReducible MemLegalProp where
  reduceToOmega legal :=
    let a := legal.span.base
    let n := legal.span.n
    mkAppN (Expr.const ``mem_legal'.of_omega []) #[n, a]

/--
info: mem_subset'.of_omega {an bn : Nat} {a b : BitVec 64}
  (h : a.toNat + an ≤ 2 ^ 64 ∧ b.toNat + bn ≤ 2 ^ 64 ∧ b.toNat ≤ a.toNat ∧ a.toNat + an ≤ b.toNat + bn) :
  mem_subset' a an b bn
-/
#guard_msgs in #check mem_subset'.of_omega

instance : OmegaReducible MemSubsetProp where
  reduceToOmega subset :=
  let a := subset.sa.base
  let an := subset.sa.n
  let b := subset.sb.base
  let bn := subset.sb.n
  mkAppN (Expr.const ``mem_subset'.of_omega []) #[an, bn, a, b]

/--
info: mem_subset'.of_omega {an bn : Nat} {a b : BitVec 64}
  (h : a.toNat + an ≤ 2 ^ 64 ∧ b.toNat + bn ≤ 2 ^ 64 ∧ b.toNat ≤ a.toNat ∧ a.toNat + an ≤ b.toNat + bn) :
  mem_subset' a an b bn
-/
#guard_msgs in #check mem_subset'.of_omega

instance : OmegaReducible MemSeparateProp where
  reduceToOmega separate :=
    let a := separate.sa.base
    let an := separate.sa.n
    let b := separate.sb.base
    let bn := separate.sb.n
    mkAppN (Expr.const ``mem_separate'.of_omega []) #[an, bn, a, b]


/-- For a goal that is reducible to `Omega`, make a new goal to be presented to the user -/
def mkProofGoalForOmega {α : Type} [ToMessageData α] [OmegaReducible α] (e : α) : MetaM (Proof α e × MVarId) := do
  let proofFromOmegaVal := (OmegaReducible.reduceToOmega e)
  -- (h : a.toNat + n ≤ 2 ^ 64) → mem_legal' a n
  let proofFromOmegaTy ← inferType (OmegaReducible.reduceToOmega e)
  -- trace[simp_mem.info] "partially applied: '{proofFromOmegaVal} : {proofFromOmegaTy}'"
  let omegaObligationTy ← do -- (h : a.toNat + n ≤ 2 ^ 64)
    match proofFromOmegaTy with
    | Expr.forallE _argName argTy _body _binderInfo => pure argTy
    | _ => throwError "expected '{proofFromOmegaTy}' to a ∀"
  trace[simp_mem.info] "omega obligation '{omegaObligationTy}'"
  let omegaObligationVal ← mkFreshExprMVar (type? := omegaObligationTy)
  let factProof := mkAppN proofFromOmegaVal #[omegaObligationVal]
  let g := omegaObligationVal.mvarId!
  return (Proof.mk (← instantiateMVars factProof), g)

/--
`OmegaReducible` is a value whose type is `omegaFact → desiredFact`.
An example is `mem_lega'.of_omega n a`, which has type:
  `(h : a.toNat + n ≤ 2 ^ 64) → mem_legal' a n`.

@bollu: TODO: this can be generalized further, what we actually need is
  a way to convert `e : α` into the `omegaToDesiredFactFnVal`.
-/
def proveWithOmega?  {α : Type} [ToMessageData α] [OmegaReducible α] (e : α)
    (extraOmegaAssumptions : Array Expr)
    (bvToNatSimpCtx : Simp.Context) (bvToNatSimprocs : Array Simp.Simprocs)
    (hyps : Array Memory.Hypothesis) : MetaM (Option (Proof α e)) := do
  -- TODO: refactor to use mkProofGoalForOmega
  let proofFromOmegaVal := (OmegaReducible.reduceToOmega e)
  -- (h : a.toNat + n ≤ 2 ^ 64) → mem_legal' a n
  let proofFromOmegaTy ← inferType (OmegaReducible.reduceToOmega e)
  -- trace[simp_mem.info] "partially applied: '{proofFromOmegaVal} : {proofFromOmegaTy}'"
  let omegaObligationTy ← do -- (h : a.toNat + n ≤ 2 ^ 64)
    match proofFromOmegaTy with
    | Expr.forallE _argName argTy _body _binderInfo => pure argTy
    | _ => throwError "expected '{proofFromOmegaTy}' to a ∀"
  trace[simp_mem.info] "omega obligation '{omegaObligationTy}'"
  let omegaObligationVal ← mkFreshExprMVar (type? := omegaObligationTy)
  let factProof := mkAppN proofFromOmegaVal #[omegaObligationVal]
  let g := omegaObligationVal.mvarId!
  g.withContext do
  try
    let (omegaAssumptions, g) ← Hypothesis.addOmegaFactsOfHyps g hyps.toList #[]
    trace[simp_mem.info] m!"Executing `omega` to close {e}"
    omega g (omegaAssumptions ++ extraOmegaAssumptions) bvToNatSimpCtx bvToNatSimprocs
    trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
    return (.some <| Proof.mk (← instantiateMVars factProof))
  catch e =>
    trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"
    return none
  end ReductionToOmega


/-- Collect nondependent hypotheses that are propositions. -/
def _root_.Lean.MVarId.getNondepPropExprs (g : MVarId) : MetaM (Array Expr) := do
  return ((← g.getNondepPropHyps).map Expr.fvar)




end Tactic.Memory
