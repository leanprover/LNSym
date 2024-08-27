/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

In this file, we define proof automation for separation conditions of memory.

References:
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/OmegaM.lean
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/Frontend.lean
-/
import Arm
import Arm.Memory.MemoryProofs
import Arm.BitVec
import Arm.Memory.Attr
import Lean
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Conv.Basic

open Lean Meta Elab Tactic


/-! ## Memory Separation Automation

##### A Note on Notation

- `[a..an)`: a range of memory starting with base address `a` of length `an`.
  aka `mem_legal' a an`.
- `[a..an) ⟂ [b..bn)`: `mem_disjoint' a an b bn`.
- `[a..an] ⊆ [b..bn)`: `mem_subset' a an b bn`

##### Tactic Loop

The core tactic tries to simplify expressions of the form:
`mem.write_bytes [b..bn) val |>. read_bytes [a..an)`
by case splitting:

1. If `[a..an) ⟂ [b..bn)`, the write does not alias the read,
  and can be replaced with ` mem.read_bytes [a..an) `
2. If `[a..an] ⊆ [b..bn)`, the write aliases the read, and can be replaced with
  `val.extractLsBs adjust([a..an), [b..bn))`. Here, `adjust` is a function that
  adjusts the read indices `[a..an)` with respect to the write indices `[b..bn)`,
  to convert a read from `mem` into a read from `val`.

The tactic shall be implemented as follows:
1. Search the goal state for `mem.write_bytes [b..bn) val |>.read_bytes [a..an)`.
2. Try to prove that either `[a..an) ⟂ [b..bn)`, or `[a..an) ⊆ [b..bn)`.
    2a. First search the local context for assumptions of this type.
    2b. Try to deduce `[a..an) ⟂ [b..bn)` from the fact that
        subsets of disjoint sets are disjoint.
        So try to find `[a'..an')`, `[b'...bn')` such that:
          (i) `[a..an) ⊆ [a'..an')`.
          (ii) `[b..bn) ⊆ [b'..bn')`.
          (iii) and `[a'..an') ⟂ [b'...bn')`.
    2b. Try to deduce `[a..an) ⊆ [b..bn)` from transitivity of subset.
        So try to find `[c..cn)` such that:
        (i) `[a..an) ⊆ [c..cn)`
        (ii) `[c..cn) ⊆ [b..bn)`
    2c. If this also fails, then reduce all hypotheses to
        linear integer arithmetic, and try to invoke `omega` to prove either
        `[a..an) ⟂ [b..bn)` or `[a..an) ⊆ [b..bn)`.
3. Given a proof of either `[a..an) ⟂ [b..bn)` or `[a..an) ⊆ [b..bn)`,
  simplify using the appropriate lemma from `Mem/Separate.lean`.
4. If we manage to prove *both* `[a..an) ⟂ [b..bn)` *and* `[a..an) ⊆ [b..bn)`,
   declare victory as this is a contradiction. This may look useless,
   but feels like it maybe useful to prove certain memory states as impossible.

##### Usability

- If no mem separate/subset assumptions are present,
  then throw an error to tell the user that we expect them to
  specify such assumptions for all memory regions of interest.
  LNSym doesn't support automated verification of programs that
  do dynamic memory allocation.

-  If any non-primed separate/subset assumptions are detected,
  error out to tell the user that no automation is supported in this case.

##### Future Work

- Add support for disjoint constraints amongst $n$ memory regions.
  This will perform proof search for `List.pairwise ⟂ mems`.
- Create a new concept, `MemRegion`, which we currently call `MemSpan`.
-/

section BvOmega

-- |TODO: Upstream BitVec.le_def unfolding to bv_omega.
macro "bv_omega'" : tactic =>
  `(tactic| (try simp only [bv_toNat, mem_legal'] at * <;> try rw [BitVec.le_def]) <;> bv_omega)

end BvOmega

namespace SeparateAutomation

structure SimpMemConfig where
  /-- number of times rewrites must be performed. -/
  rewriteFuel : Nat := 1000


/-- Context for the `SimpMemM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `simp_mem`. -/
  cfg : SimpMemConfig

def Context.init (cfg : SimpMemConfig) : Context where
  cfg := cfg

/-- a Proof of `e : α`, where `α` is a type such as `MemLegalProp`. -/
structure Proof (α : Type) (e : α) where
  /-- `h` is an expression of type `e`. -/
  h : Expr

def WithProof.e {α : Type} {e : α} (_p : Proof α e) : α := e

instance [ToMessageData α] : ToMessageData (Proof α e) where
  toMessageData proof := m! "{proof.h}: {e}"

structure MemRegionExpr where
  base : Expr
  n : Expr

/-- info: Memory.Region.mk (base : BitVec 64) (len : Nat) : Memory.Region -/
#guard_msgs in #check Memory.Region.mk

def MemRegionExpr.toExpr (e : MemRegionExpr) : Expr :=
  mkAppN (Expr.const ``Memory.Region.mk []) #[e.base, e.n]

instance : ToMessageData MemRegionExpr where
  toMessageData region := m! "[{region.base}..{region.n})"

/-- info: Memory.Region.legal (b : Memory.Region) : Prop -/
#guard_msgs in #check Memory.Region.legal

/-- a term of the form `mem_legal' a` -/
structure MemLegalProp  where
  region : MemRegionExpr

/-- convert this back to an Expr -/
def MemLegalProp.toExpr (legal : MemLegalProp) : Expr :=
  mkAppN (Expr.const ``Memory.Region.legal []) #[legal.region.toExpr]

instance : ToMessageData MemLegalProp where
  toMessageData e := m!"{e.region}.legal"

/-- Coerce a span into a `span.legal` hypothesis. -/
instance : Coe MemRegionExpr MemLegalProp where
  coe := MemLegalProp.mk


/-- info: Memory.Region.Subset (a b : Memory.Region) : Prop -/
#guard_msgs in #check Memory.Region.Subset

/-- a proposition `Memory.Region.Subset sa sb`. -/
structure MemSubsetProp where
  sa : MemRegionExpr
  sb : MemRegionExpr

instance : ToMessageData MemSubsetProp where
  toMessageData e := m!"{e.sa}⊆{e.sb}"

abbrev MemSubsetProof := Proof MemSubsetProp

def MemSubsetProof.mk {e : MemSubsetProp} (h : Expr) : MemSubsetProof e :=
  { h }

/-- info: Memory.Region.Separate (a b : Memory.Region) : Prop -/
#guard_msgs in #check Memory.Region.Separate

/-- A proposition `Memory.Region.Separate a an b bn`. -/
structure MemSeparateProp where
  sa : MemRegionExpr
  sb : MemRegionExpr

instance : ToMessageData MemSeparateProp where
  toMessageData e := m!"{e.sa}⟂{e.sb}"

abbrev MemSeparateProof := Proof MemSeparateProp

def MemSeparateProof.mk {e : MemSeparateProp} (h : Expr) : MemSeparateProof e :=
  { h }

abbrev MemLegalProof := Proof MemLegalProp

def MemLegalProof.mk {e : MemLegalProp} (h : Expr) : MemLegalProof e :=
  { h }

/-- info: Memory.read_bytes (n : Nat) (addr : BitVec 64) (m : Memory) : BitVec (n * 8) -/
#guard_msgs in #check Memory.read_bytes

/-- an occurrence of `Memory.read_bytes`. -/
structure ReadBytesExpr where
  span : MemRegionExpr
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
  span : MemRegionExpr
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
def ReadBytesEqProof.ofExpr? (eval : Expr) (etype : Expr) :  Array ReadBytesEqProof := Id.run do
  let mut out := #[]
  if let .some ⟨_ty, lhs, rhs⟩ := etype.eq? then do
    let lhs := lhs
    let rhs := rhs
    if let .some read := ReadBytesExpr.ofExpr? lhs then
      out := out.push { val := rhs, read := read, h := eval }

    if let .some read := ReadBytesExpr.ofExpr? rhs then
      out:= out.push { val := lhs, read := read, h := eval }
  return out

inductive Hypothesis
| separate (proof : MemSeparateProof e)
| subset (proof : MemSubsetProof e)
| legal (proof : MemLegalProof e)
| read_eq (proof : ReadBytesEqProof)

def Hypothesis.proof : Hypothesis → Expr
| .separate proof  => proof.h
| .subset proof => proof.h
| .legal proof => proof.h
| .read_eq proof => proof.h

instance : ToMessageData Hypothesis where
  toMessageData
  | .subset proof => toMessageData proof
  | .separate proof => toMessageData proof
  | .legal proof => toMessageData proof
  | .read_eq proof => toMessageData proof

/-- The internal state for the `SimpMemM` monad, recording previously encountered atoms. -/
structure State where
  hypotheses : Array Hypothesis := #[]
  rewriteFuel : Nat

def State.init (cfg : SimpMemConfig) : State :=
  { rewriteFuel := cfg.rewriteFuel}

abbrev SimpMemM := StateRefT State (ReaderT Context TacticM)

def SimpMemM.run (m : SimpMemM α) (cfg : SimpMemConfig) : TacticM α :=
  m.run' (State.init cfg) |>.run (Context.init cfg)

/-- Add a `Hypothesis` to our hypothesis cache. -/
def SimpMemM.addHypothesis (h : Hypothesis) : SimpMemM Unit :=
  modify fun s => { s with hypotheses := s.hypotheses.push h }

def SimpMemM.withMainContext (ma : SimpMemM α) : SimpMemM α := do
  (← getMainGoal).withContext ma

/-- create a trace node in trace class (i.e. `set_option traceClass true`),
with header `header`, whose default collapsed state is `collapsed`. -/
def SimpMemM.withTraceNode (header : MessageData) (k : SimpMemM α)
    (collapsed : Bool := true)
    (traceClass : Name := `simp_mem.info) : SimpMemM α :=
  Lean.withTraceNode traceClass (fun _ => return header) k (collapsed := collapsed)

def processingEmoji : String := "⚙️"

def consumeRewriteFuel : SimpMemM Unit :=
  modify fun s => { s with rewriteFuel := s.rewriteFuel - 1 }

def outofRewriteFuel? : SimpMemM Bool := do
  return (← get).rewriteFuel == 0
/-
Introduce a new definition into the local context,
and return the FVarId of the new definition in the goal.
-/
def introDef (name : String) (hdefVal : Expr) : SimpMemM FVarId  := do
  SimpMemM.withMainContext do
    let name ← mkFreshUserName <| .mkSimple name
    let goal ← getMainGoal
    let hdefTy ← inferType hdefVal
    let goal ← goal.define name hdefTy hdefVal
    let (fvar, goal) ← goal.intro1P
    replaceMainGoal [goal]
    return fvar

/-- SimpMemM's omega invoker -/
def omega : SimpMemM Unit := do
  -- https://leanprover.zulipchat.com/#narrow/stream/326056-ICERM22-after-party/topic/Regression.20tests/near/290131280
  -- @bollu: TODO: understand what precisely we are recovering from.
  withoutRecover do
    evalTactic (← `(tactic| bv_omega'))

section Hypotheses

/-- info: Memory.Region.Separate.ha {a b : Memory.Region} (self : a.Separate b) : a.legal -/
#guard_msgs in #check Memory.Region.Separate.ha

def MemSeparateProof.mem_separate'_ha (self : MemSeparateProof sep) :
    MemLegalProof sep.sa :=
  let h := mkAppN (Expr.const ``Memory.Region.Separate.ha [])
    #[sep.sa.toExpr, sep.sb.toExpr, sep.sb.n, self.h]
  MemLegalProof.mk h

/-- info: Memory.Region.Separate.hb {a b : Memory.Region} (self : a.Separate b) : b.legal -/
#guard_msgs in #check Memory.Region.Separate.hb

def MemSeparateProof.mem_separate'_hb (self : MemSeparateProof sep) :
    MemLegalProof sep.sb :=
  let h := mkAppN (Expr.const ``Memory.Region.Separate.hb [])
    #[sep.sa.toExpr, sep.sb.toExpr, self.h]
  MemLegalProof.mk h

/-- info: Memory.Region.Subset.ha {a b : Memory.Region} (self : a.Subset b) : a.legal -/
#guard_msgs in #check Memory.Region.Subset.ha

def MemSubsetProof.mem_subset'_ha (self : MemSubsetProof sub) :
    MemLegalProof sub.sa :=
  let h := mkAppN (Expr.const ``Memory.Region.Subset.ha [])
    #[sub.sa.toExpr, sub.sb.toExpr, self.h]
  MemLegalProof.mk h

/-- info: Memory.Region.Subset.hb {a b : Memory.Region} (self : a.Subset b) : b.legal -/
#guard_msgs in #check Memory.Region.Subset.hb

def MemSubsetProof.mem_subset'_hb (self : MemSubsetProof sub) :
    MemLegalProof sub.sb :=
  let h := mkAppN (Expr.const ``Memory.Region.Subset.hb [])
    #[sub.sa.toExpr, sub.sb.toExpr, self.h]
  MemLegalProof.mk h

/-- info: Memory.Region.base (self : Memory.Region) : BitVec 64 -/
#guard_msgs in #check Memory.Region.base

def MemoryRegionBase (e : Expr) : Expr :=
  mkAppN (Expr.const ``Memory.Region.base []) #[e]

/-- info: Memory.Region.len (self : Memory.Region) : Nat -/
#guard_msgs in #check Memory.Region.len

def MemoryRegionLen (e : Expr) : Expr :=
  mkAppN (Expr.const ``Memory.Region.len []) #[e]


/-- info: Memory.Region : Type -/
#guard_msgs in #check Memory.Region

def MemRegion.ofExpr? (e : Expr) (checkType? : Bool := true) :
    SimpMemM (Option MemRegionExpr) := do
  if checkType? then
    let ty ← inferType e
    unless ty.isConstOf ``Memory.Region do
      throwError "expected `{e} : Memory.Region`. found `{ty}`"
  match_expr e with
  | Memory.Region.mk base n => return .some { base := base, n := n }
  | _ =>
    let base ← (whnf (MemoryRegionBase e))
    let len ← (whnf (MemoryRegionLen e))
    return .some { base := base, n := len }

/-- match an expression `e` to a `mem_legal'`. -/
def MemLegalProp.ofExpr? (e : Expr) : SimpMemM (Option (MemLegalProp)) := do
  match_expr e with
  | Memory.Region.legal e =>
    let .some region ← MemRegion.ofExpr? e | pure none
    return some { region :=  region }
  | _ => return none

/-- match an expression `e` to a `mem_subset'`. -/
def MemSubsetProp.ofExpr? (e : Expr) : SimpMemM <| Option (MemSubsetProp) :=
  match_expr e with
  | Memory.Region.Subset sa sb => do
    let some sa ← MemRegion.ofExpr? sa | pure none
    let some sb ← MemRegion.ofExpr? sb | pure none
    return .some { sa := sa, sb := sb }
  | _ => return none

/-- match an expression `e` to a `mem_separate'`. -/
def MemSeparateProp.ofExpr? (e : Expr) : SimpMemM <| Option MemSeparateProp := do
  match_expr e with
  | Memory.Region.Separate sa sb =>
    let some sa ← MemRegion.ofExpr? sa | pure none
    let some sb ← MemRegion.ofExpr? sb | pure none
    return .some { sa := sa, sb := sb }
  | _ => return none

/-- Match an expression `h` to see if it's a useful hypothesis. -/
def hypothesisOfExpr (h : Expr) (hyps : Array Hypothesis) : SimpMemM (Array Hypothesis) := do
  let ht ← inferType h
  trace[simp_mem.info] "{processingEmoji} Processing '{h}' : '{toString ht}'"
  if let .some sep ← MemSeparateProp.ofExpr? ht then
    let proof : MemSeparateProof sep := ⟨h⟩
    let hyps := hyps.push (.separate proof)
    let hyps := hyps.push (.legal proof.mem_separate'_ha)
    let hyps := hyps.push (.legal proof.mem_separate'_hb)
    return hyps
  else if let .some sub ← MemSubsetProp.ofExpr? ht then
    let proof : MemSubsetProof sub := ⟨h⟩
    let hyps := hyps.push (.subset proof)
    let hyps := hyps.push (.legal proof.mem_subset'_ha)
    let hyps := hyps.push (.legal proof.mem_subset'_hb)
    return hyps
  else if let .some legal ← MemLegalProp.ofExpr? ht then
    let proof : MemLegalProof legal := ⟨h⟩
    let hyps := hyps.push (.legal proof)
    return hyps
  else
    let mut hyps := hyps
    for eqProof in ReadBytesEqProof.ofExpr? h ht do
      let proof : Hypothesis := .read_eq eqProof
      hyps := hyps.push proof
    return hyps

/--
info: Memory.Region.legal.omega_def {b : Memory.Region} (h : b.legal) : b.base.toNat + b.len ≤ 2 ^ 64
-/
#guard_msgs in #check Memory.Region.legal.omega_def


/-- Build a term corresponding to `Memory.Region.legal.omega_def`. -/
def MemLegalProof.omega_def (h : MemLegalProof e) : Expr :=
  mkAppN (Expr.const ``Memory.Region.legal.omega_def [])
    #[e.region.toExpr, h.h]

/-- Add the omega fact from `Region.legal.omega_def`. -/
def MemLegalProof.addOmegaFacts (h : MemLegalProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← introDef "hmemLegal_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)

/--
info: Memory.Region.Subset.omega_def {a b : Memory.Region} (h : a.Subset b) :
  a.base.toNat + a.len ≤ 2 ^ 64 ∧
    b.base.toNat + b.len ≤ 2 ^ 64 ∧ b.base.toNat ≤ a.base.toNat ∧ a.base.toNat + a.len ≤ b.base.toNat + b.len
-/
#guard_msgs in #check Memory.Region.Subset.omega_def

/--
Build a term corresponding to `Memory.Region.Subset.omega_def` which has facts written
in a style that is exploitable by omega.
-/
def MemSubsetProof.omega_def (h : MemSubsetProof e) : Expr :=
  mkAppN (Expr.const ``Memory.Region.Subset.omega_def [])
    #[e.sa.toExpr, e.sb.toExpr, h.h]

/-- Add the omega fact from `Memory.Region.Subset.omega_def` into the main goal. -/
def MemSubsetProof.addOmegaFacts (h : MemSubsetProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← introDef "hmemSubset_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)

/--
info: Memory.Region.Separate.omega_def {a b : Memory.Region} (h : a.Separate b) :
  a.base.toNat + a.len ≤ 2 ^ 64 ∧
    b.base.toNat + b.len ≤ 2 ^ 64 ∧ (a.base.toNat + a.len ≤ b.base.toNat ∨ a.base.toNat ≥ b.base.toNat + b.len)
-/
#guard_msgs in #check Memory.Region.Separate.omega_def

/--
Build a term corresponding to `Memory.Region.Separate.omega_def` which has facts written
in a style that is exploitable by omega.
-/
def MemSeparateProof.omega_def (h : MemSeparateProof e) : Expr :=
  mkAppN (Expr.const ``Memory.Region.Separate.omega_def [])
    #[e.sa.toExpr, e.sb.toExpr, h.h]

/-- Add the omega fact from `Memory.Region.Separate.omega_def`. -/
def MemSeparateProof.addOmegaFacts (h : MemSeparateProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← introDef "hmemSeparate_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)

/--
Given a hypothesis, add declarations that would be useful for omega-blasting
-/
def Hypothesis.addOmegaFactsOfHyp (h : Hypothesis) (args : Array Expr) : SimpMemM (Array Expr) :=
  match h with
  | Hypothesis.legal h => h.addOmegaFacts args
  | Hypothesis.subset h => h.addOmegaFacts args
  | Hypothesis.separate h => h.addOmegaFacts args
  | Hypothesis.read_eq _h => return args -- read has no extra `omega` facts.

/--
Accumulate all omega defs in `args`.
-/
def Hypothesis.addOmegaFactsOfHyps (hs : List Hypothesis) (args : Array Expr)
    : SimpMemM (Array Expr) := do
  SimpMemM.withTraceNode m!"Adding omega facts from hypotheses" do
    let mut args := args
    for h in hs do
      args ← h.addOmegaFactsOfHyp args
    return args

end Hypotheses

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
info: Memory.Region.legal.of_omega {b : Memory.Region} (h : b.base.toNat + b.len ≤ 2 ^ 64) : b.legal
-/
#guard_msgs in #check Memory.Region.legal.of_omega

instance : OmegaReducible MemLegalProp where
  reduceToOmega legal :=
    mkAppN (Expr.const ``Memory.Region.legal.of_omega []) #[legal.region.toExpr]

/--
info: Memory.Region.Subset.of_omega {a b : Memory.Region}
  (h :
    a.base.toNat + a.len ≤ 2 ^ 64 ∧
      b.base.toNat + b.len ≤ 2 ^ 64 ∧ b.base.toNat ≤ a.base.toNat ∧ a.base.toNat + a.len ≤ b.base.toNat + b.len) :
  a.Subset b
-/
#guard_msgs in #check Memory.Region.Subset.of_omega

instance : OmegaReducible MemSubsetProp where
  reduceToOmega subset :=
  mkAppN (Expr.const ``Memory.Region.Subset.of_omega [])
    #[subset.sa.toExpr, subset.sb.toExpr]

/--
info: Memory.Region.Separate.of_omega {a b : Memory.Region}
  (h :
    a.base.toNat + a.len ≤ 2 ^ 64 ∧
      b.base.toNat + b.len ≤ 2 ^ 64 ∧ (a.base.toNat + a.len ≤ b.base.toNat ∨ a.base.toNat ≥ b.base.toNat + b.len)) :
  a.Separate b
-/
#guard_msgs in #check Memory.Region.Separate.of_omega

instance : OmegaReducible MemSeparateProp where
  reduceToOmega separate :=
    mkAppN (Expr.const ``Memory.Region.Separate.of_omega [])
      #[separate.sa.toExpr, separate.sb.toExpr]

/--
`OmegaReducible` is a value whose type is `omegaFact → desiredFact`.
An example is `mem_lega'.of_omega n a`, which has type:
  `(h : a.toNat + n ≤ 2 ^ 64) → mem_legal' a n`.

@bollu: TODO: this can be generalized further, what we actually need is
  a way to convert `e : α` into the `omegaToDesiredFactFnVal`.
-/
def proveWithOmega?  {α : Type} [ToMessageData α] [OmegaReducible α] (e : α)
    (hyps : Array Hypothesis) : SimpMemM (Option (Proof α e)) := do
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
  let oldGoals := (← getGoals)

  try
    setGoals (omegaObligationVal.mvarId! :: (← getGoals))
    SimpMemM.withMainContext do
    let _ ← Hypothesis.addOmegaFactsOfHyps hyps.toList #[]
    trace[simp_mem.info] m!"Executing `omega` to close {e}"
    SimpMemM.withTraceNode m!"goal (Note: can be large)" do
      trace[simp_mem.info] "{← getMainGoal}"
    omega
    trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
    return (.some <| Proof.mk (← instantiateMVars factProof))
  catch e =>
    trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"
    setGoals oldGoals
    return none
  end ReductionToOmega

section Simplify

def SimpMemM.rewriteWithEquality (rw : Expr) (msg : MessageData) : SimpMemM Unit := do
  withTraceNode msg do
    withMainContext do
      withTraceNode m!"rewrite (Note: can be large)" do
        trace[simp_mem.info] "{← inferType rw}"
      let goal ← getMainGoal
      let result ← goal.rewrite (← getMainTarget) rw
      let mvarId' ← (← getMainGoal).replaceTargetEq result.eNew result.eqProof
      trace[simp_mem.info] "{checkEmoji} rewritten goal {mvarId'}"
      unless result.mvarIds == [] do
        throwError m!"{crossEmoji} internal error: expected rewrite to produce no side conditions. Produced {result.mvarIds}"
      replaceMainGoal [mvarId']

/--
info: Memory.Region.Separate.read_bytes_write_bytes_eq_read_bytes {mem : Memory} {r w : Memory.Region} (hsep : r.Separate w)
  (val : BitVec (w.len * 8)) :
  Memory.read_bytes r.len r.base (Memory.write_bytes w.len w.base val mem) = Memory.read_bytes r.len r.base mem
-/
#guard_msgs in #check Memory.Region.Separate.read_bytes_write_bytes_eq_read_bytes

/-- given that `e` is a read of the write, perform a rewrite,
using `Region.Separate.read_bytes_write_bytes_eq_read_bytes`. -/
def SimpMemM.rewriteReadOfSeparatedWrite
    (er : ReadBytesExpr) (ew : WriteBytesExpr)
    (separate : MemSeparateProof { sa := er.span, sb := ew.span }) : SimpMemM Unit := do
  let call :=
    mkAppN (Expr.const ``Memory.Region.Separate.read_bytes_write_bytes_eq_read_bytes [])
      #[ew.mem,
        er.span.toExpr,
        ew.span.toExpr,
        separate.h,
        ew.val]
  SimpMemM.rewriteWithEquality call m!"rewriting read({er})⟂write({ew})"

/--
info: Memory.Region.Subset.read_bytes_eq_extractLsBytes_sub {a b : Memory.Region} {mem : Memory} {val : BitVec (b.len * 8)}
  (hread : Memory.read_bytes b.len b.base mem = val) (hsubset : a.Subset b) :
  Memory.read_bytes a.len a.base mem = val.extractLsBytes (a.base.toNat - b.base.toNat) a.len
-/
#guard_msgs in #check Memory.Region.Subset.read_bytes_eq_extractLsBytes_sub

def SimpMemM.rewriteReadOfSubsetRead
    (er : ReadBytesExpr)
    (hread : ReadBytesEqProof)
    (hsubset : MemSubsetProof { sa := er.span, sb := hread.read.span })
  : SimpMemM Unit := do
  let call := mkAppN (Expr.const ``Memory.Region.Subset.read_bytes_eq_extractLsBytes_sub [])
    #[er.span.toExpr,
      hread.read.span.toExpr,
      er.mem,
      hread.val,
      hread.h,
      hsubset.h]
  SimpMemM.rewriteWithEquality call m!"rewriting read({er})⊆read({hread.read})"

/--
info: Memory.Region.Subset.read_bytes_write_bytes_eq_of_Region {mem : Memory} {r w : Memory.Region} (hsep : r.Subset w)
  (val : BitVec (w.len * 8)) :
  Memory.read_bytes r.len r.base (Memory.write_bytes w.len w.base val mem) =
    val.extractLsBytes (r.base.toNat - w.base.toNat) r.len
-/
#guard_msgs in #check Memory.Region.Subset.read_bytes_write_bytes_eq_of_Region

def SimpMemM.rewriteReadOfSubsetWrite
    (er : ReadBytesExpr) (ew : WriteBytesExpr) (hsubset : MemSubsetProof { sa := er.span, sb := ew.span }) : SimpMemM Unit := do
  let call := mkAppN (Expr.const ``Memory.Region.Subset.read_bytes_write_bytes_eq_of_Region [])
    #[ew.mem,
      er.span.toExpr,
      ew.span.toExpr,
      hsubset.h,
      ew.val]
  SimpMemM.rewriteWithEquality call m!"rewriting read({er})⊆write({ew})"

mutual

/--
Pattern match for memory patterns, and simplify them.
Close memory side conditions with `simplifyGoal`.
-/
partial def SimpMemM.simplifyExpr (e : Expr) (hyps : Array Hypothesis) : SimpMemM Unit := do
  consumeRewriteFuel
  if ← outofRewriteFuel? then
    trace[simp_mem.info] "out of fuel for rewriting, stopping."
    return ()

  if e.isSort then
    trace[simp_mem.info] "skipping sort '{e}'."
    return ()

  if let .some er := ReadBytesExpr.ofExpr? e then
    if let .some ew := WriteBytesExpr.ofExpr? er.mem then
      trace[simp_mem.info] "{checkEmoji} Found read of write."
      trace[simp_mem.info] "read: {er}"
      trace[simp_mem.info] "write: {ew}"
      trace[simp_mem.info] "{processingEmoji} read({er.span})⟂/⊆write({ew.span})"

      let separate := MemSeparateProp.mk er.span ew.span
      let subset := MemSubsetProp.mk er.span ew.span
      if let .some separateProof ← proveWithOmega? separate hyps then do
        trace[simp_mem.info] "{checkEmoji} {separate}"
        rewriteReadOfSeparatedWrite er ew separateProof
        return ()
      else if let .some subsetProof ← proveWithOmega? subset hyps then do
        trace[simp_mem.info] "{checkEmoji} {subset}"
        rewriteReadOfSubsetWrite er ew subsetProof
      else
        trace[simp_mem.info] "{crossEmoji} Could not prove {er.span} ⟂/⊆ {ew.span}"
        return ()
    else
      -- read
      trace[simp_mem.info] "{checkEmoji} Found read {er}."
      -- TODO: we don't need a separate `subset` branch for the writes: instead, for the write,
      -- we can add the theorem that `(write region).read = write val`.
      -- Then this generic theory will take care of it.
      withTraceNode m!"Searching for overlapping read {er.span}." do
        for hyp in hyps do
          if let Hypothesis.read_eq hReadEq := hyp then do
            withTraceNode m!"{processingEmoji} ... ⊆ {hReadEq.read.span} ? " do
            -- the read we are analyzing should be a subset of the hypothesis
            let subset := (MemSubsetProp.mk er.span hReadEq.read.span)
            if let some hSubsetProof ← proveWithOmega? subset hyps then
              trace[simp_mem.info] "{checkEmoji}  ... ⊆ {hReadEq.read.span}"
              rewriteReadOfSubsetRead er hReadEq hSubsetProof
              return ()
            else
              trace[simp_mem.info] "{crossEmoji}  ... ⊊ {hReadEq.read.span}"
  else
    if e.isForall then
      Lean.Meta.forallTelescope e fun xs b => do
        for x in xs do
          SimpMemM.simplifyExpr x hyps
          -- we may have a hypothesis like
          -- ∀ (x : read_mem (read_mem_bytes ...) ... = out).
          -- we want to simplify the *type* of x.
          SimpMemM.simplifyExpr (← inferType x) hyps
        SimpMemM.simplifyExpr b hyps
    else if e.isLambda then
      Lean.Meta.lambdaTelescope e fun xs b => do
        for x in xs do
          SimpMemM.simplifyExpr x hyps
          SimpMemM.simplifyExpr (← inferType x) hyps
        SimpMemM.simplifyExpr b hyps
    else
      -- check if we have expressions.
      match e with
      | .app f x =>
        SimpMemM.simplifyExpr f hyps
        SimpMemM.simplifyExpr x hyps
      | _ => return ()

/--
simplify the goal state, closing legality, subset, and separation goals,
and simplifying all other expressions.
-/
partial def SimpMemM.simplifyGoal (g : MVarId) (hyps : Array Hypothesis) : SimpMemM Unit := do
  SimpMemM.withMainContext do
    trace[simp_mem.info] "{processingEmoji} Matching on ⊢ {← g.getType}"
    let gt ← g.getType
    if let .some e ← MemLegalProp.ofExpr? gt then do
      withTraceNode m!"Matched on ⊢ {e}. Proving..." do
      if let .some proof ← proveWithOmega? e hyps then do
        (← getMainGoal).assign proof.h
    if let .some e ← MemSubsetProp.ofExpr? gt then do
      withTraceNode m!"Matched on ⊢ {e}. Proving..." do
      if let .some proof ←  proveWithOmega? e hyps then do
        (← getMainGoal).assign proof.h
    if let .some e ← MemSeparateProp.ofExpr? gt then do
      withTraceNode m!"Matched on ⊢ {e}. Proving..." do
      if let .some proof ←  proveWithOmega? e hyps then do
        (← getMainGoal).assign proof.h
    withTraceNode m!"Simplifying goal." do
      SimpMemM.simplifyExpr (← whnf gt) hyps

end

/--
The core simplification loop.
We look for appropriate hypotheses, and simplify (often closing) the main goal using them.
-/
def SimpMemM.simplifyLoop : SimpMemM Unit := do
    (← getMainGoal).withContext do
      let hyps := (← getLocalHyps)
      let foundHyps ← withTraceNode m!"Searching for Hypotheses" do
        let mut foundHyps : Array Hypothesis := #[]
        for h in hyps do
          foundHyps ← hypothesisOfExpr h foundHyps
        pure foundHyps
      withTraceNode m!"Summary: Found {foundHyps.size} hypotheses" do
        for (i, h) in foundHyps.toList.enum do
          trace[simp_mem.info] m!"{i+1}) {h}"

      withTraceNode m!"Performing Rewrite At Main Goal" do
        SimpMemM.simplifyGoal (← getMainGoal) foundHyps

end Simplify

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def simpMem (cfg : SimpMemConfig := {}) : TacticM Unit := do
  -- evalTactic (← `(simp (config := {failIfUnchanged := false}) only [memory_rules]))
  SimpMemM.run SimpMemM.simplifyLoop cfg


/-- The `simp_mem` tactic, for simplifying away statements about memory. -/
def simpMemTactic (cfg : SimpMemConfig) : TacticM Unit := simpMem cfg

end SeparateAutomation

/--
Allow elaboration of `SimpMemConfig` arguments to tactics.
-/
declare_config_elab elabSimpMemConfig SeparateAutomation.SimpMemConfig

/--
Implement the simp_mem tactic frontend.
-/
syntax (name := simp_mem) "simp_mem" (Lean.Parser.Tactic.config)? : tactic

@[tactic simp_mem]
def evalSimpMem : Tactic := fun
  | `(tactic| simp_mem $[$cfg]?) => do
    let cfg ← elabSimpMemConfig (mkOptionalNode cfg)
    SeparateAutomation.simpMemTactic cfg
  | _ => throwUnsupportedSyntax
