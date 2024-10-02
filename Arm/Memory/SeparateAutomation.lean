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
import Arm.Memory.AddressNormalization
import Lean
import Lean.Meta.ForEachExpr
import Lean.Meta.ExprTraverse
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Conv.Basic
import Tactics.Simp

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

/- We tag `mem_legal'` as `bv_toNat` here, since we want to actually lazily unfold this.
Doing it here lets us remove it from `bv_toNat` simp-set as a change to `SeparateAutomation.lean`,
without needing us to modify the core definitions file which incurs a recompile cost,
making experimentation annoying.
-/
attribute [bv_toNat] mem_legal'

end BvOmega

namespace SeparateAutomation

structure SimpMemConfig where
  /-- Locally turn on tracing for this particular invocation of 'simp_mem'. -/
  trace : Bool := false
  /-- number of times rewrites must be performed. -/
  rewriteFuel : Nat := 1000
  /-- whether an error should be thrown if the tactic makes no progress. -/
  failIfUnchanged : Bool := true

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
| pairwiseSeparate (proof : MemPairwiseSeparateProof e)
| read_eq (proof : ReadBytesEqProof)

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

/-- The internal state for the `SimpMemM` monad, recording previously encountered atoms. -/
structure State where
  hypotheses : Array Hypothesis := #[]
  rewriteFuel : Nat
  changed : Bool := false

def State.init (cfg : SimpMemConfig) : State :=
  { rewriteFuel := cfg.rewriteFuel}

abbrev SimpMemM := StateRefT State (ReaderT Context TacticM)

def SimpMemM.run (m : SimpMemM α) (cfg : SimpMemConfig) : TacticM α := do
  let insertTraceIfEnabled := fun (opts : Options) =>
    if cfg.trace then opts.insert `simp_mem.trace.info true else opts
  withOptions insertTraceIfEnabled do
    m.run' (State.init cfg) |>.run (Context.init cfg)

/-- Add a `Hypothesis` to our hypothesis cache. -/
def SimpMemM.addHypothesis (h : Hypothesis) : SimpMemM Unit :=
  modify fun s => { s with hypotheses := s.hypotheses.push h }

def SimpMemM.withMainContext (ma : SimpMemM α) : SimpMemM α := do
  (← getMainGoal).withContext ma

def SimpMemM.withContext (g : MVarId) (ma : SimpMemM α) : SimpMemM α := do
  g.withContext ma

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

/-- Create a trace note that folds `header` with `(NOTE: can be large)`,
and prints `msg` under such a trace node.
-/
def SimpMemM.traceLargeMsg (header : MessageData) (msg : MessageData) : SimpMemM Unit :=
    withTraceNode m!"{header} (NOTE: can be large)" do
      trace[simp_mem.info] msg


def getConfig : SimpMemM SimpMemConfig := do
  let ctx ← read
  return ctx.cfg

/-- info: state_value (fld : StateField) : Type -/
#guard_msgs in #check state_value

/-
Introduce a new definition into the local context, simplify it using `simp`,
and return the FVarId of the new definition in the goal.
-/
def simpAndIntroDef (name : String) (hdefVal : Expr) : SimpMemM FVarId  := do
  SimpMemM.withMainContext do

    let name ← mkFreshUserName <| .mkSimple name
    let goal ← getMainGoal
    let hdefTy ← inferType hdefVal

    /- Simp to gain some more juice out of the defn.. -/
    let mut simpTheorems : Array SimpTheorems := #[]
    for a in #[`minimal_theory, `bitvec_rules] do
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

    let goal ← goal.define name hdefTy hdefVal
    let (fvar, goal) ← goal.intro1P
    replaceMainGoal [goal]
    return fvar

/-- SimpMemM's omega invoker -/
def omega : SimpMemM Unit := do
  -- https://leanprover.zulipchat.com/#narrow/stream/326056-ICERM22-after-party/topic/Regression.20tests/near/290131280
  -- @bollu: TODO: understand what precisely we are recovering from.
  withoutRecover do
    evalTactic (← `(tactic| bv_omega))

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
  trace[simp_mem.info] "{processingEmoji} Processing '{h}' : '{toString ht}'"
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
    for eqProof in ReadBytesEqProof.ofExpr? h ht do
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
def MemLegalProof.addOmegaFacts (h : MemLegalProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← simpAndIntroDef "hmemLegal_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)

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
def MemSubsetProof.addOmegaFacts (h : MemSubsetProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← simpAndIntroDef "hmemSubset_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)

/--
Build a term corresponding to `mem_separate'.omega_def` which has facts written
in a style that is exploitable by omega.
-/
def MemSeparateProof.omega_def (h : MemSeparateProof e) : Expr :=
  mkAppN (Expr.const ``mem_separate'.omega_def [])
    #[e.sa.base, e.sa.n, e.sb.base, e.sb.n, h.h]

/-- Add the omega fact from `mem_legal'.omega_def`. -/
def MemSeparateProof.addOmegaFacts (h : MemSeparateProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    -- simp only [bitvec_rules] (failIfUnchanged := false)
    let fvar ← simpAndIntroDef "hmemSeparate_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)



/-- info: Ne.{u} {α : Sort u} (a b : α) : Prop -/
#guard_msgs in #check Ne

/-- info: List.get?.{u} {α : Type u} (as : List α) (i : Nat) : Option α -/
#guard_msgs in #check List.get?

/-- Make the expression `mems.get? i = some a`. -/
def mkListGetEqSomeTy (mems : MemPairwiseSeparateProp) (i : Nat) (a : MemSpanExpr) : SimpMemM Expr := do
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
    SimpMemM <| MemSeparateProof ⟨a, b⟩ := do
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
def MemPairwiseSeparateProof.addOmegaFacts (h : MemPairwiseSeparateProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  -- We need to loop over i, j where i < j and extract hypotheses.
  -- We need to find the length of the list, and return an `Array MemRegion`.
  let mut args := args
  for i in [0:e.xs.size] do
    for j in [i+1:e.xs.size] do
      let a := e.xs[i]!
      let b := e.xs[j]!
      args ← SimpMemM.withTraceNode m!"Exploiting ({i}, {j}) : {a} ⟂ {b}" do
        let proof ← h.mem_separate'_of_pairwiseSeparate_of_mem_of_mem i j a b
        SimpMemM.traceLargeMsg m!"added {← inferType proof.h}" m!"{proof.h}"
        proof.addOmegaFacts args
  return args
/--
Given a hypothesis, add declarations that would be useful for omega-blasting
-/
def Hypothesis.addOmegaFactsOfHyp (h : Hypothesis) (args : Array Expr) : SimpMemM (Array Expr) :=
  match h with
  | Hypothesis.legal h => h.addOmegaFacts args
  | Hypothesis.subset h => h.addOmegaFacts args
  | Hypothesis.separate h => h.addOmegaFacts args
  | Hypothesis.pairwiseSeparate h => h.addOmegaFacts args
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
Rewrites `e` via some `eq`, producing a proof `e = e'` for some `e'`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
-- source: https://github.com/leanprover-community/mathlib4/blob/b35703fe5a80f1fa74b82a2adc22f3631316a5b3/Mathlib/Lean/Expr/Basic.lean#L476-L477
private def rewrite (e eq : Expr) : MetaM Expr := do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'

/--
Rewrites the type of `e` via some `eq`, then moves `e` into the new type via `Eq.mp`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
-- source: https://github.com/leanprover-community/mathlib4/blob/b35703fe5a80f1fa74b82a2adc22f3631316a5b3/Mathlib/Lean/Expr/Basic.lean#L476-L477
private def rewriteType (e eq : Expr) : MetaM Expr := do
  mkEqMP (← rewrite (← inferType e) eq) e

-- def ppExprWithInfos (ctx : PPContext) (e : Expr) (msg : MessageData) : MetaM FormatWithInfos := do
--   let out : FormatWithInfos := {
--     fmt := format (toString e),
--     infos := RBMap.empty.insert 0 (.ofTermInfo { expr := e, lctx := ← getLCtx })
--   }
--   return out

-- def mkExprTraceNode (e : Expr) (msg : MessageData) : MessageData :=
--   MessageData.ofLazy
--     (fun ctx? => do
--       let msg ← MessageData.ofFormatWithInfos <$> match ctx? with
--         | .none => pure (format (toString e))
--         | .some ctx => ppExprWithInfos ctx e msg
--       return Dynamic.mk msg)
--     (fun mctx => instantiateMVarsCore mctx e |>.1.hasSyntheticSorry)

def SimpMemM.rewriteWithEqualityAtTarget (rw : Expr) (targetExpr : Expr) (msg : MessageData) : SimpMemM Expr := do
  withTraceNode msg do
    withMainContext do
      withTraceNode m!"rewrite (Note: can be large)" do
        trace[simp_mem.info] "{← inferType rw}"
      let targetExpr' ← rewriteType targetExpr rw
      return targetExpr'


/--
info: Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat}
  {mem : Memory} (hsep : mem_separate' x xn y yn) (val : BitVec (yn * 8)) :
  Memory.read_bytes xn x (Memory.write_bytes yn y val mem) = Memory.read_bytes xn x mem
-/
#guard_msgs in #check Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'

/-- given that `e` is a read of the write, perform a rewrite,
using `Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'`. -/
def SimpMemM.rewriteReadOfSeparatedWrite
    (er : ReadBytesExpr) (ew : WriteBytesExpr)
    (separate : MemSeparateProof { sa := er.span, sb := ew.span }) : SimpMemM Unit := do
  let call :=
    mkAppN (Expr.const ``Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' [])
      #[er.span.base, er.span.n,
        ew.span.base, ew.span.n,
        ew.mem,
        separate.h,
        ew.val]
  SimpMemM.rewriteWithEquality call m!"rewriting read({er})⟂write({ew})"

/--
info: Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset' {bn : Nat} {b : BitVec 64} {val : BitVec (bn * 8)}
  {a : BitVec 64} {an : Nat} {mem : Memory} (hread : Memory.read_bytes bn b mem = val)
  (hsubset : mem_subset' a an b bn) : Memory.read_bytes an a mem = val.extractLsBytes (a.toNat - b.toNat) an
-/
#guard_msgs in #check Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'

def SimpMemM.rewriteReadOfSubsetRead
    (er : ReadBytesExpr)
    (hread : ReadBytesEqProof)
    (hsubset : MemSubsetProof { sa := er.span, sb := hread.read.span })
  : SimpMemM Unit := do
  let call := mkAppN (Expr.const ``Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset' [])
    #[hread.read.span.n, hread.read.span.base,
      hread.val,
      er.span.base, er.span.n,
      er.mem,
      hread.h,
      hsubset.h]
  SimpMemM.rewriteWithEquality call m!"rewriting read({er})⊆read({hread.read})"

/--
info: Memory.read_bytes_write_bytes_eq_of_mem_subset' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat} {mem : Memory}
  (hsep : mem_subset' x xn y yn) (val : BitVec (yn * 8)) :
  Memory.read_bytes xn x (Memory.write_bytes yn y val mem) = val.extractLsBytes (x.toNat - y.toNat) xn
-/
#guard_msgs in #check Memory.read_bytes_write_bytes_eq_of_mem_subset'

def SimpMemM.rewriteReadOfSubsetWrite
    (er : ReadBytesExpr) (ew : WriteBytesExpr) (hsubset : MemSubsetProof { sa := er.span, sb := ew.span }) : SimpMemM Unit := do
  let call := mkAppN (Expr.const ``Memory.read_bytes_write_bytes_eq_of_mem_subset' [])
    #[er.span.base, er.span.n,
      ew.span.base, ew.span.n,
      ew.mem,
      hsubset.h,
      ew.val]
  SimpMemM.rewriteWithEquality call m!"rewriting read({er})⊆write({ew})"


structure SimplifyExprResult where
  e : Expr
  changed : Bool

mutual

/--
Pattern match for memory patterns, and simplify them.
Close memory side conditions with `simplifyGoal`.
Returns if progress was made.
-/
partial def SimpMemM.simplifyExpr
  (e : Expr)
  (hyps : Array Hypothesis)
  (useSeparate : Bool := false)
  (useSubset : Bool := false)
  (useOverlappingRead : Bool := false)
  : SimpMemM Bool := do
  consumeRewriteFuel
  if ← outofRewriteFuel? then
    trace[simp_mem.info] "out of fuel for rewriting, stopping."
    return false

  if e.isSort then
    trace[simp_mem.info] "skipping sort '{e}'."
    return false

  if let .some er := ReadBytesExpr.ofExpr? e then
    trace[simp_mem.info] "{checkEmoji} Found read {er.span}."
    if let .some ew := WriteBytesExpr.ofExpr? er.mem then
      trace[simp_mem.info] "{checkEmoji} Found read({er.span}) of write ({ew.span})."
      trace[simp_mem.info] "{processingEmoji} read({er.span})⟂/⊆write({ew.span})"

      let separate := MemSeparateProp.mk er.span ew.span
      let subset := MemSubsetProp.mk er.span ew.span
      if useSeparate then
        if let .some separateProof ← proveWithOmega? separate hyps then do
          trace[simp_mem.info] "{checkEmoji} {separate}"
          rewriteReadOfSeparatedWrite er ew separateProof
          return true
        else
          trace[simp_mem.info] "{crossEmoji} {separate}"

      if useSubset then
        if let .some subsetProof ← proveWithOmega? subset hyps then do
          trace[simp_mem.info] "{checkEmoji} {subset}"
          rewriteReadOfSubsetWrite er ew subsetProof
          return true
        else
          trace[simp_mem.info] "{crossEmoji} {separate}"

    if useOverlappingRead then
      -- TODO: we don't need a separate `subset` branch for the writes: instead, for the write,
      -- we can add the theorem that `(write region).read = write val`.
      -- Then this generic theory will take care of it.
      trace[simp_mem.info] m!"Searching for overlapping read {er.span}."
      for hyp in hyps do
        if let Hypothesis.read_eq hReadEq := hyp then do
          trace[simp_mem.info] "{processingEmoji} ... ⊆ {hReadEq.read.span} ? " do
          -- the read we are analyzing should be a subset of the hypothesis
          let subset := (MemSubsetProp.mk er.span hReadEq.read.span)
          if let some hSubsetProof ← proveWithOmega? subset hyps then
            trace[simp_mem.info] "{checkEmoji}  ... ⊆ {hReadEq.read.span}"
            rewriteReadOfSubsetRead er hReadEq hSubsetProof
            return true
    return false
  else
    if e.isForall then
      Lean.Meta.forallTelescope e fun xs b => do
        let mut changedInCurrentIter? := false
        for x in xs do
          changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr x hyps useSeparate useSubset useOverlappingRead)
          -- we may have a hypothesis like
          -- ∀ (x : read_mem (read_mem_bytes ...) ... = out).
          -- we want to simplify the *type* of x.
          changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr (← inferType x) hyps useSeparate useSubset useOverlappingRead)
        changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr b hyps useSeparate useSubset useOverlappingRead)
        return changedInCurrentIter?
    else if e.isLambda then
      Lean.Meta.lambdaTelescope e fun xs b => do
        let mut changedInCurrentIter? := false
        for x in xs do
          changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr x hyps useSeparate useSubset useOverlappingRead)
          changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr (← inferType x) hyps useSeparate useSubset useOverlappingRead)
        changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr b hyps useSeparate useSubset useOverlappingRead)
        return changedInCurrentIter?
    else
      -- check if we have expressions.
      match e with
      | .app f x =>
        let mut changedInCurrentIter? := false
        changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr f hyps useSeparate useSubset useOverlappingRead)
        changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr x hyps useSeparate useSubset useOverlappingRead)
        return changedInCurrentIter?
      | _ => return false


/--
simplify the goal state, closing legality, subset, and separation goals,
and simplifying all other expressions. return `true` if goal has been closed, and `false` otherwise.
-/
partial def SimpMemM.closeGoal (g : MVarId) (hyps : Array Hypothesis) : SimpMemM Bool := do
  SimpMemM.withContext g do
    trace[simp_mem.info] "{processingEmoji} Matching on ⊢ {← g.getType}"
    let gt ← g.getType
    if let .some e := MemLegalProp.ofExpr? gt then
      withTraceNode m!"Matched on ⊢ {e}. Proving..." do
        if let .some proof ← proveWithOmega? e hyps then
          g.assign proof.h
    if let .some e := MemSubsetProp.ofExpr? gt then
      withTraceNode m!"Matched on ⊢ {e}. Proving..." do
        if let .some proof ← proveWithOmega? e hyps then
          g.assign proof.h
    if let .some e := MemSeparateProp.ofExpr? gt then
      withTraceNode m!"Matched on ⊢ {e}. Proving..." do
        if let .some proof ← proveWithOmega? e hyps then
          g.assign proof.h
  return ← g.isAssigned



/--
simplify the goal state, closing legality, subset, and separation goals,
and simplifying all other expressions. Returns `true` if an improvement has been made
in the current iteration.
-/
partial def SimpMemM.simplifyGoal (g : MVarId) (hyps : Array Hypothesis) : SimpMemM Bool := do
  SimpMemM.withContext g do
    let gt ← g.getType
    let changedInCurrentIter? ← withTraceNode m!"Simplifying goal." do
        SimpMemM.simplifyExpr (← whnf gt) hyps (useSeparate := true) (useSubset := true) (useOverlappingRead := true)
    return changedInCurrentIter?
end

/--
The core simplification loop.
We look for appropriate hypotheses, and simplify (often closing) the main goal using them.
-/
partial def SimpMemM.simplifyLoop : SimpMemM Unit := do
  let g ← getMainGoal
  g.withContext do
    let hyps := (← getLocalHyps)
    let foundHyps ← withTraceNode m!"Searching for Hypotheses" do
      let mut foundHyps : Array Hypothesis := #[]
      for h in hyps do
        foundHyps ← hypothesisOfExpr h foundHyps
      pure foundHyps

    withTraceNode m!"Summary: Found {foundHyps.size} hypotheses" do
      for (i, h) in foundHyps.toList.enum do
        trace[simp_mem.info] m!"{i+1}) {h}"

    if ← SimpMemM.closeGoal g foundHyps then
      trace[simp_mem.info] "{checkEmoji} goal closed."
      return ()

    -- goal was not closed, try and improve.
    let mut changedInAnyIter? := false
    while true do
      if (← outofRewriteFuel?) then break

      let changedInCurrentIter? ← withTraceNode m!"Performing Rewrite At Main Goal" do
        SimpMemM.simplifyGoal (← getMainGoal) foundHyps
      changedInAnyIter? := changedInAnyIter? || changedInCurrentIter?

      if !changedInCurrentIter? then
        trace[simp_mem.info] "{crossEmoji} No progress made in this iteration. halting."
        break

    /- we haven't changed ever.. -/
    if !changedInAnyIter? && (← getConfig).failIfUnchanged then
        throwError "{crossEmoji} simp_mem failed to make any progress."

def simpMemSpecialized (useSeparate : Bool) (useSubset : Bool) (useOverlappingRead : Bool) : SimpMemM Unit := do
  let g ← getMainGoal
  let gt ← getMainTarget
  g.withContext do
    let hyps := (← getLocalHyps)
    let foundHyps : Array Hypothesis ← SimpMemM.withTraceNode m!"Searching for Hypotheses" do
      let mut foundHyps : Array Hypothesis := #[]
      for h in hyps do
        foundHyps ← hypothesisOfExpr h foundHyps
      pure foundHyps

    SimpMemM.withTraceNode m!"Summary: Found {foundHyps.size} hypotheses" do
    for (i, h) in foundHyps.toList.enum do
      trace[simp_mem.info] m!"{i+1}) {h}"

    let changed? ← SimpMemM.simplifyExpr (← whnf gt) foundHyps (useSeparate := useSeparate) (useSubset := useSubset) (useOverlappingRead := useOverlappingRead)
    if !changed? then
      throwError "{crossEmoji} simp_mem failed to make any progress."

  def simpMemSeparate : SimpMemM Unit := simpMemSpecialized (useSeparate := true) (useSubset := false) (useOverlappingRead := false)
  def simpMemSubset : SimpMemM Unit := simpMemSpecialized (useSeparate := false) (useSubset := true) (useOverlappingRead := false)
  def simpMemOverlappingRead : SimpMemM Unit := simpMemSpecialized (useSeparate := false) (useSubset := false) (useOverlappingRead := true)

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

/-- The `mem_omega` finishing tactic, to close arithmetic related goals about memory addresses. -/
def memOmegaTactic : TacticM Unit := do
  SimpMemM.run (cfg := {}) do
    let g ← getMainGoal
    g.withContext do
      let hyps := (← getLocalHyps)
      let foundHyps ← SimpMemM.withTraceNode m!"Searching for Hypotheses" do
        let mut foundHyps : Array Hypothesis := #[]
        for h in hyps do
          foundHyps ← hypothesisOfExpr h foundHyps
        pure foundHyps

      SimpMemM.withMainContext do
      let _ ← Hypothesis.addOmegaFactsOfHyps foundHyps.toList #[]
      trace[simp_mem.info] m!"Executing `omega` to close goal."
      SimpMemM.withTraceNode m!"goal (Note: can be large)" do
        trace[simp_mem.info] "{← getMainGoal}"
      omega
      trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
    return ()

end SeparateAutomation

/--
Allow elaboration of `SimpMemConfig` arguments to tactics.
-/
declare_config_elab elabSimpMemConfig SeparateAutomation.SimpMemConfig

/--
Direct `simp_mem` to assume certain memory relationships when trying to rewrite the context.
· ⟂w direct `simp_mem` to assume that the write is separated from the read.
· ⊆w directs `simp_mem` to assume that the read is a subset of a write.
· ⊆r directs `simp_mem` to assume that the read is a subset of a read in the hypothesis.
-/
syntax simpMemTarget := "⟂" <|> "⊆w" <|> "⊆r"

/--
Implement the simp_mem tactic frontend.
-/
syntax (name := simp_mem) "simp_mem" (Lean.Parser.Tactic.config)? (simpMemTarget)? : tactic

/--
Use the `simp_mem` preprocessing to automatically close goals that involve
reasoning about addresses in memory.
-/
syntax (name := mem_omega) "mem_omega" : tactic

@[tactic simp_mem]
def evalSimpMem : Tactic := fun
  | `(tactic| simp_mem $[$cfg]?) => do
    let cfg ← elabSimpMemConfig (mkOptionalNode cfg)
    SeparateAutomation.simpMemTactic cfg
  | `(tactic| simp_mem $[$cfg]? ⟂) => do
    let cfg ← elabSimpMemConfig (mkOptionalNode cfg)
    SeparateAutomation.SimpMemM.run SeparateAutomation.simpMemSeparate cfg
  | `(tactic| simp_mem $[$cfg]? ⊆w) => do
    let cfg ← elabSimpMemConfig (mkOptionalNode cfg)
    SeparateAutomation.SimpMemM.run SeparateAutomation.simpMemSubset cfg
  | `(tactic| simp_mem $[$cfg]? ⊆r) => do
    let cfg ← elabSimpMemConfig (mkOptionalNode cfg)
    SeparateAutomation.SimpMemM.run SeparateAutomation.simpMemOverlappingRead cfg
  | _ => throwUnsupportedSyntax

@[tactic mem_omega]
def evalMemOmega : Tactic := fun
| `(tactic| mem_omega) =>
  SeparateAutomation.memOmegaTactic
| _ => throwUnsupportedSyntax
