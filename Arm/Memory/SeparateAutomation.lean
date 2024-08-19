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
-/

section BvOmega

macro "bv_omega'" : tactic =>
  `(tactic| (try simp only [bv_toNat, mem_legal'] at * <;> try rw [BitVec.le_def]) <;> omega)

end BvOmega

namespace SeparateAutomation

structure SimpMemConfig where

/-- Context for the `SimpMemM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `simp_mem`. -/
  cfg : SimpMemConfig

def Context.init (cfg : SimpMemConfig) : Context where
  cfg := cfg

structure WithWitness (α : Type) (e : α) where
  h : Expr -- a proof of an expression `a`.

def WithWitness.e {α : Type} {e : α} (p : WithWitness α e) : α := e

instance [ToMessageData α] : ToMessageData (WithWitness α e) where
  toMessageData proof := m! "{proof.h}: {e}"


structure MemSpanExpr where
  base : Expr
  n : Expr

instance : ToMessageData MemSpanExpr where
  toMessageData span := m! "[{span.base}..{span.n})"

/-- a term of the form 'mem_legal a' -/
structure MemLegalExpr  where
  span : MemSpanExpr

/-- convert this back to an Expr -/
def MemLegalExpr.toExpr (legal : MemLegalExpr) : Expr :=
  mkAppN (Expr.const ``mem_legal' []) #[legal.span.base, legal.span.n]

instance : ToMessageData MemLegalExpr where
  toMessageData e := m!"{e.span}.legal"

/-- Coerce a span into a `span.legal` hypothesis. -/
instance : Coe MemSpanExpr MemLegalExpr where
  coe := MemLegalExpr.mk

structure MemSubsetExpr where
  sa : MemSpanExpr
  sb : MemSpanExpr

instance : ToMessageData MemSubsetExpr where
  toMessageData e := m!"{e.sa}⊆{e.sb}"

abbrev MemSubsetProof := WithWitness MemSubsetExpr

def MemSubsetProof.mk {e : MemSubsetExpr} (h : Expr) : MemSubsetProof e :=
  { h }

structure MemSeparateExpr where
  sa : MemSpanExpr
  sb : MemSpanExpr

instance : ToMessageData MemSeparateExpr where
  toMessageData e := m!"{e.sa}⟂{e.sb}"

abbrev MemSeparateProof := WithWitness MemSeparateExpr

def MemSeparateProof.mk {e : MemSeparateExpr} (h : Expr) : MemSeparateProof e :=
  { h }


abbrev MemLegalProof := WithWitness MemLegalExpr

def MemLegalProof.mk {e : MemLegalExpr} (h : Expr) : MemLegalProof e :=
  { h }

/-- info: Memory.read_bytes (n : Nat) (addr : BitVec 64) (m : Memory) : BitVec (n * 8) -/
#guard_msgs in #check Memory.read_bytes

structure ReadBytesExpr where
  span : MemSpanExpr
  mem : Expr

/-- match an expression `e` to `Memory.read_bytes`. -/
def ReadBytesExpr.match? (e : Expr) : Option (ReadBytesExpr) :=
  match_expr e with
  | Memory.read_bytes n addr m =>
    some { span := { base := addr, n := n }, mem := m }
  | _ => none

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



def WriteBytesExpr.match? (e : Expr) : Option WriteBytesExpr :=
  match_expr e with
  | Memory.write_bytes n addr val m =>
    some { span := { base := addr, n := n }, val := val, mem := m }
  | _ => none

inductive Hypothesis
| separate (proof : MemSeparateProof e)
| subset (proof : MemSubsetProof e)
| legal (proof : MemLegalProof e)

def Hypothesis.proof : Hypothesis → Expr
| .separate proof  => proof.h
| .subset proof => proof.h
| .legal proof => proof.h

instance : ToMessageData Hypothesis where
  toMessageData
  | .subset proof => toMessageData proof
  | .separate proof => toMessageData proof
  | .legal proof => toMessageData proof

/-- The internal state for the `SimpMemM` monad, recording previously encountered atoms. -/
structure State where
  hypotheses : Array Hypothesis := #[]

def State.init : State := {}

abbrev SimpMemM := StateRefT State (ReaderT Context TacticM)

def SimpMemM.run (m : SimpMemM α) (cfg : SimpMemConfig) : TacticM α :=
  m.run' State.init |>.run (Context.init cfg)

/-- Add a `Hypothesis` to our hypothesis cache. -/
def SimpMemM.addHypothesis (h : Hypothesis) : SimpMemM Unit :=
  modify fun s => { s with hypotheses := s.hypotheses.push h }

def SimpMemM.withMainContext (ma : SimpMemM α) : SimpMemM α := do
  (← getMainGoal).withContext ma

def processingEmoji : String := "⚙️"

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
def MemLegalExpr.match? (e : Expr) : Option (MemLegalExpr) :=
  match_expr e with
  | mem_legal' a n => .some { span := { base := a, n := n } }
  | _ => none

/-- match an expression `e` to a `mem_subset'`. -/
def MemSubsetExpr.match? (e : Expr) : Option (MemSubsetExpr) :=
  match_expr e with
  | mem_subset' a na b nb =>
    let sa : MemSpanExpr := { base := a, n := na }
    let sb : MemSpanExpr := { base := b, n := nb }
    .some { sa, sb }
  | _ => none

/-- match an expression `e` to a `mem_separate'`. -/
def MemSeparateExpr.match? (e : Expr) : Option MemSeparateExpr :=
  match_expr e with
  | mem_separate' a na b nb =>
    let sa : MemSpanExpr := ⟨a, na⟩
    let sb : MemSpanExpr := ⟨b, nb⟩
    .some { sa, sb }
  | _ => none

/-- Match an expression `h` to see if it's a useful hypothesis. -/
def processHypothesis (h : Expr) (hyps : Array Hypothesis) : MetaM (Array Hypothesis) := do
  let ht ← inferType h
  trace[simp_mem.info] "{processingEmoji} Processing '{h}' : '{toString ht}'"
  if let .some sep := MemSeparateExpr.match? ht then
    let proof : MemSeparateProof sep := ⟨h⟩
    let hyps := hyps.push (.separate proof)
    let hyps := hyps.push (.legal proof.mem_separate'_ha)
    let hyps := hyps.push (.legal proof.mem_separate'_hb)
    return hyps
  else if let .some sub := MemSubsetExpr.match? ht then
    let proof : MemSubsetProof sub := ⟨h⟩
    let hyps := hyps.push (.subset proof)
    let hyps := hyps.push (.legal proof.mem_subset'_ha)
    let hyps := hyps.push (.legal proof.mem_subset'_hb)
    return hyps
  else if let .some legal := MemLegalExpr.match? ht then
    let proof : MemLegalProof legal := ⟨h⟩
    let hyps := hyps.push (.legal proof)
    return hyps
  else
    return hyps


/-
Introduce a new definition into the local context,
and then run the rest of the continuation as `(k newDefExpr)`,
where `newDefExpr` is the FVarId of the new definition in the goal.
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
    evalTactic (← `(tactic| bv_omega'))


section MemLegal

/-- info: mem_legal'.def {a : BitVec 64} {n : Nat} (h : mem_legal' a n) : a.toNat + n ≤ 2 ^ 64 -/
#guard_msgs in #check mem_legal'.def


/-- Build a term corresponding to `mem_legal'.def`. -/
def MemLegalProof.def (h : MemLegalProof e) : Expr :=
  mkAppN (Expr.const ``mem_legal'.def []) #[e.span.base, e.span.n, h.h]

/-- Add the omega fact from `mem_legal'.def` and run the rest of the continuation. -/
def MemLegalProof.addOmegaFacts (h : MemLegalProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← introDef "hmemLegal_omega" h.def
    trace[simp_mem.info]  "{h}: added omega fact ({h.def})"
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

/-- Add the omega fact from `mem_legal'.def` and run the rest of the continuation. -/
def MemSubsetProof.addOmegaFacts (h : MemSubsetProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← introDef "hmemSubset_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)

/--
Build a term corresponding to `mem_separate'.omega_def` which has facts written
in a style that is exploitable by omega.
-/
def MemSeparateProof.omega_def (h : MemSeparateProof e) : Expr :=
  mkAppN (Expr.const ``mem_separate'.omega_def [])
    #[e.sa.base, e.sa.n, e.sb.base, e.sb.n, h.h]

/-- Add the omega fact from `mem_legal'.def` and run the rest of the continuation. -/
def MemSeparateProof.addOmegaFacts (h : MemSeparateProof e) (args : Array Expr) :
    SimpMemM (Array Expr) := do
  SimpMemM.withMainContext do
    let fvar ← introDef "hmemSeparate_omega" h.omega_def
    trace[simp_mem.info]  "{h}: added omega fact ({h.omega_def})"
    return args.push (Expr.fvar fvar)

/--
Given a hypothesis, add declarations that would be useful for omega-blasing, and then run the
continuation. -/
def Hypothesis.addOmegaFactsOfHyp (h : Hypothesis) (args : Array Expr) : SimpMemM (Array Expr) :=
  match h with
  | Hypothesis.legal h => h.addOmegaFacts args
  | Hypothesis.subset h => h.addOmegaFacts args
  | Hypothesis.separate h => h.addOmegaFacts args

/--
Accumulate all omega defs in `args` and finally call the continuation `k`
with all omega definitions added.
-/
def Hypothesis.addOmegaFactsOfHyps (hs : List Hypothesis) (args : Array Expr)
    : SimpMemM (Array Expr) := do
  withTraceNode `simp_mem.info (fun _ => return m!"Adding omega facts from hypotheses") do
    let mut args := args
    for h in hs do
      args ← h.addOmegaFactsOfHyp args
    return args

/--
info: mem_legal'.of_omega {n : Nat} {a : BitVec 64} (h : a.toNat + n ≤ 2 ^ 64) : mem_legal' a n
-/
#guard_msgs in #check mem_legal'.of_omega


/--
Try to prove that the memory access is legal by reducing the problem to `omega`.
Eventually, this will be supplemented by heuristics.
-/
def proveMemLegalWithOmega? (legal : MemLegalExpr)
    (hyps : Array Hypothesis) : SimpMemM (Option (MemLegalProof legal)) := do
  -- [a..n)
  let a := legal.span.base
  let n := legal.span.n
  -- (h : a.toNat + n ≤ 2 ^ 64) → mem_legal' a n
  let legalOfOmegaVal := mkAppN (Expr.const ``mem_legal'.of_omega []) #[n, a]
  let legalOfOmegaTy ← inferType legalOfOmegaVal
  trace[simp_mem.info] "partially applied: '{legalOfOmegaVal} : {legalOfOmegaTy}'"
  let omegaObligationTy ← do -- (h : a.toNat + n ≤ 2 ^ 64)
    match legalOfOmegaTy with
    | Expr.forallE _argName argTy _body _binderInfo => pure argTy
    | _ => throwError "expected '{legalOfOmegaTy}' to a ∀"
  trace[simp_mem.info] "omega obligation '{omegaObligationTy}'"
  let omegaGoal ← mkFreshExprMVar (type? := omegaObligationTy)
  let legalOfOmegaVal := mkAppN legalOfOmegaVal #[omegaGoal]

  try
    setGoals (omegaGoal.mvarId! :: (← getGoals))
    SimpMemM.withMainContext do
    let _ ← Hypothesis.addOmegaFactsOfHyps hyps.toList #[]
    trace[simp_mem.info] "Executing `omega` to close {legal}"
    trace[simp_mem.info] "{← getMainGoal}"
    omega
    trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
    return (.some <| MemLegalProof.mk (← instantiateMVars legalOfOmegaVal))
  catch e =>
    trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"
    return none
end MemLegal


section MemSubset

/--
info: mem_subset'.of_omega {an bn : Nat} {a b : BitVec 64}
  (h : a.toNat + an ≤ 2 ^ 64 ∧ b.toNat + bn ≤ 2 ^ 64 ∧ b.toNat ≤ a.toNat ∧ a.toNat + an ≤ b.toNat + bn) :
  mem_subset' a an b bn
-/
#guard_msgs in #check mem_subset'.of_omega


/--
Try to prove that the memory subset is legal by reducing the problem to `omega`.
Eventually, this will be supplemented by heuristics.
-/
def proveMemSubsetWithOmega? (subset : MemSubsetExpr)
    (hyps : Array Hypothesis) : SimpMemM (Option (MemSubsetProof subset)) := do
  -- [a..n)
  let a := subset.sa.base
  let an := subset.sa.n
  let b := subset.sb.base
  let bn := subset.sb.n
  let ofOmegaVal := mkAppN (Expr.const ``mem_subset'.of_omega []) #[an, bn, a, b]
  let ofOmegaTy ← inferType ofOmegaVal
  trace[simp_mem.info] "partially applied: '{ofOmegaVal} : {ofOmegaTy}'"
  let omegaObligationTy ← do
    match ofOmegaTy with
    | Expr.forallE _argName argTy _body _binderInfo => pure argTy
    | _ => throwError "expected '{ofOmegaTy}' to a ∀"
  trace[simp_mem.info] "omega obligation '{omegaObligationTy}'"
  let omegaGoal ← mkFreshExprMVar (type? := omegaObligationTy)
  let ofOmegaVal := mkAppN ofOmegaVal #[omegaGoal]

  try
    setGoals (omegaGoal.mvarId! :: (← getGoals))
    SimpMemM.withMainContext do
    let _ ← Hypothesis.addOmegaFactsOfHyps hyps.toList #[]
    trace[simp_mem.info] "Executing `omega` to close {subset}"
    trace[simp_mem.info] "{← getMainGoal}"
    omega
    trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
    return (.some <| MemSubsetProof.mk (← instantiateMVars ofOmegaVal))
  catch e =>
    -- | TODO: raise `e`.
    trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"
    return none

end MemSubset

section MemSeparate

/--
info: mem_subset'.of_omega {an bn : Nat} {a b : BitVec 64}
  (h : a.toNat + an ≤ 2 ^ 64 ∧ b.toNat + bn ≤ 2 ^ 64 ∧ b.toNat ≤ a.toNat ∧ a.toNat + an ≤ b.toNat + bn) :
  mem_subset' a an b bn
-/
#guard_msgs in #check mem_subset'.of_omega


/--
Try to prove that the memory subset is legal by reducing the problem to `omega`.
Eventually, this will be supplemented by heuristics.
-/
def proveMemSeparateWithOmega? (e : MemSeparateExpr)
    (hyps : Array Hypothesis) : SimpMemM (Option (MemSeparateProof e)) := do
  withTraceNode `simp_mem.info (fun _ => return m!"proving {e}") do
    -- [a..n)
    let a := e.sa.base
    let an := e.sa.n
    let b := e.sb.base
    let bn := e.sb.n
    let ofOmegaVal := mkAppN (Expr.const ``mem_separate'.of_omega []) #[an, bn, a, b]
    let ofOmegaTy ← inferType ofOmegaVal
    trace[simp_mem.info] "partially applied: '{ofOmegaVal} : {ofOmegaTy}'"
    let omegaObligationTy ← do
      match ofOmegaTy with
      | Expr.forallE _argName argTy _body _binderInfo => pure argTy
      | _ => throwError "expected '{ofOmegaTy}' to a ∀"
    trace[simp_mem.info] "omega obligation '{omegaObligationTy}'"
    let omegaGoal ← mkFreshExprMVar (type? := omegaObligationTy)
    let ofOmegaVal := mkAppN ofOmegaVal #[omegaGoal]

    try
      setGoals (omegaGoal.mvarId! :: (← getGoals))
      SimpMemM.withMainContext do
      let _ ← Hypothesis.addOmegaFactsOfHyps hyps.toList #[]
      trace[simp_mem.info] "Executing `omega` to close {e}"
      trace[simp_mem.info] "{← getMainGoal}"
      omega
      trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
      return (.some <| MemSeparateProof.mk (← instantiateMVars ofOmegaVal))
    catch e =>
      trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"
      return none

end MemSeparate

/--
info: Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat}
  {mem : Memory} (hsep : mem_separate' x xn y yn) (val : BitVec (yn * 8)) :
  Memory.read_bytes xn x (Memory.write_bytes yn y val mem) = Memory.read_bytes xn x mem
-/
#guard_msgs in #check Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate'

/-
TODO: add fuel to make sure we don't fuck up and create an infinite loop:
-/
mutual

/-- given that `e` is a read of the write, perform a rewrite. using -/
partial def SimpMemM.rewriteReadOfSeparatedWrite (e : Expr) (hyps : Array Hypothesis)
    (er : ReadBytesExpr) (ew : WriteBytesExpr)
    (separate : MemSeparateProof { sa := er.span, sb := ew.span }) : SimpMemM Unit := do
  withTraceNode `simp_mem.info (fun _ => return m!"simplifying read {er}⟂{ew} write") do
  withMainContext do
    let call :=
      mkAppN (Expr.const ``Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' [])
        #[er.span.base, er.span.n,
          ew.span.base, ew.span.n,
          ew.mem,
          separate.h,
          ew.val]
    -- stolen from Lean/Elab/Tactic/Rewrite
    let goal ← getMainGoal
    let result ← goal.rewrite (← getMainTarget) call
    let mvarId' ← (← getMainGoal).replaceTargetEq result.eNew result.eqProof
    trace[simp_mem.info] "{checkEmoji} rewritten goal {mvarId'}"
    unless result.mvarIds == [] do
      throwError m!"{crossEmoji} internal error: expected rewrite to produce no side conditions. Produced {result.mvarIds}"
    -- trace[simp_mem.info] "{processingEmoji} closing rewrite side condition '{goal}'."
    -- replaceMainGoal [goal]
    -- improveGoal goal hyps
    replaceMainGoal [mvarId']

partial def SimpMemM.improveExpr (e : Expr) (hyps : Array Hypothesis) : SimpMemM Unit := do
  if let .some er := ReadBytesExpr.match? e then
    if let .some ew := WriteBytesExpr.match? er.mem then
      trace[simp_mem.info] "{checkEmoji} Found read of write."
      trace[simp_mem.info] "read: {er}"
      trace[simp_mem.info] "write: {ew}"
      trace[simp_mem.info] "{processingEmoji} read({er.span})⟂/⊆write({ew.span})"

      let separate := MemSeparateExpr.mk er.span ew.span
      let subset := MemSubsetExpr.mk er.span ew.span
      if let .some separateProof ← proveMemSeparateWithOmega? separate hyps then do
        trace[simp_mem.info] "{checkEmoji} {separate}"
        rewriteReadOfSeparatedWrite e hyps er ew separateProof
        return ()
      else if let .some subsetProof ← proveMemSubsetWithOmega? subset hyps then do
        trace[simp_mem.info] "{checkEmoji} {subset}"
      else
        trace[simp_mem.info] "{crossEmoji} Could not prove {er.span} ⟂/⊆ {ew.span}"
        return ()
    else
      -- read
      trace[simp_mem.info] "{checkEmoji} Found read {er}."
      trace[simp_mem.info] "Searching for overlapping read {er.span}."
      return ()
  return ()

-- /-- info: mem_legal' (a : BitVec 64) (n : Nat) : Prop -/
-- #guard_msgs in #check mem_legal'

partial def SimpMemM.improveGoal (g : MVarId) (hyps : Array Hypothesis) : SimpMemM Unit := do
  SimpMemM.withMainContext do
    trace[simp_mem.info] "{processingEmoji} Matching on ⊢ {← g.getType}"
    let gt ← g.getType
    if let .some e := MemLegalExpr.match? gt then do
      withTraceNode `simp_mem.info (fun _ => return m!"Matched on ⊢ {e}. Proving...") do
      if let .some proof ←  proveMemLegalWithOmega? e hyps then do
        (← getMainGoal).assign proof.h
    if let .some e := MemSubsetExpr.match? gt then do
      withTraceNode `simp_mem.info (fun _ => return m!"Matched on ⊢ {e}. Proving...") do
      if let .some proof ←  proveMemSubsetWithOmega? e hyps then do
        (← getMainGoal).assign proof.h
    if let .some e := MemSeparateExpr.match? gt then do
      withTraceNode `simp_mem.info (fun _ => return m!"Matched on ⊢ {e}. Proving...") do
      if let .some proof ←  proveMemSeparateWithOmega? e hyps then do
        (← getMainGoal).assign proof.h

    if let some (_, lhs, rhs) ← matchEq? gt then
      withTraceNode `simp_mem.info (fun _ => return m!"Matched on equality. Simplifying") do
        withTraceNode `simp_mem.info (fun _ => return m!"⊢ Simplifying LHS") do
          improveExpr lhs hyps
        withTraceNode `simp_mem.info (fun _ => return m!"⊢ Simplifying RHS") do
          improveExpr rhs hyps
    -- -- TODO: do this till fixpoint.
    -- for h in (← get).hypotheses do
    --   let x ← mkFreshExprMVar .none
    --   let xn ← mkFreshExprMVar .none
    --   let y ← mkFreshExprMVar .none
    --   let yn ← mkFreshExprMVar .none
    --   let state ← mkFreshExprMVar .none
    --   let f := (Expr.const ``read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate' [])
    --   let result : Option RewriteResult ←
    --     try
    --       pure <| some (← g.rewrite (← g.getType) (mkAppN f #[x, xn, y, yn, state, h.proof]) false)
    --     catch _ =>
    --       pure <| none
    --   match result with
    --   | .none =>
    --     trace[simp_mem.info] "{crossEmoji} rewrite did not fire"
    --   | .some r =>
    --     let mvarId' ← g.replaceTargetEq r.eNew r.eqProof
    --     -- | TODO: dispatch other goals that occur proof automation.
    --     Tactic.setGoals <| mvarId' :: r.mvarIds

end

def SimpMemM.analyzeLoop : SimpMemM Unit := do
    (← getMainGoal).withContext do
      let hyps := (← getLocalHyps)
      -- trace[simp_mem] "analyzing {hyps.size} hypotheses:\n{← hyps.mapM (liftMetaM ∘ inferType)}"
      let foundHyps ← withTraceNode `simp_mem.info (fun _ => return m!"Searching for Hypotheses") do
        let mut foundHyps : Array Hypothesis := #[]
        for h in hyps do
          foundHyps ← processHypothesis h foundHyps
        pure foundHyps
        -- if let some hyp ← processHypothesis h then
        --   trace[simp_mem.info] m!"{checkEmoji} Found '{h}'"
        --   SimpMemM.addHypothesis hyp
        -- else
        --   trace[simp_mem.info] m!"{crossEmoji} Rejecting '{h}'"
      withTraceNode `simp_mem.info (fun _ => return m!"Summary: Found {foundHyps.size} hypotheses") do
        for (i, h) in foundHyps.toList.enum do
          trace[simp_mem.info] m!"{i+1}) {h}"

      withTraceNode `simp_mem.info (fun _ => return m!"Performing Rewrite At Main Goal") do
        SimpMemM.improveGoal (← getMainGoal) foundHyps
/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def simpMem (cfg : SimpMemConfig := {}) : TacticM Unit := do
  -- evalTactic (← `(simp (config := {failIfUnchanged := false}) only [memory_rules]))
  SimpMemM.run SimpMemM.analyzeLoop cfg


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
