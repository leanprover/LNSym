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


structure MemSpan where
  base : Expr
  n : Expr

instance : ToMessageData MemSpan where
  toMessageData span := m! "[{span.base}..{span.n})"

structure MemSubsetExpr where
  a : MemSpan
  b : MemSpan

structure MemSubsetProof (a b : MemSpan) where
  h : Expr

instance : ToMessageData (MemSubsetProof a b) where
  toMessageData proof := m! "{proof.h}: {a}⊆{b}"

structure MemSeparateProof (a b : MemSpan) where
  h : Expr

instance : ToMessageData (MemSeparateProof a b) where
  toMessageData proof := m! "{proof.h}: {a}⟂{b}"

structure MemLegalProof (a : MemSpan) where
  h : Expr

instance : ToMessageData (MemLegalProof a) where
  toMessageData proof := m! "{proof.h}: {a}.legal"

/-- an occurrence of Memory.read in `e`. -/
structure ReadExpr (parent : Expr) where
  hyp : Expr
  mem : Expr
  read : Span

structure ReadEqn (parent : Expr) extends ReadExpr parent where
  outval : Expr -- the value we have read.


inductive Hypothesis
| separate (a : MemSpan) (b : MemSpan) (proof : MemSeparateProof a b)
| subset (a : MemSpan) (b : MemSpan) (proof : MemSubsetProof a b)
| legal (a : MemSpan) (proof : MemLegalProof a)

def Hypothesis.proof : Hypothesis → Expr
| .separate a b proof  => proof.h
| .subset a b proof => proof.h
| .legal a proof => proof.h

instance : ToMessageData Hypothesis where
  toMessageData
  | .subset a b proof => toMessageData proof
  | .separate a b proof => toMessageData proof
  | .legal a proof => toMessageData proof

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

def processingEmoji : String := "⚙️"

/-- Match an expression `h` to see if it's a useful hypothesis. -/
def processHypothesis (h : Expr) (hyps : Array Hypothesis) : MetaM (Array Hypothesis) := do
  let ht ← inferType h
  trace[simp_mem.info] "{processingEmoji} Processing '{h}' : '{toString ht}'"
  match_expr ht with
  | mem_separate' a na b nb =>
    let sa : MemSpan := ⟨a, na⟩
    let sb : MemSpan := ⟨b, nb⟩
    let proof : MemSeparateProof sa sb := ⟨h⟩
    return hyps.push (.separate sa sb proof)
  | mem_subset' a na b nb =>
    let sa : MemSpan := ⟨a, na⟩
    let sb : MemSpan := ⟨b, nb⟩
    let proof : MemSeparateProof sa sb := ⟨h⟩
    return hyps.push (.separate sa sb proof)
  | mem_legal' a na =>
    let sa : MemSpan := ⟨a, na⟩
    let proof : MemLegalProof sa := ⟨h⟩
    return hyps.push (.legal sa proof)
  | _ => return hyps

/--
info: read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat}
  {mem : ArmState} (hsep : mem_separate' x xn y yn) (val : BitVec (yn * 8)) :
  read_mem_bytes xn x (write_mem_bytes yn y val mem) = read_mem_bytes xn x mem
-/
#guard_msgs in #check read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate'

partial def SimpMemM.rewrite (g : MVarId) : SimpMemM Unit := do
  trace[simp_mem.info] "{processingEmoji} Matching on ⊢ {← g.getType}"
  let some (_, _lhs, _rhs) ← matchEq? (← g.getType) | throwError "invalid goal, expected 'lhs = rhs'."
  -- TODO: do this till fixpoint.
  for h in (← get).hypotheses do
    let x ← mkFreshExprMVar .none
    let xn ← mkFreshExprMVar .none
    let y ← mkFreshExprMVar .none
    let yn ← mkFreshExprMVar .none
    let state ← mkFreshExprMVar .none
    let f := (Expr.const ``read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate' [])
    let result : Option RewriteResult ←
      try
        pure <| some (← g.rewrite (← g.getType) (mkAppN f #[x, xn, y, yn, state, h.proof]) false)
      catch _ =>
        pure <| none
    match result with
    | .none =>
      trace[simp_mem.info] "{crossEmoji} rewrite did not fire"
    | .some r =>
      let mvarId' ← g.replaceTargetEq r.eNew r.eqProof
      -- | TODO: dispatch other goals that occur proof automation.
      Tactic.setGoals <| mvarId' :: r.mvarIds

def addUsefulHypothesis (e : Expr) : SimpMemM Unit := sorry

def proveLegal? (a : MemSpan) : MemLegalProof a := sorry

def proveSubsetRefl? (a : MemSpan) (b : MemSpan) : SimpMemM <| Option (MemSubsetProof a b) := sorry

def proveSubset? (a : MemSpan) (b : MemSpan) : SimpMemM <| Option (MemSubsetProof a b) := sorry
  -- mkFreshMVar.
  -- withLocalContext.

def proveSeparate? (a : MemSpan) (b : MemSpan) : SimpMemM <| Option (MemSubsetProof a b) := sorry

def findReadEqn? (parent : Expr) : Option (ReadEqn parent) := sorry

def findRead? (parent : Expr) : Option (ReadExpr parent) := sorry

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
        -- trace[simp_mem.info] "▶ Found hypotheses: "
        for (i, h) in foundHyps.toList.enum do
          trace[simp_mem.info] m!"{i+1}) {h}"

      withTraceNode `simp_mem.info (fun _ => return m!"Performing Rewrite At Main Goal") do
        SimpMemM.rewrite (← getMainGoal)

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def simpMem (cfg : SimpMemConfig := {}) : TacticM Unit :=
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
