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

/- # Features Wanted List
- `at` syntax for `simp_mem at h₁ h₂ ⊢`.
-/
open Lean Meta Elab Tactic

namespace SeparateAutomation

structure SimpMemConfig where

/-- Context for the `SimpMemM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `simp_mem`. -/
  cfg : SimpMemConfig

def Context.init (cfg : SimpMemConfig) : Context where
  cfg := cfg

inductive Hypothesis
| separate (h : Expr) (a na b nb : Expr)
| subset (h : Expr)

def Hypothesis.expr : Hypothesis → Expr
| .separate h .. => h
| .subset h .. => h

instance : ToMessageData Hypothesis where
  toMessageData
  | .subset h => toMessageData h
  | .separate h _a _na _b _nb => toMessageData h

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
def processHypothesis (h : Expr) : MetaM (Option Hypothesis) := do
  -- trace[simp_mem] "processing hyp '{(← inferType h)}'"
  let ht ← inferType h
  trace[simp_mem.info] "{processingEmoji} Processing '{h}' : '{toString ht}'"
  match_expr ht with
  | mem_separate' a ha b hb => return .some (.separate h a ha b hb)
  | _ => return .none

/--
info: read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat}
  {state : ArmState} (hsep : mem_separate' x xn y yn) (val : BitVec (yn * 8)) :
  read_mem_bytes xn x (write_mem_bytes yn y val state) = read_mem_bytes xn x state
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
        pure <| some (← g.rewrite (← g.getType) (mkAppN f #[x, xn, y, yn, state, h.expr]) false)
      catch _ =>
        pure <| none
    match result with
    | .none =>
      trace[simp_mem.info] "{crossEmoji} rewrite did not fire"
    | .some r =>
      let mvarId' ← g.replaceTargetEq r.eNew r.eqProof
      -- | TODO: dispatch other goals that occur proof automation.
      Tactic.setGoals <| mvarId' :: r.mvarIds

def SimpMemM.analyzeLoop : SimpMemM Unit := do
    (← getMainGoal).withContext do
      let hyps := (← getLocalHyps)
      trace[simp_mem] "analyzing {hyps.size} hypotheses:\n{← hyps.mapM (liftMetaM ∘ inferType)}"
      for h in hyps do
        if let some hyp ← processHypothesis h then
          trace[simp_mem.info] "{checkEmoji} Found '{h}'"
          SimpMemM.addHypothesis hyp
        else
          trace[simp_mem.info] "{crossEmoji} Rejecting '{h}'"
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
