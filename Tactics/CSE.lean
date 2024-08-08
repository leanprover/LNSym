/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

This file contains an implementation of a common subexpression elimination pass,
used to simplify goal states.
-/
import Lean
import Tactics.Attr
open Lean Elab Tactic Expr Meta



/-! ### Common Subexpression Eliminiation Tactic

cse ⊢
cse ⊢ h h' -- will use all expressions to compute thresholds.

#### TODO

- don't generalize over implicits.
- don't generalize over stuff that's hidden by notation?

#### Algorithm:

- step 1: collect statistics on (sub) expression occurrence in the target expression.
- step 2: once again, working bottom up, call `generalize` for each of these, generating appropriate generalize names.
- step 3: done?
-/


namespace Tactic.CSE

structure CSEConfig where


structure State where
  /--
  a mapping from the canonical normal form of an expression `expr` to its number of occurrences.
  -/
  canon2count : HashMap Expr Nat := {}

abbrev CSEM := StateRefT State (ReaderT CSEConfig TacticM)

def CSEM.run (val : CSEM α) (config : CSEConfig) : TacticM α :=
   val.run' {} |>.run config


def cseImpl : CSEM Unit := return ()

def cseWithConfig (cfg : CSEConfig) : TacticM Unit := do
  trace[Tactic.cse.info] m!"running CSE"
  CSEM.run cseImpl cfg

open Lean Elab Tactic Parser.Tactic

/-- The `cse` tactic, for performing common subexpression elimination of goal states. -/
def cseTactic (cfg : CSEConfig) : TacticM Unit := cseWithConfig cfg

/-- The `omega` tactic, for resolving integer and natural linear arithmetic problems. This
`TacticM Unit` frontend with default configuration can be used as an Aesop rule, for example via
the tactic call `aesop (add 50% tactic Lean.Omega.omegaDefault)`. -/
def cseTacticDefault : TacticM Unit := cseWithConfig {}

end Tactic.CSE

/--
Allow elaboration of `CseConfig` arguments to tactics.
-/
declare_config_elab elabCSEConfig Tactic.CSE.CSEConfig

/--
common subexpression elimination.
-/
syntax (name := cse) "cse" (Lean.Parser.Tactic.config)? : tactic

@[tactic cse]
def evalCse : Tactic := fun
  | `(tactic| cse $[$cfg]?) => do
    let cfg ← elabCSEConfig (mkOptionalNode cfg)
    Tactic.CSE.cseTactic cfg
  | _ => throwUnsupportedSyntax
