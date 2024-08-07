/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

This file contains an implementation of a common subexpression elimination pass,
used to simplify goal states.
-/
import Lean
import Arm.Attr
open Lean Elab Tactic Expr Meta
open BitVec

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



