/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Tactic.BVDecide

/-!
`bv_decide`'s enum preprocessing realizes auxiliary declarations such as
`PUnit.enumToBitVec` in whichever module first needs them. As of Lean v4.34
(still present in v4.35), when two modules that do not import one another
both realize the same declaration from a `theorem`, any module importing both
fails with "environment already contains 'PUnit.enumToBitVec'".

Work around this by realizing them once, in the module that defines the enum
(or, for core types such as `PUnit`, here: every `bv_decide` user imports this
module via `Arm.BitVec`); the later realizations then find and reuse the
imported declarations. See `bv_decide_realize_PFlag_enum` in `Arm/State.lean`.
-/

private theorem bv_decide_realize_PUnit_enum (x y : PUnit) (a : BitVec 1) (_h : x = y) :
    a &&& a = a := by
  bv_decide
