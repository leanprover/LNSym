/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat
-/

/-- define a value `x := val`, and name the hypothesis `heq : x := val` -/
macro "name" heq:ident ":" x:ident " := " val:term : tactic =>
  `(tactic| generalize $heq : $val = $x)
