/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat
-/
import Lean

open Lean Elab Meta Tactic in
/-- `clear_named [n₁, n₂, ...]` clear all inaccessible names that have
*any* one of `n₁, n2, ...` as prefixes. -/
elab "clear_named" "[" names:(ident),* "]": tactic =>  do
  withMainContext do
    for hyp in (← getLCtx) do
      -- trace[debug] "name: {hyp.userName}"
      for name in names.getElems do
        if name.getId.toString.isPrefixOf hyp.userName.toString then
          replaceMainGoal [← (← getMainGoal).clear hyp.fvarId]
          continue
