/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

/-
Experimental method to aggregate state effects using reflection. This is
inspired by `simp_arith`, especially the following files:

`[lean] Init/Data/Nat/Linear.lean`
`[lean] Meta/Tactic/LinearAith/Nat/Basic.lean`
`[lean] Meta/Tactic/LinearAith/Nat/Simp.lean`
-/

import Arm.Exec

namespace ArmConstr

/- We use `Nat`s to refer to all the state variables in our context. -/
abbrev StateVar := Nat

/-- A `GPRVal` can either be a variable or a read from the previous state.

  This is very barebones right now -- for instance, we'd need to support
  `BitVec` operators here.
-/
inductive GPRVal where
  | var (i : Nat)
  | r_gpr (i : BitVec 5)
  deriving DecidableEq, Repr, Inhabited

abbrev StateContext := List ArmState
abbrev GPRValContext := List (BitVec 64)

/--
Context containing all the variables encountered in the problem. The
position of a variable in the context becomes variable name (see, e.g.,
`StateVar`, which is a `Nat`).
-/
structure Context where
  state : StateContext
  gpr : GPRValContext
  deriving Repr, Inhabited

/--
Look up variable `v` in the `StateContext`.
-/
def StateVar.denote (ctx : StateContext) (v : StateVar) : ArmState :=
  match ctx, v with
  | [],      _   => ArmState.default
  | s :: _,  0   => s
  | _ :: ss, i + 1 => denote ss i

/--
Denote `GPRVal v`.

If `v` is a variable then look it up in the `GPRValContext`. Else if `v` is
`r_gpr i`, then look up the `i`th register in `prev_s`.
-/
def GPRVal.denote (ctx : GPRValContext) (v : GPRVal) (prev_s : ArmState)
  : BitVec 64 :=
  match v with
  | var i => go_var ctx i
  | r_gpr i => r (.GPR i) prev_s
  where go_var (ctx : GPRValContext) (v : Nat) : BitVec 64 :=
    match ctx, v with
    | [],      _   => 0#64
    | v0 :: _,  0   => v0
    | _ :: vs, i + 1 => go_var vs i

/--
Datastructure that characterizes all the updates that can be made to an
`ArmState`.
-/
inductive Update where
  -- `i` is a constant.
  | w_gpr (i : BitVec 5) (v : GPRVal)
  -- TODO: Other state components.
  deriving DecidableEq, Repr, Inhabited

/--
Do updates `x` and `y` refer to the same state component?
-/
def Update.regEq (x y : Update) : Bool :=
  match x, y with
  | w_gpr i _, w_gpr j _ => i == j

/--
Is the register index of update `x` less than that of `y`?
-/
def Update.regIndexLt (x y : Update) : Bool :=
  match x, y with
  | w_gpr i _, w_gpr j _ => i < j

/--
Datastructure to represent expressions characterizing the following state
update. Note that we ensure, by construction, that the `writes` are sorted by
the state components.
```
curr_state = writes[prev_state]
```
-/
structure Expr where
   curr_state : StateVar
   prev_state : StateVar
   writes : List Update -- Sorted by the state components.
deriving DecidableEq, Repr, Inhabited

/--
Map updates `us` to state `prev_state` to an `ArmState`.
-/
def Expr.writes.denote (ctx : Context) (us : List Update) (prev_state : StateVar)
  : ArmState :=
  match us with
  | [] => StateVar.denote ctx.state prev_state
  | Update.w_gpr i v :: rest =>
    w (.GPR i)
      (GPRVal.denote ctx.gpr v (StateVar.denote ctx.state prev_state))
      (Expr.writes.denote ctx rest prev_state)

/--
Denote an `Expr e` to a `Prop` corresponding to `curr_state = writes[prev_state]`.
-/
def Expr.denote (ctx : Context) (e : Expr) : Prop :=
  StateVar.denote ctx.state e.curr_state =
  Expr.writes.denote ctx e.writes e.prev_state

/--
Return a `Prop` corresponding to `e1 = e2`.
-/
def Expr.denote_eq (ctx : Context) (e1 e2 : Expr) : Prop :=
  StateVar.denote ctx.state e1.prev_state = StateVar.denote ctx.state e2.prev_state ∧
  StateVar.denote ctx.state e1.curr_state = StateVar.denote ctx.state e2.curr_state ∧
  Expr.denote ctx e1 ∧
  Expr.denote ctx e2

abbrev Exprs := List Expr

/--
Denote each expression in `es` using `Expr.denote`.
-/
def Exprs.denote (ctx : Context) (es : Exprs) : Prop :=
  match es with
  | [] => True
  | u :: rest => Expr.denote ctx u ∧ Exprs.denote ctx rest

def Expr.default : Expr :=
  { prev_state := 0, curr_state := 0, writes := [] }

def Update.insertSorted (es : List Update) (u : Update) : List Update :=
  match es with
  | [] => [u]
  | e :: rest =>
    if u.regIndexLt e then
      -- `u` does not appear in `es` (given that `es` is sorted), so we retain
      -- this update.
      u :: es
    else if u.regEq e then
      -- We overwrite `e` with `x`.
      u :: rest
    else
      e :: (insertSorted rest u)

/--
Resolve any reads in `u` by looking it up in `es`.
-/
def Update.resolveRead (es : List Update) (u : Update) : Update :=
  match u with
  | .w_gpr _ (.var _) => u
  | .w_gpr i (.r_gpr gpr_idx) =>
    let ans := go gpr_idx es
    .w_gpr i ans
  where go (gpr_idx : BitVec 5) (es : List Update) : GPRVal :=
    match es with
    | [] => .r_gpr gpr_idx
    | (.w_gpr i v) :: rest =>
      if i == gpr_idx then v else go gpr_idx rest

/--
Resolve any reads in each of `us` by looking them up in `es`.
-/
def Update.resolveReads (es us : List Update) : List Update :=
  match us with
  | [] => []
  | u :: rest =>
    (Update.resolveRead es u) :: resolveReads es rest

/--
Aggregate `e` and `u`, assuming `u` follows `e`.
-/
def Expr.aggregate1 (e u : Expr) : Expr :=
  if e.curr_state == u.prev_state then
    let u_resolved_writes := Update.resolveReads e.writes u.writes
    { prev_state := e.prev_state,
      curr_state := u.curr_state,
      writes := go e.writes u_resolved_writes }
  else
    -- We cannot aggregate two non-consecutive states, so we return the original
    -- StateUpdate here.
    -- TODO: We should probably throw an error here.
    e
 where go (es us : List Update) : List Update :=
  match es, us with
  | [], us => us
  | es, [] => es
  | es, u :: rest_us =>
    go (Update.insertSorted es u) rest_us

/--
info: { curr_state := 2,
  prev_state := 0,
  writes := [ArmConstr.Update.w_gpr 0x00#5 (ArmConstr.GPRVal.var 1),
             ArmConstr.Update.w_gpr 0x01#5 (ArmConstr.GPRVal.var 1),
             ArmConstr.Update.w_gpr 0x02#5 (ArmConstr.GPRVal.var 3)] }
-/
#guard_msgs in
open Expr Update in
#eval Expr.aggregate1
        { prev_state := 0,
          curr_state := 1,
          writes := [w_gpr 0#5 (.var 1), w_gpr 1#5 (.var 3)] }
        { prev_state := 1,
          curr_state := 2,
          writes := [w_gpr 1#5 (.var 1), w_gpr 2#5 (.r_gpr 1)] }

/--
Aggregate `es` onto `init`.
Earlier updates appear first in `es`, and of course, `es` follows `init`.
-/
def Expr.aggregate (init : Expr) (es : Exprs) : Expr :=
  match es with
  | [] => init
  | e :: rest => aggregate (aggregate1 init e) rest

open Expr Update in
/--
info: { curr_state := 2,
  prev_state := 0,
  writes := [ArmConstr.Update.w_gpr 0x01#5 (ArmConstr.GPRVal.var 1),
             ArmConstr.Update.w_gpr 0x02#5 (ArmConstr.GPRVal.var 2),
             ArmConstr.Update.w_gpr 0x03#5 (ArmConstr.GPRVal.var 3)] }
-/
#guard_msgs in
#eval Expr.aggregate
        Expr.default
        [
          { prev_state := 0,
            curr_state := 1,
            writes := [w_gpr 1#5 (.var 1),
                       w_gpr 3#5 (.var 3)] },
          { prev_state := 1,
            curr_state := 2,
            writes := [w_gpr 1#5 (.var 1),
                       w_gpr 2#5 (.var 2)] }
        ]

/-- Does aggregating `updates` over `init` yield `final`? -/
def Expr.isAggregated (init : Expr) (updates : Exprs) (final : Expr) : Bool :=
  final == aggregate init updates

theorem Expr.eq_true_of_isValid (ctx : Context) (init final : Expr) (updates : Exprs) :
  (Expr.isAggregated init updates final) →
  Expr.denote ctx init ∧ Exprs.denote ctx updates → (Expr.denote ctx final) := by
  sorry

-------------------------------------------------------------------------------

-- Tests

#time
open Expr Update in
theorem completely_shadowed_updates
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 s0))
  (h_s2 : s2 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 s1)) :
  /-
  (NOTE) Replacing the RHS with `xxxx` gives the following type mismatch, which
  can help in doing ACL2-style wormhole abstraction.

  type mismatch
  this (Eq.refl s0) h_s1 h_s2
  has type
    denote { state := [s0, s1, s2], gpr := [x0, x1] }
      { prev_state := 0, curr_state := 2, writes := [w_gpr (0#5) 0, w_gpr (1#5) 1] } : Prop
  but is expected to have type
    s2 = xxxx : Prop
  -/
  s2 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 s0) := by
  have := (Expr.eq_true_of_isValid { state := [s0, s1, s2],
                                     gpr := [x0, x1] }
          -- init
          { prev_state := 0, curr_state := 0, writes := []}
          -- final
          { prev_state := 0, curr_state := 2, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] }
          -- updates
          [ { prev_state := 0, curr_state := 1, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] },
            { prev_state := 1, curr_state := 2, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] } ]
            (Eq.refl true))
  simp only [Exprs.denote, and_true, and_imp] at this
  exact this (Eq.refl s0) h_s1 h_s2
  done

open Expr Update in
theorem partially_shadowed_and_new_updates
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) old_x1 s0))
  /-
  (NOTE) if any instructions updates are not sorted, as is the case in `h_s2`
  below, then we run into a problem because the writes in `Expr` are sorted.
  `(h_s2 : s2 = w (.GPR 3#5) x3 (w (.GPR 1#5) x1 s1))`
  `{ prev_state := 1, curr_state := 2, writes := [w_gpr 1#5 2, w_gpr 3#5 3] }`
  This means that
  `exact this (Eq.refl s0) h_s1 h_s2`
  will result in a type mismatch.

  Therefore, for convenience, we ought to enforce that instruction updates like
  `h_s2` are sorted in the preprocessing step.
  -/
  (h_s2 : s2 = w (.GPR 1#5) x1 (w (.GPR 3#5) x3 s1)) :
  s2 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 3#5) x3 s0)) := by
  have := (Expr.eq_true_of_isValid { state := [s0, s1, s2],
                                     gpr := [x0, old_x1, x1, x3] }
          -- init
          { prev_state := 0, curr_state := 0, writes := []}
          -- final
          { prev_state := 0, curr_state := 2, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 2), w_gpr 3#5 (.var 3)] }
          -- updates
          [ { prev_state := 0, curr_state := 1, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] },
            { prev_state := 1, curr_state := 2, writes := [w_gpr 1#5 (.var 2), w_gpr 3#5 (.var 3)] } ]
            (Eq.refl true))
  simp only [Exprs.denote, and_true, and_imp] at this
  exact this (Eq.refl s0) h_s1 h_s2
  done

/--
info: true
-/
#guard_msgs in
#eval
 Expr.isAggregated
      -- init
      { curr_state := 0, prev_state := 0, writes := [] }
      -- updates
     [{ curr_state := 1, prev_state := 0, writes := [.w_gpr (0#5) (GPRVal.var 0), .w_gpr (1#5) (GPRVal.var 1)] },
      { curr_state := 2, prev_state := 1, writes := [.w_gpr (1#5) (GPRVal.var 2), .w_gpr (3#5) (GPRVal.r_gpr 1)] }]
    { curr_state := 2, prev_state := 0,
      writes := [.w_gpr (0#5) (GPRVal.var 0), .w_gpr (1#5) (GPRVal.var 2), .w_gpr (3#5) (GPRVal.var 1)] }

#time
open Expr Update in
theorem read_from_prev_update_test1
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) old_x1 s0))
  (h_s2 : s2 = w (.GPR 1#5) x1 (w (.GPR 3#5) (r (.GPR 1#5) s1) s1)) :
  s2 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 3#5) old_x1 s0)) := by
  have := (Expr.eq_true_of_isValid { state := [s0, s1, s2],
                                     gpr := [x0, old_x1, x1] }
          -- init
          { prev_state := 0, curr_state := 0, writes := []}
          -- final
          { prev_state := 0, curr_state := 2,
            writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 2), w_gpr 3#5 (.var 1)] }
          -- updates
          [ { prev_state := 0, curr_state := 1, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] },
            { prev_state := 1, curr_state := 2, writes := [w_gpr 1#5 (.var 2), w_gpr 3#5 (.r_gpr 1)] } ]
            (Eq.refl true))
  simp only [Exprs.denote, and_true, and_imp] at this
  exact this (Eq.refl s0) h_s1 h_s2
  done

#time
open Expr Update in
theorem read_from_prev_update_test2 (s0 s1 s2 : ArmState)
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) old_x1 s0))
  (h_s2 : s2 = w (.GPR 1#5) x1 (w (.GPR 3#5) (r (.GPR 5#5) s1) s1)) :
  s2 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 3#5) (r (.GPR 5#5) s0) s0)) := by
  have := (Expr.eq_true_of_isValid { state := [s0, s1, s2],
                                     gpr := [x0, old_x1, x1] }
          -- init
          { prev_state := 0, curr_state := 0, writes := []}
          -- final
          { prev_state := 0, curr_state := 2,
            writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 2), w_gpr 3#5 (.r_gpr 5#5)] }
          -- updates
          [ { prev_state := 0, curr_state := 1,
              writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] },
            { prev_state := 1, curr_state := 2,
              writes := [w_gpr 1#5 (.var 2), w_gpr 3#5 (.r_gpr 5#5)] } ]
            (Eq.refl true))
  simp only [Exprs.denote, and_true, and_imp] at this
  exact this (Eq.refl s0) h_s1 h_s2
  done

end ArmConstr
