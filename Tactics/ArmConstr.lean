/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

/-
Experimental method to aggregate state effects using reflection.

In LNSym, we already have a language that describes reads from and writes to the
`ArmState` using functions `r` and `w` respectively (we ignore memory reads and
writes at this point). We reflect precisely these two functions, as well as arbitrary
bitvector expressions for register updates to the `ArmState`.

This is inspired by `simp_arith`, especially the following files:

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
  us.map (Update.resolveRead es)

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

/-- TODO: we're probably missing a well-formedness hyp. about the `ctx` here. -/
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

open Expr Update in
/--
info: { curr_state := 30,
  prev_state := 0,
  writes := [ArmConstr.Update.w_gpr 0x01#5 (ArmConstr.GPRVal.var 52),
             ArmConstr.Update.w_gpr 0x02#5 (ArmConstr.GPRVal.var 51),
             ArmConstr.Update.w_gpr 0x03#5 (ArmConstr.GPRVal.var 53),
             ArmConstr.Update.w_gpr 0x04#5 (ArmConstr.GPRVal.var 76),
             ArmConstr.Update.w_gpr 0x05#5 (ArmConstr.GPRVal.var 81),
             ArmConstr.Update.w_gpr 0x06#5 (ArmConstr.GPRVal.var 74),
             ArmConstr.Update.w_gpr 0x07#5 (ArmConstr.GPRVal.var 73),
             ArmConstr.Update.w_gpr 0x08#5 (ArmConstr.GPRVal.var 87),
             ArmConstr.Update.w_gpr 0x09#5 (ArmConstr.GPRVal.var 86),
             ArmConstr.Update.w_gpr 0x0a#5 (ArmConstr.GPRVal.var 85),
             ArmConstr.Update.w_gpr 0x0b#5 (ArmConstr.GPRVal.var 84),
             ArmConstr.Update.w_gpr 0x0c#5 (ArmConstr.GPRVal.var 61),
             ArmConstr.Update.w_gpr 0x0d#5 (ArmConstr.GPRVal.var 83),
             ArmConstr.Update.w_gpr 0x0e#5 (ArmConstr.GPRVal.var 82),
             ArmConstr.Update.w_gpr 0x0f#5 (ArmConstr.GPRVal.var 19),
             ArmConstr.Update.w_gpr 0x10#5 (ArmConstr.GPRVal.var 80),
             ArmConstr.Update.w_gpr 0x11#5 (ArmConstr.GPRVal.var 79),
             ArmConstr.Update.w_gpr 0x12#5 (ArmConstr.GPRVal.var 78),
             ArmConstr.Update.w_gpr 0x13#5 (ArmConstr.GPRVal.var 77),
             ArmConstr.Update.w_gpr 0x14#5 (ArmConstr.GPRVal.var 44),
             ArmConstr.Update.w_gpr 0x15#5 (ArmConstr.GPRVal.var 43),
             ArmConstr.Update.w_gpr 0x16#5 (ArmConstr.GPRVal.var 42),
             ArmConstr.Update.w_gpr 0x17#5 (ArmConstr.GPRVal.var 41),
             ArmConstr.Update.w_gpr 0x18#5 (ArmConstr.GPRVal.var 3),
             ArmConstr.Update.w_gpr 0x19#5 (ArmConstr.GPRVal.var 2),
             ArmConstr.Update.w_gpr 0x1a#5 (ArmConstr.GPRVal.var 1),
             ArmConstr.Update.w_gpr 0x1b#5 (ArmConstr.GPRVal.var 0),
             ArmConstr.Update.w_gpr 0x1c#5 (ArmConstr.GPRVal.var 60),
             ArmConstr.Update.w_gpr 0x1d#5 (ArmConstr.GPRVal.var 59),
             ArmConstr.Update.w_gpr 0x1e#5 (ArmConstr.GPRVal.var 58),
             ArmConstr.Update.w_gpr 0x1f#5 (ArmConstr.GPRVal.var 57)] }
-/
#guard_msgs in
#eval Expr.aggregate
      { prev_state := 0, curr_state := 0, writes := []}
      [{ curr_state := 1, prev_state := 0,
          writes :=
            [w_gpr (23#5) (GPRVal.var 4), w_gpr (24#5) (GPRVal.var 3), w_gpr (25#5) (GPRVal.var 2),
              w_gpr (26#5) (GPRVal.var 1), w_gpr (27#5) (GPRVal.var 0)] },
        { curr_state := 2, prev_state := 1, writes := [w_gpr (2#5) (GPRVal.var 6), w_gpr (3#5) (GPRVal.var 5)] },
        { curr_state := 3, prev_state := 2,
          writes :=
            [w_gpr (28#5) (GPRVal.var 10), w_gpr (29#5) (GPRVal.var 9), w_gpr (30#5) (GPRVal.var 8),
              w_gpr (31#5) (GPRVal.var 7)] },
        { curr_state := 4, prev_state := 3,
          writes :=
            [w_gpr (17#5) (GPRVal.var 14), w_gpr (18#5) (GPRVal.var 13), w_gpr (19#5) (GPRVal.var 12),
              w_gpr (20#5) (GPRVal.var 11)] },
        { curr_state := 5, prev_state := 4, writes := [w_gpr (15#5) (GPRVal.var 16), w_gpr (16#5) (GPRVal.var 15)] },
        { curr_state := 6, prev_state := 5, writes := [w_gpr (30#5) (GPRVal.var 17)] },
        { curr_state := 7, prev_state := 6,
          writes :=
            [w_gpr (12#5) (GPRVal.var 22), w_gpr (13#5) (GPRVal.var 21), w_gpr (14#5) (GPRVal.var 20),
              w_gpr (15#5) (GPRVal.var 19), w_gpr (16#5) (GPRVal.var 18)] },
        { curr_state := 8, prev_state := 7,
          writes :=
            [w_gpr (8#5) (GPRVal.var 27), w_gpr (9#5) (GPRVal.var 26), w_gpr (10#5) (GPRVal.var 25),
              w_gpr (11#5) (GPRVal.var 24), w_gpr (12#5) (GPRVal.var 23)] },
        { curr_state := 9, prev_state := 8,
          writes := [w_gpr (28#5) (GPRVal.var 30), w_gpr (29#5) (GPRVal.var 29), w_gpr (30#5) (GPRVal.var 28)] },
        { curr_state := 10, prev_state := 9, writes := [w_gpr (21#5) (GPRVal.var 31)] },
        { curr_state := 11, prev_state := 10,
          writes :=
            [w_gpr (18#5) (GPRVal.var 36), w_gpr (19#5) (GPRVal.var 35), w_gpr (20#5) (GPRVal.var 34),
              w_gpr (21#5) (GPRVal.var 33), w_gpr (22#5) (GPRVal.var 32)] },
        { curr_state := 12, prev_state := 11,
          writes :=
            [w_gpr (18#5) (GPRVal.var 40), w_gpr (19#5) (GPRVal.var 39), w_gpr (20#5) (GPRVal.var 38),
              w_gpr (21#5) (GPRVal.var 37)] },
        { curr_state := 13, prev_state := 12,
          writes :=
            [w_gpr (20#5) (GPRVal.var 44), w_gpr (21#5) (GPRVal.var 43), w_gpr (22#5) (GPRVal.var 42),
              w_gpr (23#5) (GPRVal.var 41)] },
        { curr_state := 14, prev_state := 13, writes := [w_gpr (17#5) (GPRVal.var 45)] },
        { curr_state := 15, prev_state := 14, writes := [w_gpr (14#5) (GPRVal.var 46)] },
        { curr_state := 16, prev_state := 15, writes := [w_gpr (16#5) (GPRVal.var 47)] },
        { curr_state := 17, prev_state := 16,
          writes :=
            [w_gpr (1#5) (GPRVal.var 52), w_gpr (2#5) (GPRVal.var 51), w_gpr (3#5) (GPRVal.var 50),
              w_gpr (4#5) (GPRVal.var 49), w_gpr (5#5) (GPRVal.var 48)] },
        { curr_state := 18, prev_state := 17, writes := [w_gpr (3#5) (GPRVal.var 53)] },
        { curr_state := 19, prev_state := 18, writes := [w_gpr (8#5) (GPRVal.var 54)] },
        { curr_state := 20, prev_state := 19, writes := [w_gpr (5#5) (GPRVal.var 55)] },
        { curr_state := 21, prev_state := 20, writes := [w_gpr (9#5) (GPRVal.var 56)] },
        { curr_state := 22, prev_state := 21,
          writes :=
            [w_gpr (28#5) (GPRVal.var 60), w_gpr (29#5) (GPRVal.var 59), w_gpr (30#5) (GPRVal.var 58),
              w_gpr (31#5) (GPRVal.var 57)] },
        { curr_state := 23, prev_state := 22,
          writes :=
            [w_gpr (8#5) (GPRVal.var 65), w_gpr (9#5) (GPRVal.var 64), w_gpr (10#5) (GPRVal.var 63),
              w_gpr (11#5) (GPRVal.var 62), w_gpr (12#5) (GPRVal.var 61)] },
        { curr_state := 24, prev_state := 23,
          writes :=
            [w_gpr (7#5) (GPRVal.var 70), w_gpr (8#5) (GPRVal.var 69), w_gpr (9#5) (GPRVal.var 68),
              w_gpr (10#5) (GPRVal.var 67), w_gpr (11#5) (GPRVal.var 66)] },
        { curr_state := 25, prev_state := 24, writes := [w_gpr (5#5) (GPRVal.var 72), w_gpr (6#5) (GPRVal.var 71)] },
        { curr_state := 26, prev_state := 25,
          writes :=
            [w_gpr (4#5) (GPRVal.var 76), w_gpr (5#5) (GPRVal.var 75), w_gpr (6#5) (GPRVal.var 74),
              w_gpr (7#5) (GPRVal.var 73)] },
        { curr_state := 27, prev_state := 26,
          writes :=
            [w_gpr (16#5) (GPRVal.var 80), w_gpr (17#5) (GPRVal.var 79), w_gpr (18#5) (GPRVal.var 78),
              w_gpr (19#5) (GPRVal.var 77)] },
        { curr_state := 28, prev_state := 27, writes := [w_gpr (5#5) (GPRVal.var 81)] },
        { curr_state := 29, prev_state := 28, writes := [w_gpr (13#5) (GPRVal.var 83), w_gpr (14#5) (GPRVal.var 82)] },
        { curr_state := 30, prev_state := 29,
          writes :=
            [w_gpr (8#5) (GPRVal.var 87), w_gpr (9#5) (GPRVal.var 86), w_gpr (10#5) (GPRVal.var 85),
              w_gpr (11#5) (GPRVal.var 84)] }]

#time
open Expr Update in
theorem test_30_steps (s0 : ArmState)
  (h_step_1 : s1 = (w (.GPR 23#5) val4 (w (.GPR 24#5) val3 (w (.GPR 25#5) val2 (w (.GPR 26#5) val1 (w (.GPR 27#5) val0 s0))))))
  (h_step_2 : s2 = (w (.GPR 2#5) val6 (w (.GPR 3#5) val5 s1)))
  (h_step_3 : s3 = (w (.GPR 28#5) val10 (w (.GPR 29#5) val9 (w (.GPR 30#5) val8 (w (.GPR 31#5) val7 s2)))))
  (h_step_4 : s4 = (w (.GPR 17#5) val14 (w (.GPR 18#5) val13 (w (.GPR 19#5) val12 (w (.GPR 20#5) val11 s3)))))
  (h_step_5 : s5 = (w (.GPR 15#5) val16 (w (.GPR 16#5) val15 s4)))
  (h_step_6 : s6 = (w (.GPR 30#5) val17 s5))
  (h_step_7 : s7 = (w (.GPR 12#5) val22 (w (.GPR 13#5) val21 (w (.GPR 14#5) val20 (w (.GPR 15#5) val19 (w (.GPR 16#5) val18 s6))))))
  (h_step_8 : s8 = (w (.GPR 8#5) val27 (w (.GPR 9#5) val26 (w (.GPR 10#5) val25 (w (.GPR 11#5) val24 (w (.GPR 12#5) val23 s7))))))
  (h_step_9 : s9 = (w (.GPR 28#5) val30 (w (.GPR 29#5) val29 (w (.GPR 30#5) val28 s8))))
  (h_step_10 : s10 = (w (.GPR 21#5) val31 s9))
  (h_step_11 : s11 = (w (.GPR 18#5) val36 (w (.GPR 19#5) val35 (w (.GPR 20#5) val34 (w (.GPR 21#5) val33 (w (.GPR 22#5) val32 s10))))))
  (h_step_12 : s12 = (w (.GPR 18#5) val40 (w (.GPR 19#5) val39 (w (.GPR 20#5) val38 (w (.GPR 21#5) val37 s11)))))
  (h_step_13 : s13 = (w (.GPR 20#5) val44 (w (.GPR 21#5) val43 (w (.GPR 22#5) val42 (w (.GPR 23#5) val41 s12)))))
  (h_step_14 : s14 = (w (.GPR 17#5) val45 s13))
  (h_step_15 : s15 = (w (.GPR 14#5) val46 s14))
  (h_step_16 : s16 = (w (.GPR 16#5) val47 s15))
  (h_step_17 : s17 = (w (.GPR 1#5) val52 (w (.GPR 2#5) val51 (w (.GPR 3#5) val50 (w (.GPR 4#5) val49 (w (.GPR 5#5) val48 s16))))))
  (h_step_18 : s18 = (w (.GPR 3#5) val53 s17))
  (h_step_19 : s19 = (w (.GPR 8#5) val54 s18))
  (h_step_20 : s20 = (w (.GPR 5#5) val55 s19))
  (h_step_21 : s21 = (w (.GPR 9#5) val56 s20))
  (h_step_22 : s22 = (w (.GPR 28#5) val60 (w (.GPR 29#5) val59 (w (.GPR 30#5) val58 (w (.GPR 31#5) val57 s21)))))
  (h_step_23 : s23 = (w (.GPR 8#5) val65 (w (.GPR 9#5) val64 (w (.GPR 10#5) val63 (w (.GPR 11#5) val62 (w (.GPR 12#5) val61 s22))))))
  (h_step_24 : s24 = (w (.GPR 7#5) val70 (w (.GPR 8#5) val69 (w (.GPR 9#5) val68 (w (.GPR 10#5) val67 (w (.GPR 11#5) val66 s23))))))
  (h_step_25 : s25 = (w (.GPR 5#5) val72 (w (.GPR 6#5) val71 s24)))
  (h_step_26 : s26 = (w (.GPR 4#5) val76 (w (.GPR 5#5) val75 (w (.GPR 6#5) val74 (w (.GPR 7#5) val73 s25)))))
  (h_step_27 : s27 = (w (.GPR 16#5) val80 (w (.GPR 17#5) val79 (w (.GPR 18#5) val78 (w (.GPR 19#5) val77 s26)))))
  (h_step_28 : s28 = (w (.GPR 5#5) val81 s27))
  (h_step_29 : s29 = (w (.GPR 13#5) val83 (w (.GPR 14#5) val82 s28)))
  (h_step_30 : s30 = (w (.GPR 8#5) val87 (w (.GPR 9#5) val86 (w (.GPR 10#5) val85 (w (.GPR 11#5) val84 s29))))) :
  s30 = (w (.GPR 0x01#5) val52 (w (.GPR 0x02#5) val51 (w (.GPR 0x03#5) val53 (w (.GPR 0x04#5) val76 (w (.GPR 0x05#5) val81 (w (.GPR 0x06#5) val74 (w (.GPR 0x07#5) val73 (w (.GPR 0x08#5) val87 (w (.GPR 0x09#5) val86 (w (.GPR 0x0a#5) val85 (w (.GPR 0x0b#5) val84 (w (.GPR 0x0c#5) val61 (w (.GPR 0x0d#5) val83 (w (.GPR 0x0e#5) val82 (w (.GPR 0x0f#5) val19 (w (.GPR 0x10#5) val80 (w (.GPR 0x11#5) val79 (w (.GPR 0x12#5) val78 (w (.GPR 0x13#5) val77 (w (.GPR 0x14#5) val44 (w (.GPR 0x15#5) val43 (w (.GPR 0x16#5) val42 (w (.GPR 0x17#5) val41 (w (.GPR 0x18#5) val3 (w (.GPR 0x19#5) val2 (w (.GPR 0x1a#5) val1 (w (.GPR 0x1b#5) val0 (w (.GPR 0x1c#5) val60 (w (.GPR 0x1d#5) val59 (w (.GPR 0x1e#5) val58 (w (.GPR 0x1f#5) val57 s0)))))))))))))))))))))))))))))))
  := by
  have :=
    (Expr.eq_true_of_isValid { state := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
                                         s11, s12, s13, s14, s15, s16, s17, s18, s19,
                                         s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30],
                               gpr := [val0, val1, val2, val3, val4, val5, val6, val7, val8, val9, val10,
                                       val11, val12, val13, val14, val15, val16, val17, val18, val19, val20,
                                       val21, val22, val23, val24, val25, val26, val27, val28, val29, val30,
                                       val31, val32, val33, val34, val35, val36, val37, val38, val39, val40,
                                       val41, val42, val43, val44, val45, val46, val47, val48, val49, val50,
                                       val51, val52, val53, val54, val55, val56, val57, val58, val59, val60,
                                       val61, val62, val63, val64, val65, val66, val67, val68, val69, val70,
                                       val71, val72, val73, val74, val75, val76, val77, val78, val79, val80,
                                       val81, val82, val83, val84, val85, val86, val87] }
            -- init
            { prev_state := 0, curr_state := 0, writes := []}
            -- final
            { curr_state := 30,
              prev_state := 0,
              writes := [w_gpr 0x01#5 (.var 52),
                         w_gpr 0x02#5 (.var 51),
                         w_gpr 0x03#5 (.var 53),
                         w_gpr 0x04#5 (.var 76),
                         w_gpr 0x05#5 (.var 81),
                         w_gpr 0x06#5 (.var 74),
                         w_gpr 0x07#5 (.var 73),
                         w_gpr 0x08#5 (.var 87),
                         w_gpr 0x09#5 (.var 86),
                         w_gpr 0x0a#5 (.var 85),
                         w_gpr 0x0b#5 (.var 84),
                         w_gpr 0x0c#5 (.var 61),
                         w_gpr 0x0d#5 (.var 83),
                         w_gpr 0x0e#5 (.var 82),
                         w_gpr 0x0f#5 (.var 19),
                         w_gpr 0x10#5 (.var 80),
                         w_gpr 0x11#5 (.var 79),
                         w_gpr 0x12#5 (.var 78),
                         w_gpr 0x13#5 (.var 77),
                         w_gpr 0x14#5 (.var 44),
                         w_gpr 0x15#5 (.var 43),
                         w_gpr 0x16#5 (.var 42),
                         w_gpr 0x17#5 (.var 41),
                         w_gpr 0x18#5 (.var 3),
                         w_gpr 0x19#5 (.var 2),
                         w_gpr 0x1a#5 (.var 1),
                         w_gpr 0x1b#5 (.var 0),
                         w_gpr 0x1c#5 (.var 60),
                         w_gpr 0x1d#5 (.var 59),
                         w_gpr 0x1e#5 (.var 58),
                         w_gpr 0x1f#5 (.var 57)] }
            -- updates
            [
              { curr_state := 1, prev_state := 0, writes := [w_gpr 23#5 (.var 4), w_gpr 24#5 (.var 3), w_gpr 25#5 (.var 2), w_gpr 26#5 (.var 1), w_gpr 27#5 (.var 0), ] },
              { curr_state := 2, prev_state := 1, writes := [w_gpr 2#5 (.var 6), w_gpr 3#5 (.var 5), ] },
              { curr_state := 3, prev_state := 2, writes := [w_gpr 28#5 (.var 10), w_gpr 29#5 (.var 9), w_gpr 30#5 (.var 8), w_gpr 31#5 (.var 7), ] },
              { curr_state := 4, prev_state := 3, writes := [w_gpr 17#5 (.var 14), w_gpr 18#5 (.var 13), w_gpr 19#5 (.var 12), w_gpr 20#5 (.var 11), ] },
              { curr_state := 5, prev_state := 4, writes := [w_gpr 15#5 (.var 16), w_gpr 16#5 (.var 15), ] },
              { curr_state := 6, prev_state := 5, writes := [w_gpr 30#5 (.var 17), ] },
              { curr_state := 7, prev_state := 6, writes := [w_gpr 12#5 (.var 22), w_gpr 13#5 (.var 21), w_gpr 14#5 (.var 20), w_gpr 15#5 (.var 19), w_gpr 16#5 (.var 18), ] },
              { curr_state := 8, prev_state := 7, writes := [w_gpr 8#5 (.var 27), w_gpr 9#5 (.var 26), w_gpr 10#5 (.var 25), w_gpr 11#5 (.var 24), w_gpr 12#5 (.var 23), ] },
              { curr_state := 9, prev_state := 8, writes := [w_gpr 28#5 (.var 30), w_gpr 29#5 (.var 29), w_gpr 30#5 (.var 28), ] },
              { curr_state := 10, prev_state := 9, writes := [w_gpr 21#5 (.var 31), ] },
              { curr_state := 11, prev_state := 10, writes := [w_gpr 18#5 (.var 36), w_gpr 19#5 (.var 35), w_gpr 20#5 (.var 34), w_gpr 21#5 (.var 33), w_gpr 22#5 (.var 32), ] },
              { curr_state := 12, prev_state := 11, writes := [w_gpr 18#5 (.var 40), w_gpr 19#5 (.var 39), w_gpr 20#5 (.var 38), w_gpr 21#5 (.var 37), ] },
              { curr_state := 13, prev_state := 12, writes := [w_gpr 20#5 (.var 44), w_gpr 21#5 (.var 43), w_gpr 22#5 (.var 42), w_gpr 23#5 (.var 41), ] },
              { curr_state := 14, prev_state := 13, writes := [w_gpr 17#5 (.var 45), ] },
              { curr_state := 15, prev_state := 14, writes := [w_gpr 14#5 (.var 46), ] },
              { curr_state := 16, prev_state := 15, writes := [w_gpr 16#5 (.var 47), ] },
              { curr_state := 17, prev_state := 16, writes := [w_gpr 1#5 (.var 52), w_gpr 2#5 (.var 51), w_gpr 3#5 (.var 50), w_gpr 4#5 (.var 49), w_gpr 5#5 (.var 48), ] },
              { curr_state := 18, prev_state := 17, writes := [w_gpr 3#5 (.var 53), ] },
              { curr_state := 19, prev_state := 18, writes := [w_gpr 8#5 (.var 54), ] },
              { curr_state := 20, prev_state := 19, writes := [w_gpr 5#5 (.var 55), ] },
              { curr_state := 21, prev_state := 20, writes := [w_gpr 9#5 (.var 56), ] },
              { curr_state := 22, prev_state := 21, writes := [w_gpr 28#5 (.var 60), w_gpr 29#5 (.var 59), w_gpr 30#5 (.var 58), w_gpr 31#5 (.var 57), ] },
              { curr_state := 23, prev_state := 22, writes := [w_gpr 8#5 (.var 65), w_gpr 9#5 (.var 64), w_gpr 10#5 (.var 63), w_gpr 11#5 (.var 62), w_gpr 12#5 (.var 61), ] },
              { curr_state := 24, prev_state := 23, writes := [w_gpr 7#5 (.var 70), w_gpr 8#5 (.var 69), w_gpr 9#5 (.var 68), w_gpr 10#5 (.var 67), w_gpr 11#5 (.var 66), ] },
              { curr_state := 25, prev_state := 24, writes := [w_gpr 5#5 (.var 72), w_gpr 6#5 (.var 71), ] },
              { curr_state := 26, prev_state := 25, writes := [w_gpr 4#5 (.var 76), w_gpr 5#5 (.var 75), w_gpr 6#5 (.var 74), w_gpr 7#5 (.var 73), ] },
              { curr_state := 27, prev_state := 26, writes := [w_gpr 16#5 (.var 80), w_gpr 17#5 (.var 79), w_gpr 18#5 (.var 78), w_gpr 19#5 (.var 77), ] },
              { curr_state := 28, prev_state := 27, writes := [w_gpr 5#5 (.var 81), ] },
              { curr_state := 29, prev_state := 28, writes := [w_gpr 13#5 (.var 83), w_gpr 14#5 (.var 82), ] },
              { curr_state := 30, prev_state := 29, writes := [w_gpr 8#5 (.var 87), w_gpr 9#5 (.var 86), w_gpr 10#5 (.var 85), w_gpr 11#5 (.var 84), ] }
            ]
            (by native_decide))
  simp only [Exprs.denote, and_true, and_imp] at this
  exact this (Eq.refl s0) h_step_1 h_step_2 h_step_3 h_step_4 h_step_5 h_step_6 h_step_7 h_step_8 h_step_9 h_step_10 h_step_11 h_step_12 h_step_13 h_step_14 h_step_15 h_step_16 h_step_17 h_step_18 h_step_19 h_step_20 h_step_21 h_step_22 h_step_23 h_step_24 h_step_25 h_step_26 h_step_27 h_step_28 h_step_29 h_step_30
  done



end ArmConstr
