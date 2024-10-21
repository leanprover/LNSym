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
import Arm.FromMathlib

namespace ArmConstr

/- We use `Nat`s to refer to all the state variables in our context. -/
abbrev StateVar := Nat

/-- A `GPRVal` can either be a variable or a read from the previous state.

  This is very barebones right now -- for instance, we'd need to support
  `BitVec` operators here.
-/
inductive GPRVal where
  -- A variable in the context.
  | var (i : Nat)
  -- A read from a previous state.
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
  ctx.getD v ArmState.default

/--
Denote `GPRVal v` over `ArmState prev_s`. That is, if `v` is a variable then
look it up in the `GPRValContext`. Else if `v` is `r_gpr i`, then look up the
`i`th register in `prev_s`.
-/
def GPRVal.denote (ctx : GPRValContext) (v : GPRVal) (prev_s : ArmState) : BitVec 64 :=
  match v with
  | var i => ctx.getD i 0
  | r_gpr i => r (.GPR i) prev_s

@[local simp]
theorem GPRVal.denote_of_var :
  GPRVal.denote ctx (GPRVal.var v) s = ctx.getD v 0 := by
  simp [GPRVal.denote]
  done

/--
Datastructure that characterizes all the updates that can be made to an
`ArmState`.
-/
inductive Update where
  -- `i` is a constant.
  | w_gpr (i : BitVec 5) (v : GPRVal)
  -- TODO: Other state components.
  deriving DecidableEq, Repr, Inhabited

abbrev Updates := List Update

/--
Do updates `x` and `y` refer to the same state component?
-/
def Update.regEq (x y : Update) : Prop :=
  match x, y with
  | w_gpr i _, w_gpr j _ => i = j

instance : Decidable (Update.regEq x y) :=
  inferInstanceAs (Decidable <|
    match x, y with
    | .w_gpr i _, .w_gpr j _ => i = j)

/--
Is the register index of update `x` less than or equal to that of `y`?
-/
def Update.regIndexLe (x y : Update) : Bool :=
  match x, y with
  | w_gpr i _, w_gpr j _ => i <= j

theorem Update.regIndexLe_trans (a b c : Update)
  (h1 : Update.regIndexLe a b)
  (h2 : Update.regIndexLe b c) :
  Update.regIndexLe a c := by
  simp_all [Update.regIndexLe]
  exact BitVec.le_trans h1 h2

theorem Update.regIndexLe_total (a b : Update) :
  Update.regIndexLe a b || Update.regIndexLe b a := by
  simp_all [Update.regIndexLe]
  exact BitVec.le_total a.1 b.1

/--
Datastructure to represent expressions characterizing the following state
update.
```
curr_state = writes[prev_state]
```
-/
structure Expr where
   curr_state : StateVar
   prev_state : StateVar
   writes : Updates
deriving DecidableEq, Repr, Inhabited

/--
Map updates `us` to state `prev_state` to an `ArmState`.
-/
def Expr.denote_writes (ctx : Context) (us : Updates) (prev_state : StateVar)
  : ArmState :=
  match us with
  | [] => StateVar.denote ctx.state prev_state
  | Update.w_gpr i v :: rest =>
    w (.GPR i)
      (GPRVal.denote ctx.gpr v (StateVar.denote ctx.state prev_state))
      (Expr.denote_writes ctx rest prev_state)

@[local simp]
theorem denote_writes_empty :
  Expr.denote_writes ctx [] prev_state = StateVar.denote ctx.state prev_state := by
  simp only [Expr.denote_writes]

@[local simp]
theorem denote_writes_cons :
  Expr.denote_writes ctx (e :: us) prev_state =
  w (StateField.GPR e.1) (GPRVal.denote ctx.gpr e.2 (StateVar.denote ctx.state prev_state))
    (Expr.denote_writes ctx us prev_state) := by
  simp only [Expr.denote_writes]

theorem denote_statevar_eq_denote_writes_eq
  (h : StateVar.denote ctx.state v1 = StateVar.denote ctx.state v2) :
  Expr.denote_writes ctx writes v1 = Expr.denote_writes ctx writes v2 := by
  induction writes
  case nil => simpa [Expr.denote_writes]
  case cons =>
    rename_i head tail h_ind
    simp [Expr.denote_writes]
    simp_all only
  done

-- TODO: Generalize and move to Arm/State.
theorem w_of_w_gpr_commute (i j : BitVec 5)
  (h : i ≠ j) :
  w (StateField.GPR i) v1 (w (StateField.GPR j) v2 s) =
  w (StateField.GPR j) v2 (w (StateField.GPR i) v1 s) := by
  simp_all [w, write_base_gpr, Update.regIndexLe]
  unfold write_store
  ext i
  (repeat (split <;> simp_all!))
  done

private theorem denote_writes_sorted_helper
  (h : ∀ (b : Update), b ∈ l1 → (!head.regIndexLe b) = true) :
  Expr.denote_writes ctx (l1 ++ head :: l2) s =
  Expr.denote_writes ctx (head :: l1 ++ l2) s := by
  induction l1
  case nil => simp_all only [List.not_mem_nil,
                             Bool.not_eq_eq_eq_not,
                             Bool.not_true, false_implies,
                             implies_true, List.nil_append,
                             denote_writes_cons,
                             List.singleton_append]
  case cons =>
    rename_i head' tail' ih
    simp [denote_writes_cons]
    rw [ih]
    simp only [List.cons_append, denote_writes_cons]
    · rw [w_of_w_gpr_commute]
      simp_all [Update.regIndexLe]
      apply BitVec.ne_of_lt
      simp_all
    · simp_all only [List.mem_cons,
                     or_true, implies_true,
                     List.cons_append, denote_writes_cons,
                     true_implies, Bool.not_eq_eq_eq_not,
                     Bool.not_true, forall_eq_or_imp, Bool.not_false]

/--
Sorting `Updates xs` using `Update.regIndexLe` is immaterial to their denotation
over `StateVar s`. This is because sorting preserves the order of shadowed
updates in `xs`, which means that the most recent one appears first in the
sorted list (see `w_of_w_shadow`); changing the order of independent updates
does not affect the semantics (see, e.g., `w_of_w_gpr_commute`).
-/
@[local simp]
theorem denote_writes_sorted :
  Expr.denote_writes ctx (List.mergeSort xs Update.regIndexLe) s =
  Expr.denote_writes ctx xs s := by
  induction xs
  case nil => simp only [List.mergeSort_nil, denote_writes_empty]
  case cons =>
    rename_i head tail ih
    simp only [denote_writes_cons]
    have ⟨l1, l2, h1, h2, h3⟩ :=
      @List.mergeSort_cons Update Update.regIndexLe
        (by apply Update.regIndexLe_trans)
        (by apply Update.regIndexLe_total)
        head tail
    rw [h1]
    simp_all only [Bool.not_eq_eq_eq_not,
                   Bool.not_true,
                   denote_writes_sorted_helper h3,
                   List.cons_append, denote_writes_cons]
    done


/--
Denote an `Expr e` to a `Prop` corresponding to `curr_state = writes[prev_state]`.
-/
def Expr.denote (ctx : Context) (e : Expr) : Prop :=
  StateVar.denote ctx.state e.curr_state =
  Expr.denote_writes ctx e.writes e.prev_state

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
  -- es.foldl (init := True) (fun p e => p ∧ e.denote ctx)
  match es with
  | [] => True
  | u :: rest => Expr.denote ctx u ∧ Exprs.denote ctx rest

def Expr.default : Expr :=
  { prev_state := 0, curr_state := 0, writes := [] }

/--
Insert `u`, which comes after `es`, at an appropriate safe point in `es`.

Note that `u` only changes `es` only if the former shadows some update in the
latter. Independent updates are unaffected.
-/
def Update.insertSorted (es : Updates) (u : Update) : Updates :=
  match es with
  | [] => [u]
  | e :: rest =>
    if u.regEq e then
      -- We overwrite `e` with `u`.
      u :: rest
    else if u.regIndexLe e then
      -- `u` does not appear in `es` (given that `es` is
      -- sorted). We order `u` before `e` to retain this update.
      u :: es
    else
      e :: (insertSorted rest u)

/--
Resolve any reads in `u` by looking it up in `es`. Note that `es` is expected to
be sorted.
-/
def Update.resolveRead (es : Updates) (u : Update) : Update :=
  match u with
  | .w_gpr _ (.var _) => u
  | .w_gpr i (.r_gpr gpr_idx) =>
    let ans := go gpr_idx es
    .w_gpr i ans
  where go (gpr_idx : BitVec 5) (es : Updates) : GPRVal :=
    match es with
    | [] => .r_gpr gpr_idx
    | (.w_gpr i v) :: rest =>
      if i == gpr_idx then v else go gpr_idx rest

@[local simp]
theorem Update.resolveRead_w_gpr :
  Update.resolveRead es (.w_gpr i (.var v)) = (.w_gpr i (.var v)) := by
  simp [Update.resolveRead]
  done

@[local simp]
theorem Update.resolveRead_empty_1 :
  Update.resolveRead [] u = u := by
  simp [Update.resolveRead]
  split <;> rfl

@[local simp]
theorem Update.resolveRead_index_unchanged (w : Updates) :
  (Update.resolveRead w u).1 = u.1 := by
  simp [Update.resolveRead]
  split <;> simp only
  done

/--
Resolve any reads in each of `us` by looking them up in `es`, which is expected
to be sorted.
-/
def Update.resolveReads (es us : Updates) : Updates :=
  us.map (Update.resolveRead es)

@[local simp]
theorem Update.resolveReads_cons_w_gpr :
  Update.resolveReads es (Update.w_gpr i (GPRVal.var idx) :: tail) =
  Update.w_gpr i (GPRVal.var idx) :: (Update.resolveReads es tail) := by
  simp [Update.resolveReads, Update.resolveRead]

@[local simp]
theorem Update.resolveReads_empty_1 :
  Update.resolveReads [] us = us := by
  simp [Update.resolveReads]
  apply List.map_id''; intro i
  apply Update.resolveRead_empty_1
  done

@[local simp]
theorem Update.resolvedReads_empty_2 :
  Update.resolveReads es [] = [] := by
  simp only [resolveReads, List.map_nil]

@[local simp]
theorem Update.resolveRead_empty_1_fn_is_id :
  (Update.resolveRead []) = id := by
  ext
  simp [resolveRead]
  split <;> simp_all [resolveRead.go]
  done

@[local simp]
theorem map_resolveRead_empty_1 :
  (List.map (Update.resolveRead []) us) = us := by
  simp [Update.resolveRead_empty_1_fn_is_id]
  done

-- If a write shadows another, then `List.mergeSort` with `Update.regIndexLe`
-- will preserve the order of the writes.
open Expr Update in
/--
info: [ArmConstr.Update.w_gpr 0x01#5 (ArmConstr.GPRVal.var 1),
ArmConstr.Update.w_gpr 0x01#5 (ArmConstr.GPRVal.var 2)]
-/
#guard_msgs in
#eval List.mergeSort [.w_gpr 1#5 (.var 1), .w_gpr 1#5 (.var 2)] Update.regIndexLe

/--
Aggregate `e` and `u`, assuming `u` follows `e`.
-/
def Expr.aggregate1 (e u : Expr) : Expr :=
  if e.curr_state == u.prev_state then
    let e_sorted_writes := List.mergeSort e.writes Update.regIndexLe
    let u_resolved_writes := Update.resolveReads e_sorted_writes u.writes
    { prev_state := e.prev_state,
      curr_state := u.curr_state,
      -- In principle, we can simply append `u_resolved_writes` to
      -- `e_sorted_writes`. However, it is prudent to weed out shadowed updates
      -- to keep the size of the update nest in check.
      writes := go e_sorted_writes u_resolved_writes }
  else
    -- We cannot aggregate two non-consecutive states, so we return the original
    -- Expr here.
    -- TODO: We should probably throw an error here.
    e
 where go (es us : Updates) : Updates :=
  match es, us with
  | [], us => us
  | es, [] => es
  | es, u :: rest_us =>
    Update.insertSorted (go es rest_us) u

@[local simp]
theorem Expr.aggregate1.go_empty_1 :
  Expr.aggregate1.go [] us = us := by
  simp [Expr.aggregate1.go]

@[local simp]
theorem Expr.aggregate1.go_empty_2 :
  Expr.aggregate1.go es [] = es := by
  unfold Expr.aggregate1.go
  split <;> simp_all
  done

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
          writes := [w_gpr 2#5 (.r_gpr 1), w_gpr 1#5 (.var 1)] }

/--
Aggregate `es` onto `init`.
Earlier updates appear first in `es`, and `es` follow `init`.
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

/--
If `next.writes` is empty, then
```
next.curr_state = sorted(init.writes(init.prev_state))
```
-/
theorem Expr.denote_when_next_writes_empty
  (h_init : denote ctx init)
  (h_next : denote ctx next)
  (h_init_curr_next_prev : init.curr_state = next.prev_state)
  (h_next_writes_empty : next.writes = []) :
  denote ctx
    { curr_state := next.curr_state, prev_state := init.prev_state,
      writes := List.mergeSort init.writes Update.regIndexLe } := by
  simp only [denote] at *
  simp [h_next_writes_empty] at h_next
  rw [h_next, ←h_init_curr_next_prev, h_init, denote_writes_sorted]
  done

/--
Using `Update.insertSorted es u` is equivalent to inserting `u` at the beginning
of `es`, vis-a-vis denotation. This is because `Update.insertSorted` only
modifies an `Update` in `es` if `u` shadows it.
-/
@[local simp]
theorem denote_writes_insertSorted :
  Expr.denote_writes ctx (Update.insertSorted es u) s =
  Expr.denote_writes ctx (u :: es) s := by
  induction es
  case nil =>
    simp [Update.insertSorted]
  case cons =>
    rename_i head tail ih
    simp [Update.insertSorted]
    split
    case isTrue =>
      rename_i h_u_head_eq
      simp only [denote_writes_cons]
      simp_all only [Update.regEq]
      rw [h_u_head_eq, w_of_w_shadow]
    case isFalse =>
      rename_i h_u_head_neq
      simp_all only [Update.regEq]
      split
      · simp only [denote_writes_cons]
      · simp only [denote_writes_cons]
        rw [ih]
        simp only [denote_writes_cons]
        rw [w_of_w_gpr_commute]
        exact fun a => h_u_head_neq (id (Eq.symm a))
  done

/--
Resolving `Update u` w.r.t. `writes` and then denoting it over `StateVar s0`
is equivalent to denoting the _unresolved_ `u` w.r.t. `writes` denoted over
`s0`.
-/
theorem GPRVal.denote_resolveRead (ctx : Context) :
  GPRVal.denote ctx.gpr (Update.resolveRead writes u).2 (StateVar.denote ctx.state s0) =
  GPRVal.denote ctx.gpr u.2 (Expr.denote_writes ctx writes s0) := by
  induction writes generalizing u
  case nil =>
    simp only [denote_writes_empty, Update.resolveRead_empty_1]
  case cons =>
    rename_i head tail ih
    simp only [denote_writes_cons]
    simp [Update.resolveRead]
    split
    case h_1 =>
      rename_i u' idx var
      simp [GPRVal.denote_of_var]
    case h_2 =>
      rename_i u' i' gpr_idx
      simp [Update.resolveRead.go]
      split
      case isTrue =>
        rename_i h_eq
        subst gpr_idx
        simp [GPRVal.denote, r_of_w_same]
      case isFalse =>
        rename_i h_neq
        conv => rhs; simp [GPRVal.denote]
        rw [r_of_w_different (by simp_all; exact fun a => h_neq (id (Eq.symm a)))]
        have ih' := @ih (.w_gpr gpr_idx (GPRVal.r_gpr gpr_idx))
        simp [Update.resolveRead] at ih'
        rw [ih']
        simp [GPRVal.denote]
  done

/--
`Expr.aggregate1` aggregates `first` and `second` correctly, allowing
us to express `second.curr_state` in terms of `first.prev_state`. That is:
```
if first.curr_state = first.writes[first.prev_state] and
   second.curr_state = second.writes[second.prev_state] then
 second.curr_state = resolveReads(second.writes, first.writes)[first.prev_state]
```
-/
theorem Expr.denote_aggregate1
  (h1 : Expr.denote ctx first)
  (h2 : Expr.denote ctx second) :
  Expr.denote ctx (aggregate1 first second) := by
  simp [aggregate1]
  by_cases h₀ : first.curr_state = second.prev_state
  case neg => -- h0 : first.curr_state ≠ second.prev_state
    simp_all only [minimal_theory]
  case pos => -- first.curr_state = second.prev_state
    simp_all [denote]
    rw [←h₀] at h1 h2 ⊢
    generalize first.prev_state = s0 at *
    generalize first.curr_state = s1 at *
    generalize first.writes = writes1 at *
    generalize second.writes = writes2 at *
    clear h₀ h2 first second
    induction writes2 generalizing s0 s1 writes1
    case nil =>
      simp_all
      rw [Update.resolvedReads_empty_2]
      unfold aggregate1.go
      split
      · have : writes1 = [] := by
          have := @List.length_mergeSort Update Update.regIndexLe writes1
          simp_all only [List.length_nil]
          exact List.length_eq_zero.mp (id (Eq.symm this))
        simp_all only [denote_writes_empty]
      · simp [denote_writes_sorted]
      · simp_all
    case cons =>
      rename_i u us ih
      simp [denote_writes_cons]
      simp [Update.resolveReads]
      conv => rhs; unfold aggregate1.go
      split
      case h_1 =>
        have : writes1 = [] := by
          have := @List.length_mergeSort Update Update.regIndexLe writes1
          simp_all only [List.length_nil]
          exact List.length_eq_zero.mp (id (Eq.symm this))
        simp_all [Update.resolveRead_empty_1]
        rw [ih s0 s1 [] h1]
        simp [Expr.aggregate1.go_empty_1, Update.resolveReads_empty_1, map_resolveRead_empty_1]
      case h_2 => contradiction
      case h_3 =>
        rename_i es' us' u' rest_us' h_eq h_nonempty
        have h_u' : u' = Update.resolveRead (List.mergeSort writes1 Update.regIndexLe) u := by
          simp_all
        have h_rest_us' : rest_us' = List.map (Update.resolveRead (List.mergeSort writes1 Update.regIndexLe)) us := by
          simp_all
        subst u' rest_us'
        clear h_eq
        rw [denote_writes_insertSorted]
        simp [denote_writes_cons]
        rw [Update.resolveRead_index_unchanged]
        simp [Update.resolveReads] at ih
        rw [←ih s0 s1 writes1 h1]
        rw [GPRVal.denote_resolveRead]
        rw [denote_writes_sorted, h1]
  done

/--
If `Expr.isAggregated` computes that aggregating `updates` over `init` yields
`final`, then it accurately represents `ArmState` aggregation in logic.
-/
theorem Expr.eq_true_of_denote (ctx : Context) (init final : Expr) (updates : Exprs) :
  (Expr.isAggregated init updates final) →
  Expr.denote ctx init ∧ Exprs.denote ctx updates → (Expr.denote ctx final) := by
  induction updates generalizing init
  case nil =>
    simp only [isAggregated, aggregate, beq_iff_eq, Exprs.denote, and_true]
    intro i; simp_all only [minimal_theory]
  case cons =>
    rename_i head tail h_ind
    simp [isAggregated] at *
    simp [aggregate, Exprs.denote]
    intros h_final h_init h_head h_tail
    have h_aggr1 := @Expr.denote_aggregate1 ctx init head h_init h_head
    have h_ind' := h_ind (init.aggregate1 head) h_final h_aggr1 h_tail
    exact h_ind'
    done

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Litmus Tests

open Expr Update in
example :  Expr.isAggregated
    { curr_state := 0, prev_state := 0, writes := [] }
      [{ curr_state := 1, prev_state := 0, writes := [w_gpr (0#5) (GPRVal.var 0), w_gpr (1#5) (GPRVal.var 1)] },
        { curr_state := 2, prev_state := 1, writes := [w_gpr (0#5) (GPRVal.var 0), w_gpr (1#5) (GPRVal.var 1)] }]
      { curr_state := 2, prev_state := 0, writes := [w_gpr (0#5) (GPRVal.var 0), w_gpr (1#5) (GPRVal.var 1)] } := by
      -- List.mergeSort, using in Expr.aggregate1, is irreducible, which
      -- causes reduction to get stuck. We use `with_unfolding_all` below to
      -- workaround that problem. We can also use `native_decide` here.
      with_unfolding_all decide

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
  have := (Expr.eq_true_of_denote { state := [s0, s1, s2],
                                     gpr := [x0, x1] }
          -- init
          { prev_state := 0, curr_state := 0, writes := []}
          -- final
          { prev_state := 0, curr_state := 2, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] }
          -- updates
          [ { prev_state := 0, curr_state := 1, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] },
            { prev_state := 1, curr_state := 2, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] } ]
            (by native_decide))
  simp only [Exprs.denote, List.foldl, true_and, and_true, and_imp] at this
  exact this (Eq.refl s0) h_s1 h_s2
  done

/--
info: 'ArmConstr.completely_shadowed_updates' depends on axioms: [propext,
Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in #print axioms completely_shadowed_updates

open Expr Update in
theorem partially_shadowed_and_new_updates
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) old_x1 s0))
  /-
  (NOTE) No
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
  -- (h_s2 : s2 = w (.GPR 1#5) x1 (w (.GPR 3#5) x3 s1)) :
  (h_s2 : s2 = w (.GPR 3#5) x3 (w (.GPR 1#5) x1 s1)) :
  s2 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 3#5) x3 s0)) := by
  have := (Expr.eq_true_of_denote { state := [s0, s1, s2],
                                     gpr := [x0, old_x1, x1, x3] }
          -- init
          { prev_state := 0, curr_state := 0, writes := []}
          -- final
          { prev_state := 0, curr_state := 2, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 2), w_gpr 3#5 (.var 3)] }
          -- updates
          [ { prev_state := 0, curr_state := 1, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] },
            { prev_state := 1, curr_state := 2, writes := [w_gpr 3#5 (.var 3), w_gpr 1#5 (.var 2)] } ]
            (by native_decide))
  simp only [Exprs.denote, List.foldl_cons, and_true, true_and, List.foldl_nil, and_imp] at this
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
  have := (Expr.eq_true_of_denote { state := [s0, s1, s2],
                                     gpr := [x0, old_x1, x1] }
          -- init
          { prev_state := 0, curr_state := 0, writes := []}
          -- final
          { prev_state := 0, curr_state := 2,
            writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 2), w_gpr 3#5 (.var 1)] }
          -- updates
          [ { prev_state := 0, curr_state := 1, writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] },
            { prev_state := 1, curr_state := 2, writes := [w_gpr 1#5 (.var 2), w_gpr 3#5 (.r_gpr 1)] } ]
            (by native_decide))
  simp only [Exprs.denote, List.foldl_cons, and_true, true_and, List.foldl_nil,
    and_imp] at this
  exact this (Eq.refl s0) h_s1 h_s2
  done

#time
open Expr Update in
theorem read_from_prev_update_test2 (s0 s1 s2 : ArmState)
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) old_x1 s0))
  (h_s2 : s2 = w (.GPR 1#5) x1 (w (.GPR 3#5) (r (.GPR 5#5) s1) s1)) :
  s2 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 3#5) (r (.GPR 5#5) s0) s0)) := by
  have := (Expr.eq_true_of_denote { state := [s0, s1, s2],
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
            (by native_decide))
  simp only [Exprs.denote, List.foldl, true_and, and_true, and_imp] at this
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

open Expr Update in
#eval Expr.aggregate
      { prev_state := 0, curr_state := 0, writes := []}
      [  { curr_state := 1, prev_state := 0, writes := [w_gpr 13#5 (.var 1), w_gpr 14#5 (.var 0), ] },
   { curr_state := 2, prev_state := 1, writes := [w_gpr 11#5 (.var 2), ] },
   { curr_state := 3, prev_state := 2, writes := [w_gpr 11#5 (.var 5), w_gpr 12#5 (.var 4), w_gpr 13#5 (.var 3), ] },
   { curr_state := 4, prev_state := 3, writes := [w_gpr 10#5 (.var 10), w_gpr 11#5 (.var 9), w_gpr 12#5 (.var 8), w_gpr 13#5 (.var 7), w_gpr 14#5 (.var 6), ] },
   { curr_state := 5, prev_state := 4, writes := [w_gpr 21#5 (.var 14), w_gpr 22#5 (.var 13), w_gpr 23#5 (.var 12), w_gpr 24#5 (.var 11), ] },
   { curr_state := 6, prev_state := 5, writes := [w_gpr 2#5 (.var 19), w_gpr 3#5 (.var 18), w_gpr 4#5 (.var 17), w_gpr 5#5 (.var 16), w_gpr 6#5 (.var 15), ] },
   { curr_state := 7, prev_state := 6, writes := [w_gpr 28#5 (.var 22), w_gpr 29#5 (.var 21), w_gpr 30#5 (.var 20), ] },
   { curr_state := 8, prev_state := 7, writes := [w_gpr 21#5 (.var 27), w_gpr 22#5 (.var 26), w_gpr 23#5 (.var 25), w_gpr 24#5 (.var 24), w_gpr 25#5 (.var 23), ] },
   { curr_state := 9, prev_state := 8, writes := [w_gpr 29#5 (.var 28), ] },
   { curr_state := 10, prev_state := 9, writes := [w_gpr 29#5 (.var 29), ] },
 ]

#time
open Expr Update in
theorem test_10_steps (s0 : ArmState)
  (h_step_1 : s1 = (w (.GPR 13#5) val1 (w (.GPR 14#5) val0 s0)))
  (h_step_2 : s2 = (w (.GPR 11#5) val2 s1))
  (h_step_3 : s3 = (w (.GPR 11#5) val5 (w (.GPR 12#5) val4 (w (.GPR 13#5) val3 s2))))
  (h_step_4 : s4 = (w (.GPR 10#5) val10 (w (.GPR 11#5) val9 (w (.GPR 12#5) val8 (w (.GPR 13#5) val7 (w (.GPR 14#5) val6 s3))))))
  (h_step_5 : s5 = (w (.GPR 21#5) val14 (w (.GPR 22#5) val13 (w (.GPR 23#5) val12 (w (.GPR 24#5) val11 s4)))))
  (h_step_6 : s6 = (w (.GPR 2#5) val19 (w (.GPR 3#5) val18 (w (.GPR 4#5) val17 (w (.GPR 5#5) val16 (w (.GPR 6#5) val15 s5))))))
  (h_step_7 : s7 = (w (.GPR 28#5) val22 (w (.GPR 29#5) val21 (w (.GPR 30#5) val20 s6))))
  (h_step_8 : s8 = (w (.GPR 21#5) val27 (w (.GPR 22#5) val26 (w (.GPR 23#5) val25 (w (.GPR 24#5) val24 (w (.GPR 25#5) val23 s7))))))
  (h_step_9 : s9 = (w (.GPR 29#5) val28 s8))
  (h_step_10 : s10 = (w (.GPR 29#5) val29 s9))
  :
  s10 = (w (.GPR  0x02#5) val19 (w (.GPR  0x03#5) val18 (w (.GPR  0x04#5) val17 (w (.GPR  0x05#5) val16 (w (.GPR  0x06#5) val15 (w (.GPR  0x0a#5) val10 (w (.GPR  0x0b#5) val9 (w (.GPR  0x0c#5) val8 (w (.GPR  0x0d#5) val7 (w (.GPR  0x0e#5) val6 (w (.GPR  0x15#5) val27 (w (.GPR  0x16#5) val26 (w (.GPR  0x17#5) val25 (w (.GPR  0x18#5) val24 (w (.GPR  0x19#5) val23 (w (.GPR  0x1c#5) val22 (w (.GPR  0x1d#5) val29 (w (.GPR  0x1e#5) val20 s0)))))))))))))))))) := by
    have := (Expr.eq_true_of_denote
            -- Context
            { state := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10],
               gpr := [val0, val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20, val21, val22, val23, val24, val25, val26, val27, val28, val29] }
            -- init
            { curr_state := 0, prev_state := 0, writes := [] }
            -- final
            { curr_state := 10,
              prev_state := 0,
              writes := [ArmConstr.Update.w_gpr 0x02#5 (ArmConstr.GPRVal.var 19),
                         ArmConstr.Update.w_gpr 0x03#5 (ArmConstr.GPRVal.var 18),
                         ArmConstr.Update.w_gpr 0x04#5 (ArmConstr.GPRVal.var 17),
                         ArmConstr.Update.w_gpr 0x05#5 (ArmConstr.GPRVal.var 16),
                         ArmConstr.Update.w_gpr 0x06#5 (ArmConstr.GPRVal.var 15),
                         ArmConstr.Update.w_gpr 0x0a#5 (ArmConstr.GPRVal.var 10),
                         ArmConstr.Update.w_gpr 0x0b#5 (ArmConstr.GPRVal.var 9),
                         ArmConstr.Update.w_gpr 0x0c#5 (ArmConstr.GPRVal.var 8),
                         ArmConstr.Update.w_gpr 0x0d#5 (ArmConstr.GPRVal.var 7),
                         ArmConstr.Update.w_gpr 0x0e#5 (ArmConstr.GPRVal.var 6),
                         ArmConstr.Update.w_gpr 0x15#5 (ArmConstr.GPRVal.var 27),
                         ArmConstr.Update.w_gpr 0x16#5 (ArmConstr.GPRVal.var 26),
                         ArmConstr.Update.w_gpr 0x17#5 (ArmConstr.GPRVal.var 25),
                         ArmConstr.Update.w_gpr 0x18#5 (ArmConstr.GPRVal.var 24),
                         ArmConstr.Update.w_gpr 0x19#5 (ArmConstr.GPRVal.var 23),
                         ArmConstr.Update.w_gpr 0x1c#5 (ArmConstr.GPRVal.var 22),
                         ArmConstr.Update.w_gpr 0x1d#5 (ArmConstr.GPRVal.var 29),
                         ArmConstr.Update.w_gpr 0x1e#5 (ArmConstr.GPRVal.var 20)] }
            -- updates
            [  { curr_state := 1, prev_state := 0, writes := [w_gpr 13#5 (.var 1), w_gpr 14#5 (.var 0), ] },
               { curr_state := 2, prev_state := 1, writes := [w_gpr 11#5 (.var 2), ] },
               { curr_state := 3, prev_state := 2, writes := [w_gpr 11#5 (.var 5), w_gpr 12#5 (.var 4), w_gpr 13#5 (.var 3), ] },
               { curr_state := 4, prev_state := 3, writes := [w_gpr 10#5 (.var 10), w_gpr 11#5 (.var 9), w_gpr 12#5 (.var 8), w_gpr 13#5 (.var 7), w_gpr 14#5 (.var 6), ] },
               { curr_state := 5, prev_state := 4, writes := [w_gpr 21#5 (.var 14), w_gpr 22#5 (.var 13), w_gpr 23#5 (.var 12), w_gpr 24#5 (.var 11), ] },
               { curr_state := 6, prev_state := 5, writes := [w_gpr 2#5 (.var 19), w_gpr 3#5 (.var 18), w_gpr 4#5 (.var 17), w_gpr 5#5 (.var 16), w_gpr 6#5 (.var 15), ] },
               { curr_state := 7, prev_state := 6, writes := [w_gpr 28#5 (.var 22), w_gpr 29#5 (.var 21), w_gpr 30#5 (.var 20), ] },
               { curr_state := 8, prev_state := 7, writes := [w_gpr 21#5 (.var 27), w_gpr 22#5 (.var 26), w_gpr 23#5 (.var 25), w_gpr 24#5 (.var 24), w_gpr 25#5 (.var 23), ] },
               { curr_state := 9, prev_state := 8, writes := [w_gpr 29#5 (.var 28), ] },
               { curr_state := 10, prev_state := 9, writes := [w_gpr 29#5 (.var 29), ] },
             ]
            (by native_decide))
    simp only [Exprs.denote, and_true, and_imp] at this
    exact this (Eq.refl s0) h_step_1 h_step_2 h_step_3 h_step_4 h_step_5 h_step_6 h_step_7 h_step_8 h_step_9 h_step_10
    done

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
    (Expr.eq_true_of_denote { state := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
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

#time
open Expr Update in
theorem test_40_steps (s0 : ArmState)
  (h_step_1 : s1 = (w (.GPR 4#5) val3 (w (.GPR 5#5) val2 (w (.GPR 6#5) val1 (w (.GPR 7#5) val0 s0)))))
  (h_step_2 : s2 = (w (.GPR 6#5) val7 (w (.GPR 7#5) val6 (w (.GPR 8#5) val5 (w (.GPR 9#5) val4 s1)))))
  (h_step_3 : s3 = (w (.GPR 6#5) val8 s2))
  (h_step_4 : s4 = (w (.GPR 23#5) val11 (w (.GPR 24#5) val10 (w (.GPR 25#5) val9 s3))))
  (h_step_5 : s5 = (w (.GPR 2#5) val12 s4))
  (h_step_6 : s6 = (w (.GPR 22#5) val17 (w (.GPR 23#5) val16 (w (.GPR 24#5) val15 (w (.GPR 25#5) val14 (w (.GPR 26#5) val13 s5))))))
  (h_step_7 : s7 = (w (.GPR 5#5) val19 (w (.GPR 6#5) val18 s6)))
  (h_step_8 : s8 = (w (.GPR 23#5) val21 (w (.GPR 24#5) val20 s7)))
  (h_step_9 : s9 = (w (.GPR 13#5) val22 s8))
  (h_step_10 : s10 = (w (.GPR 1#5) val25 (w (.GPR 2#5) val24 (w (.GPR 3#5) val23 s9))))
  (h_step_11 : s11 = (w (.GPR 14#5) val26 s10))
  (h_step_12 : s12 = (w (.GPR 28#5) val27 s11))
  (h_step_13 : s13 = (w (.GPR 15#5) val28 s12))
  (h_step_14 : s14 = (w (.GPR 24#5) val29 s13))
  (h_step_15 : s15 = (w (.GPR 4#5) val34 (w (.GPR 5#5) val33 (w (.GPR 6#5) val32 (w (.GPR 7#5) val31 (w (.GPR 8#5) val30 s14))))))
  (h_step_16 : s16 = (w (.GPR 13#5) val38 (w (.GPR 14#5) val37 (w (.GPR 15#5) val36 (w (.GPR 16#5) val35 s15)))))
  (h_step_17 : s17 = (w (.GPR 13#5) val40 (w (.GPR 14#5) val39 s16)))
  (h_step_18 : s18 = (w (.GPR 20#5) val45 (w (.GPR 21#5) val44 (w (.GPR 22#5) val43 (w (.GPR 23#5) val42 (w (.GPR 24#5) val41 s17))))))
  (h_step_19 : s19 = (w (.GPR 2#5) val46 s18))
  (h_step_20 : s20 = (w (.GPR 11#5) val51 (w (.GPR 12#5) val50 (w (.GPR 13#5) val49 (w (.GPR 14#5) val48 (w (.GPR 15#5) val47 s19))))))
  (h_step_21 : s21 = (w (.GPR 17#5) val55 (w (.GPR 18#5) val54 (w (.GPR 19#5) val53 (w (.GPR 20#5) val52 s20)))))
  (h_step_22 : s22 = (w (.GPR 20#5) val60 (w (.GPR 21#5) val59 (w (.GPR 22#5) val58 (w (.GPR 23#5) val57 (w (.GPR 24#5) val56 s21))))))
  (h_step_23 : s23 = (w (.GPR 9#5) val65 (w (.GPR 10#5) val64 (w (.GPR 11#5) val63 (w (.GPR 12#5) val62 (w (.GPR 13#5) val61 s22))))))
  (h_step_24 : s24 = (w (.GPR 27#5) val67 (w (.GPR 28#5) val66 s23)))
  (h_step_25 : s25 = (w (.GPR 2#5) val68 s24))
  (h_step_26 : s26 = (w (.GPR 11#5) val69 s25))
  (h_step_27 : s27 = (w (.GPR 1#5) val73 (w (.GPR 2#5) val72 (w (.GPR 3#5) val71 (w (.GPR 4#5) val70 s26)))))
  (h_step_28 : s28 = (w (.GPR 11#5) val76 (w (.GPR 12#5) val75 (w (.GPR 13#5) val74 s27))))
  (h_step_29 : s29 = (w (.GPR 26#5) val80 (w (.GPR 27#5) val79 (w (.GPR 28#5) val78 (w (.GPR 29#5) val77 s28)))))
  (h_step_30 : s30 = (w (.GPR 13#5) val81 s29))
  (h_step_31 : s31 = (w (.GPR 25#5) val82 s30))
  (h_step_32 : s32 = (w (.GPR 7#5) val86 (w (.GPR 8#5) val85 (w (.GPR 9#5) val84 (w (.GPR 10#5) val83 s31)))))
  (h_step_33 : s33 = (w (.GPR 5#5) val90 (w (.GPR 6#5) val89 (w (.GPR 7#5) val88 (w (.GPR 8#5) val87 s32)))))
  (h_step_34 : s34 = (w (.GPR 9#5) val93 (w (.GPR 10#5) val92 (w (.GPR 11#5) val91 s33))))
  (h_step_35 : s35 = (w (.GPR 8#5) val95 (w (.GPR 9#5) val94 s34)))
  (h_step_36 : s36 = (w (.GPR 4#5) val97 (w (.GPR 5#5) val96 s35)))
  (h_step_37 : s37 = (w (.GPR 28#5) val101 (w (.GPR 29#5) val100 (w (.GPR 30#5) val99 (w (.GPR 31#5) val98 s36)))))
  (h_step_38 : s38 = (w (.GPR 17#5) val104 (w (.GPR 18#5) val103 (w (.GPR 19#5) val102 s37))))
  (h_step_39 : s39 = (w (.GPR 19#5) val109 (w (.GPR 20#5) val108 (w (.GPR 21#5) val107 (w (.GPR 22#5) val106 (w (.GPR 23#5) val105 s38))))))
  (h_step_40 : s40 = (w (.GPR 7#5) val110 s39))
  :
  s40 = w (.GPR 1#5) (val73) (w (.GPR 2#5) (val72) (w (.GPR 3#5) (val71) (w (.GPR 4#5) (val97) (w (.GPR 5#5) (val96) (w (.GPR 6#5) (val89) (w (.GPR 7#5) (val110) (w (.GPR 8#5) (val95) (w (.GPR 9#5) (val94) (w (.GPR 10#5) (val92) (w (.GPR 11#5) (val91) (w (.GPR 12#5) (val75) (w (.GPR 13#5) (val81) (w (.GPR 14#5) (val48) (w (.GPR 15#5) (val47) (w (.GPR 16#5) (val35) (w (.GPR 17#5) (val104) (w (.GPR 18#5) (val103) (w (.GPR 19#5) (val109) (w (.GPR 20#5) (val108) (w (.GPR 21#5) (val107) (w (.GPR 22#5) (val106) (w (.GPR 23#5) (val105) (w (.GPR 24#5) (val56) (w (.GPR 25#5) (val82) (w (.GPR 26#5) (val80) (w (.GPR 27#5) (val79) (w (.GPR 28#5) (val101) (w (.GPR 29#5) (val100) (w (.GPR 30#5) (val99) (w (.GPR 31#5) (val98) s0)))))))))))))))))))))))))))))) := by
    have := (Expr.eq_true_of_denote
            -- Context
            { state := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40],
               gpr := [val0, val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20, val21, val22, val23, val24, val25, val26, val27, val28, val29, val30, val31, val32, val33, val34, val35, val36, val37, val38, val39, val40, val41, val42, val43, val44, val45, val46, val47, val48, val49, val50, val51, val52, val53, val54, val55, val56, val57, val58, val59, val60, val61, val62, val63, val64, val65, val66, val67, val68, val69, val70, val71, val72, val73, val74, val75, val76, val77, val78, val79, val80, val81, val82, val83, val84, val85, val86, val87, val88, val89, val90, val91, val92, val93, val94, val95, val96, val97, val98, val99, val100, val101, val102, val103, val104, val105, val106, val107, val108, val109, val110] }
            -- init
            { curr_state := 0, prev_state := 0, writes := [] }
            -- final: run `Exprs.aggregate init updates` to get the following.
            { curr_state := 40,
              prev_state := 0,
              writes := [ArmConstr.Update.w_gpr 0x01#5 (ArmConstr.GPRVal.var 73),
             ArmConstr.Update.w_gpr 0x02#5 (ArmConstr.GPRVal.var 72),
             ArmConstr.Update.w_gpr 0x03#5 (ArmConstr.GPRVal.var 71),
             ArmConstr.Update.w_gpr 0x04#5 (ArmConstr.GPRVal.var 97),
             ArmConstr.Update.w_gpr 0x05#5 (ArmConstr.GPRVal.var 96),
             ArmConstr.Update.w_gpr 0x06#5 (ArmConstr.GPRVal.var 89),
             ArmConstr.Update.w_gpr 0x07#5 (ArmConstr.GPRVal.var 110),
             ArmConstr.Update.w_gpr 0x08#5 (ArmConstr.GPRVal.var 95),
             ArmConstr.Update.w_gpr 0x09#5 (ArmConstr.GPRVal.var 94),
             ArmConstr.Update.w_gpr 0x0a#5 (ArmConstr.GPRVal.var 92),
             ArmConstr.Update.w_gpr 0x0b#5 (ArmConstr.GPRVal.var 91),
             ArmConstr.Update.w_gpr 0x0c#5 (ArmConstr.GPRVal.var 75),
             ArmConstr.Update.w_gpr 0x0d#5 (ArmConstr.GPRVal.var 81),
             ArmConstr.Update.w_gpr 0x0e#5 (ArmConstr.GPRVal.var 48),
             ArmConstr.Update.w_gpr 0x0f#5 (ArmConstr.GPRVal.var 47),
             ArmConstr.Update.w_gpr 0x10#5 (ArmConstr.GPRVal.var 35),
             ArmConstr.Update.w_gpr 0x11#5 (ArmConstr.GPRVal.var 104),
             ArmConstr.Update.w_gpr 0x12#5 (ArmConstr.GPRVal.var 103),
             ArmConstr.Update.w_gpr 0x13#5 (ArmConstr.GPRVal.var 109),
             ArmConstr.Update.w_gpr 0x14#5 (ArmConstr.GPRVal.var 108),
             ArmConstr.Update.w_gpr 0x15#5 (ArmConstr.GPRVal.var 107),
             ArmConstr.Update.w_gpr 0x16#5 (ArmConstr.GPRVal.var 106),
             ArmConstr.Update.w_gpr 0x17#5 (ArmConstr.GPRVal.var 105),
             ArmConstr.Update.w_gpr 0x18#5 (ArmConstr.GPRVal.var 56),
             ArmConstr.Update.w_gpr 0x19#5 (ArmConstr.GPRVal.var 82),
             ArmConstr.Update.w_gpr 0x1a#5 (ArmConstr.GPRVal.var 80),
             ArmConstr.Update.w_gpr 0x1b#5 (ArmConstr.GPRVal.var 79),
             ArmConstr.Update.w_gpr 0x1c#5 (ArmConstr.GPRVal.var 101),
             ArmConstr.Update.w_gpr 0x1d#5 (ArmConstr.GPRVal.var 100),
             ArmConstr.Update.w_gpr 0x1e#5 (ArmConstr.GPRVal.var 99),
             ArmConstr.Update.w_gpr 0x1f#5 (ArmConstr.GPRVal.var 98)] }
            -- updates
            [  { curr_state := 1, prev_state := 0, writes := [w_gpr 4#5 (.var 3), w_gpr 5#5 (.var 2), w_gpr 6#5 (.var 1), w_gpr 7#5 (.var 0), ] },
  { curr_state := 2, prev_state := 1, writes := [w_gpr 6#5 (.var 7), w_gpr 7#5 (.var 6), w_gpr 8#5 (.var 5), w_gpr 9#5 (.var 4), ] },
  { curr_state := 3, prev_state := 2, writes := [w_gpr 6#5 (.var 8), ] },
  { curr_state := 4, prev_state := 3, writes := [w_gpr 23#5 (.var 11), w_gpr 24#5 (.var 10), w_gpr 25#5 (.var 9), ] },
  { curr_state := 5, prev_state := 4, writes := [w_gpr 2#5 (.var 12), ] },
  { curr_state := 6, prev_state := 5, writes := [w_gpr 22#5 (.var 17), w_gpr 23#5 (.var 16), w_gpr 24#5 (.var 15), w_gpr 25#5 (.var 14), w_gpr 26#5 (.var 13), ] },
  { curr_state := 7, prev_state := 6, writes := [w_gpr 5#5 (.var 19), w_gpr 6#5 (.var 18), ] },
  { curr_state := 8, prev_state := 7, writes := [w_gpr 23#5 (.var 21), w_gpr 24#5 (.var 20), ] },
  { curr_state := 9, prev_state := 8, writes := [w_gpr 13#5 (.var 22), ] },
  { curr_state := 10, prev_state := 9, writes := [w_gpr 1#5 (.var 25), w_gpr 2#5 (.var 24), w_gpr 3#5 (.var 23), ] },
  { curr_state := 11, prev_state := 10, writes := [w_gpr 14#5 (.var 26), ] },
  { curr_state := 12, prev_state := 11, writes := [w_gpr 28#5 (.var 27), ] },
  { curr_state := 13, prev_state := 12, writes := [w_gpr 15#5 (.var 28), ] },
  { curr_state := 14, prev_state := 13, writes := [w_gpr 24#5 (.var 29), ] },
  { curr_state := 15, prev_state := 14, writes := [w_gpr 4#5 (.var 34), w_gpr 5#5 (.var 33), w_gpr 6#5 (.var 32), w_gpr 7#5 (.var 31), w_gpr 8#5 (.var 30), ] },
  { curr_state := 16, prev_state := 15, writes := [w_gpr 13#5 (.var 38), w_gpr 14#5 (.var 37), w_gpr 15#5 (.var 36), w_gpr 16#5 (.var 35), ] },
  { curr_state := 17, prev_state := 16, writes := [w_gpr 13#5 (.var 40), w_gpr 14#5 (.var 39), ] },
  { curr_state := 18, prev_state := 17, writes := [w_gpr 20#5 (.var 45), w_gpr 21#5 (.var 44), w_gpr 22#5 (.var 43), w_gpr 23#5 (.var 42), w_gpr 24#5 (.var 41), ] },
  { curr_state := 19, prev_state := 18, writes := [w_gpr 2#5 (.var 46), ] },
  { curr_state := 20, prev_state := 19, writes := [w_gpr 11#5 (.var 51), w_gpr 12#5 (.var 50), w_gpr 13#5 (.var 49), w_gpr 14#5 (.var 48), w_gpr 15#5 (.var 47), ] },
  { curr_state := 21, prev_state := 20, writes := [w_gpr 17#5 (.var 55), w_gpr 18#5 (.var 54), w_gpr 19#5 (.var 53), w_gpr 20#5 (.var 52), ] },
  { curr_state := 22, prev_state := 21, writes := [w_gpr 20#5 (.var 60), w_gpr 21#5 (.var 59), w_gpr 22#5 (.var 58), w_gpr 23#5 (.var 57), w_gpr 24#5 (.var 56), ] },
  { curr_state := 23, prev_state := 22, writes := [w_gpr 9#5 (.var 65), w_gpr 10#5 (.var 64), w_gpr 11#5 (.var 63), w_gpr 12#5 (.var 62), w_gpr 13#5 (.var 61), ] },
  { curr_state := 24, prev_state := 23, writes := [w_gpr 27#5 (.var 67), w_gpr 28#5 (.var 66), ] },
  { curr_state := 25, prev_state := 24, writes := [w_gpr 2#5 (.var 68), ] },
  { curr_state := 26, prev_state := 25, writes := [w_gpr 11#5 (.var 69), ] },
  { curr_state := 27, prev_state := 26, writes := [w_gpr 1#5 (.var 73), w_gpr 2#5 (.var 72), w_gpr 3#5 (.var 71), w_gpr 4#5 (.var 70), ] },
  { curr_state := 28, prev_state := 27, writes := [w_gpr 11#5 (.var 76), w_gpr 12#5 (.var 75), w_gpr 13#5 (.var 74), ] },
  { curr_state := 29, prev_state := 28, writes := [w_gpr 26#5 (.var 80), w_gpr 27#5 (.var 79), w_gpr 28#5 (.var 78), w_gpr 29#5 (.var 77), ] },
  { curr_state := 30, prev_state := 29, writes := [w_gpr 13#5 (.var 81), ] },
  { curr_state := 31, prev_state := 30, writes := [w_gpr 25#5 (.var 82), ] },
  { curr_state := 32, prev_state := 31, writes := [w_gpr 7#5 (.var 86), w_gpr 8#5 (.var 85), w_gpr 9#5 (.var 84), w_gpr 10#5 (.var 83), ] },
  { curr_state := 33, prev_state := 32, writes := [w_gpr 5#5 (.var 90), w_gpr 6#5 (.var 89), w_gpr 7#5 (.var 88), w_gpr 8#5 (.var 87), ] },
  { curr_state := 34, prev_state := 33, writes := [w_gpr 9#5 (.var 93), w_gpr 10#5 (.var 92), w_gpr 11#5 (.var 91), ] },
  { curr_state := 35, prev_state := 34, writes := [w_gpr 8#5 (.var 95), w_gpr 9#5 (.var 94), ] },
  { curr_state := 36, prev_state := 35, writes := [w_gpr 4#5 (.var 97), w_gpr 5#5 (.var 96), ] },
  { curr_state := 37, prev_state := 36, writes := [w_gpr 28#5 (.var 101), w_gpr 29#5 (.var 100), w_gpr 30#5 (.var 99), w_gpr 31#5 (.var 98), ] },
  { curr_state := 38, prev_state := 37, writes := [w_gpr 17#5 (.var 104), w_gpr 18#5 (.var 103), w_gpr 19#5 (.var 102), ] },
  { curr_state := 39, prev_state := 38, writes := [w_gpr 19#5 (.var 109), w_gpr 20#5 (.var 108), w_gpr 21#5 (.var 107), w_gpr 22#5 (.var 106), w_gpr 23#5 (.var 105), ] },
  { curr_state := 40, prev_state := 39, writes := [w_gpr 7#5 (.var 110), ] }]
            (by native_decide))
    simp only [Exprs.denote, and_true, and_imp] at this
    exact this (Eq.refl s0) h_step_1 h_step_2 h_step_3 h_step_4 h_step_5 h_step_6 h_step_7 h_step_8 h_step_9 h_step_10 h_step_11 h_step_12 h_step_13 h_step_14 h_step_15 h_step_16 h_step_17 h_step_18 h_step_19 h_step_20 h_step_21 h_step_22 h_step_23 h_step_24 h_step_25 h_step_26 h_step_27 h_step_28 h_step_29 h_step_30 h_step_31 h_step_32 h_step_33 h_step_34 h_step_35 h_step_36 h_step_37 h_step_38 h_step_39 h_step_40
    done

end ArmConstr
