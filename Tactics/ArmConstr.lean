/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

/-
Experimental method to aggregate state effects using reflection.

In LNSym, we already have a language that describes writes to the `ArmState`
using functions `w` and `Memory.write_bytes`. However, these writes can shadow
others, which causes the nest of writes to grow large. We reflect `w` and
`Memory.write_bytes` to get a pruned nest of writes. As a simple example,
consider the following nest of writes:
```
s1 = w .PC pc (w (.GPR 0) x0 (w .PC pc' (w (.GPR 0) x0' s0)))
```
We would like to prune this to the equivalent term below:
```
s1 = w .PC pc (w (.GPR 0) x0 s0)
```

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

/-- A `GPRVal` is simply a variable. -/
inductive GPRVal where
  -- A variable in the context.
  | var (i : Nat)
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
look it up in the `GPRValContext`.
-/
def GPRVal.denote (ctx : GPRValContext) (v : GPRVal) : BitVec 64 :=
  match v with
  | var i => ctx.getD i 0

@[local simp]
theorem GPRVal.denote_of_var :
  GPRVal.denote ctx (GPRVal.var v) = ctx.getD v 0 := by
  simp [GPRVal.denote]

/--
Datastructure that characterizes all the updates that can be made to an
`ArmState`.
-/
inductive Update where
  -- `i` is a constant.
  | w_gpr (i : BitVec 5) (v : GPRVal)
  -- TODO: Other state components.
  deriving DecidableEq, Repr, Inhabited

def Update.field (u : Update) : BitVec 5 :=
  match u with
  | w_gpr i _ => i

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
      (GPRVal.denote ctx.gpr v)
      (Expr.denote_writes ctx rest prev_state)

@[local simp]
theorem denote_writes_empty :
  Expr.denote_writes ctx [] prev_state = StateVar.denote ctx.state prev_state := by
  simp only [Expr.denote_writes]

@[local simp]
theorem denote_writes_cons :
  Expr.denote_writes ctx (e :: us) prev_state =
  w (StateField.GPR e.1) (GPRVal.denote ctx.gpr e.2)
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
    · rw [w_of_w_commute]
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
does not affect the semantics (see, e.g., `w_of_w_commute`).
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

open Expr Update in
/--
info: true
-/
#guard_msgs in
#eval List.mergeSort [.w_gpr 1#5 (.var 1), .w_gpr 1#5 (.var 2)] Update.regIndexLe =
      -- If a write shadows another, then `List.mergeSort` with `Update.regIndexLe`
      -- will preserve the order of the writes.
      [.w_gpr 1#5 (.var 1), .w_gpr 1#5 (.var 2)]

/--
Erase repeated adjacent elements. Keeps the first occurrence of each run.

Non tail-recursive version.
-/
def Expr.eraseReps (us : Updates) : Updates :=
  match us with
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
    match x.field == y.field with
    | true => x :: eraseReps rest
    | false => x :: eraseReps (y :: rest)

@[local simp]
theorem denote_writes_eraseReps :
  Expr.denote_writes ctx (Expr.eraseReps xs) s =
  Expr.denote_writes ctx xs s := by
  induction xs using Expr.eraseReps.induct
  case case1 =>
    simp_all [Expr.eraseReps]
  case case2 =>
    rename_i x
    simp [Expr.eraseReps]
  case case3 =>
    rename_i x y rest h_eq ih
    simp [Expr.eraseReps, h_eq]
    simp [Update.field] at h_eq
    rw [h_eq, w_of_w_shadow]
    simp_all
  case case4 =>
    rename_i x y rest h_eq ih
    simp [Expr.eraseReps, h_eq]
    simp [Update.field] at h_eq
    simp_all
    done

def Expr.eraseAdjReps.loop (u : Update) (us rs : Updates) : Updates :=
match u, us, rs with
| a, [], rs => (a::rs).reverse
| a, a'::as, rs =>
  match a.field == a'.field with
  | true  => loop a as rs
  | false => loop a' as (a::rs)
/--
Tail-recursive version of `Expr.eraseReps`.
-/
def Expr.eraseAdjReps (us : Updates) : Updates :=
  match us with
  | []    => []
  | a::as => Expr.eraseAdjReps.loop a as []

@[local simp]
theorem Expr.eraseAdjReps_empty :
  eraseAdjReps [] = [] := by
  simp [eraseAdjReps]

@[local simp]
theorem Expr.eraseAdjReps_one :
  eraseAdjReps [a] = [a] := by
  simp [eraseAdjReps]
  unfold eraseAdjReps.loop; simp

private theorem Expr.eraseAdjReps.loop_eq :
  Expr.eraseAdjReps.loop x (u :: us) rs =
  if x.field == u.field then Expr.eraseAdjReps.loop x us rs
                        else Expr.eraseAdjReps.loop u us (x :: rs) := by
  simp [loop]
  split
  · rename_i h_eq
    simp_all [Update.field]
  · rename_i h_eq
    simp_all [Update.field]
  done

private theorem Expr.eraseAdjReps.loop_append :
  Expr.eraseAdjReps.loop x xs (acc2 ++ acc1) =
  acc1.reverse ++ (Expr.eraseAdjReps.loop x xs acc2) := by
  induction xs generalizing x acc1 acc2
  case nil => simp [Expr.eraseAdjReps.loop]
  case cons =>
    rename_i head tail ih
    simp [Expr.eraseAdjReps.loop]
    split
    · rename_i h_eq
      simp [Update.field] at h_eq
      rw [ih]
    · rename_i h_neq
      simp [Update.field] at h_neq
      have : (x :: (acc2 ++ acc1)) = x :: acc2 ++ acc1 := by
        simp only [List.cons_append]
      rw [this, ih]
      done

-- #check Expr.eraseReps.induct
-- #check Expr.eraseAdjReps.loop.induct
/-
theorem Expr.eraseReps_and_eraseAdjReps.loop :
  acc.reverse ++ eraseReps (x :: xs) = eraseAdjReps.loop x xs acc := by
  induction x, xs, acc using eraseAdjReps.loop.induct
  case case1 => simp [eraseAdjReps.loop, eraseReps]
  case case2 =>
    rename_i a a' as rs h_eq ih
    simp [eraseReps, eraseAdjReps.loop, h_eq]
    sorry
  repeat sorry
-/

def Expr.prune (e : Expr) : Expr :=
  let e_nodups := eraseReps $ List.mergeSort e.writes Update.regIndexLe
  { e with writes := e_nodups }

open Expr Update in
/--
info: { curr_state := 1, prev_state := 0, writes := [ArmConstr.Update.w_gpr 0x00#5 (ArmConstr.GPRVal.var 0)] }
-/
#guard_msgs in
#eval prune { prev_state := 0, curr_state := 1, writes := [w_gpr 0#5 (.var 0), w_gpr 0#5 (.var 1)] }

/--
Does removing shadowed writes in `e1` give `e2`?
-/
def Expr.isPruned (e1 e2 : Expr) : Bool :=
  prune e1 == e2

theorem Expr.eq_true_of_denote (ctx : Context) (e1 e2 : Expr) :
  (Expr.isPruned e1 e2) → Expr.denote ctx e1 → Expr.denote ctx e2 := by
  simp [isPruned, prune, denote]
  intro h; cases e2
  rename_i s1 s0 writes; simp_all only [mk.injEq]
  rw [←h.right.right]; clear h
  simp only [denote_writes_eraseReps, denote_writes_sorted, implies_true]
  done

#time
open Expr Update in
theorem example1
  (h_s1 : s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 (w (.GPR 0#5) x1 s0))) :
  s1 = w (.GPR 0#5) x0 (w (.GPR 1#5) x1 s0) := by
  exact
    ((Expr.eq_true_of_denote { state := [s0, s1],
                               gpr := [x0, x1] }
        -- e1
        { prev_state := 0, curr_state := 1,
          writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1), w_gpr 0#5 (.var 1)] }
        -- e2
        { prev_state := 0, curr_state := 1,
          writes := [w_gpr 0#5 (.var 0), w_gpr 1#5 (.var 1)] }
        (by native_decide)))
    h_s1

-- #print example1

end ArmConstr
