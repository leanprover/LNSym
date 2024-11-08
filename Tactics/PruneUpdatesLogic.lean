/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

/-
Experimental method to aggregate state effects using reflection.

In LNSym, we already have a language that describes writes to the `ArmState`
using functions `w`. However, these writes can shadow others, which causes the
nest of writes to grow large. We reflect `w` and to get a pruned nest of writes.
As a simple example, consider the following nest of writes:
```
s1 = w .PC pc (w (.GPR 0) x0 (w .PC pc' (w (.GPR 0) x0' s0)))
```
We would like to prune this to the equivalent term below:
```
s1 = w .PC pc (w (.GPR 0) x0 s0)
```

Note that we do not reflect memory updates at this point.

This is inspired by `simp_arith`, especially the following files:

`[lean] Init/Data/Nat/Linear.lean`
`[lean] Meta/Tactic/LinearAith/Nat/Basic.lean`
`[lean] Meta/Tactic/LinearAith/Nat/Simp.lean`
-/

import Arm.Exec
import Arm.FromMathlib

namespace ArmConstr

/- We use `Nat`s to refer to all the variables in our context. -/
abbrev StateVar  := Nat
abbrev GPRVar    := Nat
abbrev SFPVar    := Nat
abbrev PCVar     := Nat
abbrev ErrVar    := Nat
abbrev FlagVar   := Nat

inductive Var where
  | state (var : StateVar)
  | gpr   (var : GPRVar)
  | sfp   (var : SFPVar)
  | pc    (var : PCVar)
  | err   (var : ErrVar)
  | flag  (var : FlagVar)
  deriving Repr, DecidableEq, Inhabited

abbrev StateContext := List ArmState
abbrev GPRContext   := List (BitVec 64)
abbrev SFPContext   := List (BitVec 128)
abbrev PCContext    := List (BitVec 64)
abbrev FlagContext  := List (BitVec 1)
abbrev ErrContext  := List (StateError)

/--
Context containing all the variables encountered in the problem. The
position of a variable in the context becomes variable name (see, e.g.,
`StateVar`, which is a `Nat`).
-/
structure Context where
  state : StateContext
  err   : ErrContext
  pc    : PCContext
  gpr   : GPRContext
  sfp   : SFPContext
  flag  : FlagContext
  deriving Repr, Inhabited

def Val (var : Var) : Type :=
  match var with
  | .state _ => ArmState
  | .gpr _ => BitVec 64
  | .sfp _ => BitVec 128
  | .pc _ => BitVec 64
  | .flag _ => BitVec 1
  | .err _ => StateError

/--
Look up variable `v` in the `StateContext`.
-/
def StateVar.denote (ctx : StateContext) (v : StateVar) : ArmState :=
  ctx.getD v ArmState.default

/--
Look up variable `v` in the `GPRContext`.
-/
def GPRVar.denote (ctx : GPRContext) (v : GPRVar) : BitVec 64 :=
  ctx.getD v 0

@[local simp]
theorem GPRVar.denote_of_var :
  GPRVar.denote ctx v = ctx.getD v 0 := by
  simp [GPRVar.denote]

/--
Look up variable `v` in the `SFPContext`.
-/
def SFPVar.denote (ctx : SFPContext) (v : SFPVar) : BitVec 128 :=
  ctx.getD v 0

/--
Look up variable `v` in the `PCContext`.
-/
def PCVar.denote (ctx : PCContext) (v : PCVar) : BitVec 64 :=
  ctx.getD v 0

/--
Look up variable `v` in the `ErrContext`.
-/
def ErrVar.denote (ctx : ErrContext) (v : ErrVar) : StateError :=
  ctx.getD v StateError.None

/--
Look up variable `v` in the `FlagContext`.
-/
def FlagVar.denote (ctx : FlagContext) (v : FlagVar) : BitVec 1 :=
  ctx.getD v 0

/--
Look up `var` in the appropriate field of `ctx`, indicated by `fld`.
-/
def Var.denote (ctx : Context) (fld : StateField) (var : Nat) : state_value fld :=
  match fld with
  | .GPR _   => GPRVar.denote ctx.gpr var
  | .SFP _   => SFPVar.denote ctx.sfp var
  | .PC      => PCVar.denote ctx.pc var
  | .FLAG _  => FlagVar.denote ctx.flag var
  | .ERR     => ErrVar.denote ctx.err var

/--
Datastructure that characterizes all the updates that can be made to an
`ArmState`.
-/
inductive Update where
  | err  (v : ErrVar)
  | pc   (v : PCVar)
  | gpr  (i : BitVec 5) (v : GPRVar)
  | sfp  (i : BitVec 5) (v : SFPVar)
  | flag (i : PFlag)    (v : FlagVar)
 deriving DecidableEq, Repr, Inhabited

instance : ToString Update where toString a := toString (repr a)

instance : Lean.ToMessageData Update where
  toMessageData x := match x with
  | .err v    => m!"(err {v})"
  | .pc v     => m!"(pc {v})"
  | .gpr i v  => m!"(gpr {i} {v})"
  | .sfp i v  => m!"(sfp {i} {v})"
  | .flag i v => m!"(flag {i} {v})"

abbrev Updates := List Update

/--
`StateField` characterized by the `Update u`.
-/
def Update.field (u : Update) : StateField :=
  match u with
  | .err _ => StateField.ERR
  | .pc _ => StateField.PC
  | .gpr i _ => StateField.GPR i
  | .sfp i _ => StateField.SFP i
  | .flag i _ => StateField.FLAG i

/--
Variable ensconsed in `Update u`.
-/
def Update.var (u : Update) : Nat :=
  match u with
  | Update.err v    => v
  | Update.pc v     => v
  | Update.gpr _ v  => v
  | Update.sfp _ v  => v
  | Update.flag _ v => v

/--
Do updates `x` and `y` refer to the same state component?
-/
def Update.regEq (x y : Update) : Prop :=
  match x, y with
  | err _, err _ => True
  | pc _, pc _ => True
  | gpr i _, gpr j _ => i = j
  | sfp i _, sfp j _ => i = j
  | flag i _, flag j _ => i = j
  | _, _ => False

-- set_option diagnostics true in
-- instance : Decidable (Update.regEq x y) :=
--   inferInstanceAs (Decidable <|
--     match x, y with
--     | .pc _, .pc _ => True
--     | .gpr i _, .gpr j _ => i = j
--     | .sfp i _, .sfp j _ => i = j
--     | .flag i _, .flag j _ => i = j
--     | _, _ => False)

private def PFlag.natIdx (f : PFlag) : Nat :=
  match f with
  | .N => 0
  | .Z => 1
  | .C => 2
  | .V => 3

/--
Is the field of update `x` "less than or equal to" that of `y`?
-/
def Update.regIndexLe (x y : Update) : Bool :=
  match x, y with
  | err _, _ => true
  | _, err _ => false
  | pc _, _ => true
  | _, pc _ => false
  | gpr i _, gpr j _ => i <= j
  | gpr _ _, _ => true
  | _, gpr _ _ => false
  | sfp i _, sfp j _ => i <= j
  | sfp _ _, _ => true
  | _, sfp _ _ => false
  | flag i _, flag j _ => PFlag.natIdx i <= PFlag.natIdx j

theorem Update.regIndexLe_trans (a b c : Update)
  (h1 : Update.regIndexLe a b)
  (h2 : Update.regIndexLe b c) :
  Update.regIndexLe a c := by
  simp_all [Update.regIndexLe]
  cases a <;> cases b <;> cases c <;> simp_all
  repeat (exact BitVec.le_trans h1 h2)
  exact Nat.le_trans h1 h2
  done

theorem Update.regIndexLe_total (a b : Update) :
  Update.regIndexLe a b || Update.regIndexLe b a := by
  simp [Update.regIndexLe]
  cases a <;> cases b <;> simp_all
  repeat apply BitVec.le_total
  apply Nat.le_total
  done

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
  | Update.gpr i v :: rest =>
    w (.GPR i)
      (GPRVar.denote ctx.gpr v)
      (Expr.denote_writes ctx rest prev_state)
  | Update.sfp i v :: rest =>
    w (.SFP i)
      (SFPVar.denote ctx.sfp v)
      (Expr.denote_writes ctx rest prev_state)
  | Update.pc v :: rest =>
    w .PC
      (PCVar.denote ctx.pc v)
      (Expr.denote_writes ctx rest prev_state)
  | Update.err v :: rest =>
    w .ERR
      (ErrVar.denote ctx.err v)
      (Expr.denote_writes ctx rest prev_state)
  | Update.flag i v :: rest =>
    w (.FLAG i)
      (FlagVar.denote ctx.flag v)
      (Expr.denote_writes ctx rest prev_state)

@[local simp]
theorem denote_writes_empty :
  Expr.denote_writes ctx [] prev_state = StateVar.denote ctx.state prev_state := by
  simp only [Expr.denote_writes]

@[local simp]
theorem denote_writes_cons :
  Expr.denote_writes ctx (e :: us) prev_state =
  w (Update.field e) (Var.denote ctx (Update.field e) (Update.var e))
    (Expr.denote_writes ctx us prev_state) := by
  conv => lhs; unfold Expr.denote_writes
  simp_all [Update.field, Update.var, Var.denote]
  split
  · -- Empty updates
    simp_all
  · -- GPR update
    rename_i heq i' v i h_cons
    have h_cons_1 : e = Update.gpr i' v := by simp_all
    have h_cons_2 : us = i := by simp_all
    rw [h_cons_1]; simp_all
  · -- SFP update
    rename_i heq i' v i h_cons
    have h_cons_1 : e = Update.sfp i' v := by simp_all
    have h_cons_2 : us = i := by simp_all
    rw [h_cons_1]; simp_all
  · -- PC update
    rename_i heq i' v i
    have h_cons_1 : e = Update.pc i' := by simp_all
    have h_cons_2 : us = v := by simp_all
    rw [h_cons_1]; simp_all
  · -- ERR update
    rename_i heq i' v i
    have h_cons_1 : e = Update.err i' := by simp_all
    have h_cons_2 : us = v := by simp_all
    rw [h_cons_1]; simp_all
  · -- Flag update
    rename_i heq i' v i h_cons
    have h_cons_1 : e = Update.flag i' v := by simp_all
    have h_cons_2 : us = i := by simp_all
    rw [h_cons_1]; simp_all
  done

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
      simp_all [Update.regIndexLe, Update.field]
      obtain ⟨h1, h2⟩ := h
      clear h2
      cases head <;> try simp_all <;> cases head' <;>
      try simp_all <;> try exact BitVec.ne_of_lt h1
      rename_i i1 _ i2 _
      cases i1 <;> cases i2 <;> try simp_all
    · simp_all

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
#eval List.mergeSort [.gpr 1#5 1, .gpr 1#5 2] Update.regIndexLe =
      -- If a write shadows another, then `List.mergeSort` with `Update.regIndexLe`
      -- will preserve the order of the writes.
      [.gpr 1#5 1, .gpr 1#5 2]

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
    | true => eraseReps (x :: rest)
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
    cases x <;> try simp_all <;> cases y <;>
    try simp_all [Update.field, Update.var] <;>
    rw [h_eq, w_of_w_shadow]
    all_goals (simp_all [Update.field, Update.var]; rw [w_of_w_shadow])
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

(FIXME) Prove equivalent to `Expr.eraseReps`.
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
  let e_sorted := List.mergeSort e.writes Update.regIndexLe
  let e_nodups := eraseReps e_sorted
  { e with writes := e_nodups }

open Expr Update in
/--
info: { curr_state := 1,
  prev_state := 0,
  writes := [ArmConstr.Update.pc 0,
             ArmConstr.Update.sfp 0x00#5 3,
             ArmConstr.Update.sfp 0x01#5 2,
             ArmConstr.Update.sfp 0x02#5 1,
             ArmConstr.Update.sfp 0x03#5 0] }
-/
#guard_msgs in
#eval Expr.prune { curr_state := 1,
                   prev_state := 0,
                   writes := [(.pc 0),
                              (.sfp 0x03#5 0),
                              (.pc 1),
                              (.sfp 0x02#5 1),
                              (.pc 2),
                              (.sfp 0x01#5 2),
                              (.pc 3),
                              (.sfp 0x00#5 3)]}

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
                               gpr := [x0, x1],
                               sfp := [],
                               pc := [],
                               flag := [],
                               err := [] }
        -- e1
        { prev_state := 0, curr_state := 1,
          writes := [.gpr 0#5 (0), .gpr 1#5 (1), .gpr 0#5 (1)] }
        -- e2
        { prev_state := 0, curr_state := 1,
          writes := [.gpr 0#5 (0), .gpr 1#5 (1)] }
        (by native_decide)))
    h_s1

-- #print example1

end ArmConstr
