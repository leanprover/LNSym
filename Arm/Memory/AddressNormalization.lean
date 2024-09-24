/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat, Tobias Grosser
-/

/-
This file implements bitvector expression simplification simprocs.
We perform the following additional changes:

1. Canonicalizing bitvector expression to always have constants on the left.
  Recall that the default associativity of addition is to the left: x + y + z = (x + y) + z.
  If we thus normalize our expressions to have constants on the left,
  and if we reassociate our additions to be to the left, we will naturally perform
  constant folding:

  (a) (x + c) -> (c + x).
  (b) x + (y + z) -> (x + y) + c.

  Observe an example:

  ((x + 10) + 20)
  -b-> (20 + (x + 10))
  -b-> (20 + (10 + x))
  -a-> (20 + 10) + x
  -reduceAdd-> 30 + x

2. Canonicalizing (a + b) % n → a % n + b % n by exploiting `bv_omega`,
   and eventually, `simp_mem`.
-/
import Lean
import Tactics.Attr
import Arm.Attr

open Lean Meta Elab Simp


theorem Nat.mod_eq_sub {x y : Nat} (h : x ≥ y) (h' : x - y < y) :
    x % y = x - y := by
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt h']

private def mkLTNat (x y : Expr) : Expr :=
  mkAppN (.const ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat, x, y]

private def mkLENat (x y : Expr) : Expr :=
  mkAppN (.const ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat, x, y]

private def mkGENat (x y : Expr) : Expr := mkLENat y x

private def mkSubNat (x y : Expr) : Expr :=
  let lz := levelZero
  let nat := mkConst ``Nat
  let instSub := mkConst ``instSubNat
  let instHSub := mkAppN (mkConst ``instHSub [lz]) #[nat, instSub]
  mkAppN (mkConst ``HSub.hSub [lz, lz, lz]) #[nat, nat, nat, instHSub, x, y]

/--
Given an expression of the form `n#w`, return the value of `n` if it is a ground constant.
-/
def getBitVecOfNatValue? (e : Expr) : MetaM (Option Nat) :=
  match_expr e with
  | BitVec.ofNat _nExpr vExpr => getNatValue? vExpr
  | _ => return none

/-- Try to build a proof for `ty` by reduction to `bv_omega`. -/
@[inline] def proveByBvOmega (ty : Expr) : SimpM Step := do
  let proof : Expr ← mkFreshExprMVar ty
  let g := proof.mvarId!
  let some g ← g.falseOrByContra
    | return .continue
  try
    g.withContext (do Lean.Elab.Tactic.Omega.omega (← getLocalHyps).toList g {})
  catch _ =>
    return .continue
  return .done { expr := ty, proof? := proof }

/-- Try to build a proof for `ty` by reduction to `omega`. -/
@[inline] def proveByOmega (ty : Expr) : SimpM Step := do
  let proof : Expr ← mkFreshExprMVar ty
  let g := proof.mvarId!
  let some g ← g.falseOrByContra
    | return .continue
  try
    g.withContext (do Lean.Elab.Tactic.Omega.omega (← getLocalHyps).toList g {})
  catch _ =>
    return .continue
  return .done { expr := ty, proof? := proof }

-- x % n = x if x < n
@[inline] def reduceModOfLt (x : Expr) (n : Expr) : SimpM Step := do
  trace[Tactic.addressNormalization] "trying to reduce... '{x} % {n} → {x}'"
  let ltTy := mkLTNat x n
  let Step.done { expr := _, proof? := some p} ← proveByOmega ltTy
    | return .continue
  let eqProof ← mkAppM ``Nat.mod_eq_of_lt #[p]
  return .done { expr := x, proof? := eqProof : Result }

-- x % n = x - n if x >= n and x - n < n
@[inline] def reduceModSub (x : Expr) (n : Expr) : SimpM Step := do
  trace[Tactic.addressNormalization] "trying to reduce... '{x} % {n} → {x} - {n}'"
  let geTy := mkGENat x n
  let Step.done { expr := _, proof? := some geProof} ← proveByOmega geTy
    | return .continue
  let subTy := mkSubNat x n
  let ltTy := mkLTNat subTy n
  let Step.done { expr := _, proof? := some ltProof} ← proveByOmega ltTy
    | return .continue
  let eqProof ← mkAppM ``Nat.mod_eq_sub #[geProof, ltProof]
  return .done { expr := subTy, proof? := eqProof : Result }

@[inline, bv_toNat] def reduceMod (e : Expr) : SimpM Step := do
  -- trace[Tactic.addressNormalization] "trying to reduce... '{e}'"
  match_expr e with
  | HMod.hMod xTy nTy outTy _inst x n =>
    let natTy := mkConst ``Nat
    if (xTy != natTy) || (nTy != natTy) || (outTy != natTy) then
      return .continue
    if let .done res ← reduceModOfLt x n then
      return .done res
    if let .done res ← reduceModSub x n then
      return .done res
    return .continue
  | _ => do
     return .continue

simproc↑ [address_normalization] reduce_mod_omega (_ % _) := fun e => reduceMod e

/-- In a commutative binary operation, move a bitvector constant to the left. -/
@[inline, bv_toNat] def moveBinConstLeft (declName : Name)
    (arity : Nat) (commProofDecl : Name) (fxy : Expr) : SimpM Step := do
  unless fxy.isAppOfArity declName arity do return .continue
  -- let some v₁ ← BitVec.fromExpr? e.appFn!.appArg! | return .continue
  let fx := fxy.appFn!
  let x := fx.appArg!
  let f := fx.appFn!
  let y := fxy.appArg!
  trace[Tactic.addressNormalization] "trying to move constant to left in '({f} {x} {y})'"
  if (← getBitVecOfNatValue? y).isSome then
    trace[Tactic.addressNormalization] "{checkEmoji} found constant '{y}' to the right in '({f} {x} {y})'. Moving."
    let e' := mkAppN f #[y, x]
    return .done { expr := e', proof? := ← mkAppM commProofDecl #[x, y] : Result }
  else
    trace[Tactic.addressNormalization] "{crossEmoji} non-constant '{y}' to the right in '({f} {x} {y})'. Skipping."
    return .continue

/- Change `100` to `100#64` so we can pattern match to `BitVec.ofNat` -/
attribute [address_normalization] BitVec.ofNat_eq_ofNat

@[address_normalization]
theorem BitVec.add_ofNat_eq_ofNat_add (n : Nat) (x : BitVec w) : x + BitVec.ofNat w n = BitVec.ofNat w n + x := by
  apply BitVec.add_comm

@[address_normalization]
theorem BitVec.ofNat_add_ofNat_eq_add_ofNat (n m : Nat) : BitVec.ofNat w n + BitVec.ofNat w m = BitVec.ofNat w (n + m) := by
  apply BitVec.eq_of_toNat_eq
  simp

/- Reduce bitvector operations. -/
-- attribute [address_normalization] BitVec.reduceAdd
-- attribute [address_normalization] BitVec.reduceSub
-- attribute [address_normalization] BitVec.reduceAdd
-- attribute [address_normalization] BitVec.reduceMul
-- attribute [address_normalization] BitVec.reduceShiftLeft
-- attribute [address_normalization] BitVec.reduceShiftLeftShiftLeft
-- attribute [address_normalization] BitVec.reduceShiftLeftZeroExtend
-- attribute [address_normalization] BitVec.reduceShiftRightShiftRight
-- attribute [address_normalization] BitVec.reduceAbs
-- attribute [address_normalization] BitVec.reduceAnd
-- attribute [address_normalization] BitVec.reduceAllOnes
-- attribute [address_normalization] Nat.reduceAdd

/-- Reassociate addition to left. -/
@[address_normalization]
theorem BitVec.reassoc_add (x y z : BitVec w) : x + (y + z) = x + y + z := by
  rw [BitVec.add_assoc]

-- simproc [address_normalization] moveAddConstLeft ((_ + _ : BitVec _)) :=
--   moveBinConstLeft ``HAdd.hAdd 6 ``BitVec.add_comm

set_option trace.Tactic.addressNormalization true in
/-- info: [Tactic.addressNormalization] trying to reduce... 'x.toNat % 2 ^ w → x.toNat' -/
#guard_msgs in theorem eg₁ (x : BitVec w) : x.toNat % 2 ^ w = x.toNat + 0 := by
  simp only [address_normalization]
  rfl

/-- info: 'eg₁' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₁

set_option trace.Tactic.addressNormalization true in
/--
info: [Tactic.addressNormalization] trying to reduce... 'x.toNat + y.toNat % 2 ^ w → x.toNat + y.toNat'
-/
#guard_msgs in theorem eg₂ (x y : BitVec w)  (h : x.toNat + y.toNat < 2 ^ w) :
  (x + y).toNat = x.toNat + y.toNat := by
  simp [address_normalization]

/-- info: 'eg₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₂

set_option trace.Tactic.addressNormalization true in
/--
info: [Tactic.addressNormalization] trying to reduce... 'x.toNat + y.toNat % 2 ^ w → x.toNat + y.toNat'
[Tactic.addressNormalization] trying to reduce... 'x.toNat + y.toNat % 2 ^ w → x.toNat + y.toNat - 2 ^ w'
-/
#guard_msgs in theorem eg₃ (x y : BitVec w) :
  (x + y).toNat = (x.toNat + y.toNat) % 2 ^ w := by
  simp [address_normalization]

/-- info: 'eg₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₂

theorem eg₄ (x y z : BitVec w)
  (h₂ : y.toNat + z.toNat < 2 ^ w)
  (h : x.toNat * (y.toNat + z.toNat) < 2 ^ w) :
  (x * (y + z)).toNat = x.toNat * (y.toNat + z.toNat) := by
  simp [address_normalization]

/-- info: 'eg₄' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₄

theorem eg₅ (x y : BitVec w) (h : x.toNat + y.toNat ≥ 2 ^ w) (h' : (x.toNat + y.toNat) - 2 ^ w < 2 ^ w) :
  (x + y).toNat = x.toNat + y.toNat - 2 ^ w := by
  simp [address_normalization]

/-- info: 'eg₅' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₅

set_option trace.Tactic.addressNormalization true in
#guard_msgs in theorem eg₆ (x : BitVec w) : x + 100#w = 100#w + x := by
  simp only [address_normalization]

/-- info: 'eg₆' depends on axioms: [propext] -/
#guard_msgs in #print axioms eg₆

set_option tactic.simp.trace true
set_option diagnostics true in
example {w : Nat} : 100#w + 200#w = 300#w := by
  simp only [address_normalization]
  -- simp made no progress

theorem eg₇ (x : BitVec w) : 100#w + (200#w + x) = 300#w + x := by
  simp

  simp only [address_normalization]
  rfl

/-- info: 'eg₅' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₇
