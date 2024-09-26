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
  and if we constant-fold constants, we will naturally perform canonicalization.
  That is, the two rewrites:

  (a) (x + c) -> (c + x).
  (b) x + (y + z) -> (x + y) + z.

  combine to achieve constant folding. Observe an example:

  ((x + 10) + 20)
  -b-> (20 + (x + 10))
  -b-> (20 + (10 + x))
  -a-> (20 + 10) + x
  -reduceAdd-> 30 + x

2. Canonicalizing (a + b) % n → a % n + b % n by exploiting `bv_omega`,
   and eventually, `simp_mem`.
-/
import Lean
import Arm.Memory.Attr
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

Notice that this is different from `getBitVecValue?` in that here we allow `w` to be symbolic.
Hence, we might not know the width, explaining why we return a `Nat` rather than a `BitVec`.
-/
def getBitVecOfNatValue? (e : Expr) : (Option (Expr × Expr)) :=
  match_expr e with
  | BitVec.ofNat nExpr vExpr => some (nExpr, vExpr)
  | _ => none

/-- Try to build a proof for `ty` by reduction to `omega`. -/
@[inline] def dischargeByOmega (ty : Expr) : SimpM Step := do
  let proof : Expr ← mkFreshExprMVar ty
  let g := proof.mvarId!
  let some g ← g.falseOrByContra
    | return .continue
  try
    g.withContext (do Lean.Elab.Tactic.Omega.omega (← getLocalHyps).toList g {})
  catch _ =>
    return .continue
  return .done { expr := ty, proof? := proof }

def processingEmoji : String := "⚙️"

-- x % n = x if x < n
@[inline] def reduceModOfLt (x : Expr) (n : Expr) : SimpM Step := do
  trace[Tactic.address_normalization] "{processingEmoji} reduceModOfLt '{x} % {n}'"
  let ltTy := mkLTNat x n
  let Step.done { expr := _, proof? := some p} ← dischargeByOmega ltTy
    | return .continue
  let eqProof ← mkAppM ``Nat.mod_eq_of_lt #[p]
  trace[Tactic.address_normalization] "{checkEmoji} reduceModOfLt '{x} % {n}'"
  return .done { expr := x, proof? := eqProof : Result }

-- x % n = x - n if x >= n and x - n < n
@[inline] def reduceModSub (x : Expr) (n : Expr) : SimpM Step := do
  trace[Tactic.address_normalization] "{processingEmoji} reduceModSub '{x} % {n}'"
  let geTy := mkGENat x n
  let Step.done { expr := _, proof? := some geProof} ← dischargeByOmega geTy
    | return .continue
  let subTy := mkSubNat x n
  let ltTy := mkLTNat subTy n
  let Step.done { expr := _, proof? := some ltProof} ← dischargeByOmega ltTy
    | return .continue
  let eqProof ← mkAppM ``Nat.mod_eq_sub #[geProof, ltProof]
  trace[Tactic.address_normalization] "{checkEmoji} reduceModSub '{x} % {n}'"
  return .done { expr := subTy, proof? := eqProof : Result }

@[inline, bv_toNat] def reduceMod (e : Expr) : SimpM Step := do
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

/-- Canonicalize a commutative binary operation.

1. If both arguments are constants, we perform constant folding.
2. If only one of the arguments is a constant, we move the constant to the left.
-/
@[inline, bv_toNat] def canonicalizeBinConst (declName : Name) -- operator to constant fold, such as `HAdd.hAdd`.
    (arity : Nat)
    (commProofDecl : Name) -- commProof: `∀ (x y : Bitvec w), x op y = y op x`.
    (reduceProofDecl : Name) -- reduce proof: `∀ (w : Nat), (n m : Nat) (BitVec.ofNat w n) op (BitVec.ofNat w m) = BitVec.ofNat w (n op' m)`.
    (fxy : Expr) : SimpM Step := do
  unless fxy.isAppOfArity declName arity do return .continue
  let fx := fxy.appFn!
  let x := fx.appArg!
  let f := fx.appFn!
  let y := fxy.appArg!
  trace[Tactic.address_normalization] "{processingEmoji} canonicalizeBinConst '({f} {x} {y})'"
  match getBitVecOfNatValue? x with
  | some (xwExpr, xvalExpr) =>
    -- We have a constant on the left, check if we have a constant on the right
    -- so we can fully constant fold the expression.
    let .some (_, yvalExpr) := getBitVecOfNatValue? y
      | return .continue

    let e' ← mkAppM reduceProofDecl #[xwExpr, xvalExpr, yvalExpr]
    trace[Tactic.address_normalization] "{checkEmoji} canonicalizeBinConst '({f} {x} {y})'"
    return .done { expr := e', proof? := ← mkAppM reduceProofDecl #[x, y] : Result }

  | none =>
    -- We don't have a constant on the left, check if we have a constant on the right
    -- and try to move it to the left.
    let .some _ := getBitVecOfNatValue? y
      | return .continue -- no constants on either side, nothing to do.

    -- Nothing more to to do, except to move the right constant to the left.
    let e' := mkAppN f #[y, x]
    trace[Tactic.address_normalization] "{checkEmoji} canonicalizeBinConst '({f} {x} {y})'"
    return .done { expr := e', proof? := ← mkAppM commProofDecl #[x, y] : Result }

/- Change `100` to `100#64` so we can pattern match to `BitVec.ofNat` -/
attribute [address_normalization] BitVec.ofNat_eq_ofNat


theorem BitVec.add_ofNat_eq_ofNat_add (n : Nat) (x : BitVec w) : x + BitVec.ofNat w n = BitVec.ofNat w n + x := by
  apply BitVec.add_comm


theorem BitVec.mul_ofNat_eq_ofNat_mul (n : Nat) (x : BitVec w) : x * BitVec.ofNat w n = BitVec.ofNat w n * x := by
  apply BitVec.mul_comm

simproc [address_normalization] constFoldAdd ((_ + _ : BitVec _)) :=
  canonicalizeBinConst ``HAdd.hAdd 6 ``BitVec.add_comm ``BitVec.add_ofNat_eq_ofNat_add

simproc [address_normalization] constFoldMul ((_ * _ : BitVec _)) :=
  canonicalizeBinConst ``HMul.hMul 6 ``BitVec.mul_comm ``BitVec.mul_ofNat_eq_ofNat_mul

@[address_normalization]
theorem BitVec.ofNat_add_ofNat_eq_add_ofNat (w : Nat) (n m : Nat) : 
    BitVec.ofNat w n + BitVec.ofNat w m = BitVec.ofNat w (n + m) := by
  apply BitVec.eq_of_toNat_eq
  simp

@[address_normalization]
theorem BitVec.ofNat_mul_ofNat_eq_mul_ofNat (w : Nat) (n m : Nat) : 
    BitVec.ofNat w n * BitVec.ofNat w m = BitVec.ofNat w (n * m) := by
  apply BitVec.eq_of_toNat_eq
  -- Note that omega cannot close the goal since it's symbolic multiplication.
  simp only [toNat_mul, toNat_ofNat, ← Nat.mul_mod]

/-- Reassociate addition to left. -/
@[address_normalization]
theorem BitVec.add_assoc_symm (x y z : BitVec w) : x + (y + z) = x + y + z := by
  rw [BitVec.add_assoc]

/-- Reassociate multiplication to left. -/
@[address_normalization]
theorem BitVec.mul_assoc_symm (x y z : BitVec w) : x * (y * z) = x * y * z := by
  rw [BitVec.mul_assoc]
