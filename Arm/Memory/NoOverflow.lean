/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat
-/
import Arm.Memory.Attr

/-
We build generic abstractions to state that a bitvector
expression does not overflow. This allows us to write
expression trees involving addition, subtraction, and multiplication
and assert that they do not overflow.
-/

/--
An expression tree that can be asserted to not overflow
with NoOverflow.assert
-/
inductive NoOverflow (w : Nat)
| mul (x y : NoOverflow w) : NoOverflow w
| add (x y : NoOverflow w) : NoOverflow w
| sub (x y : NoOverflow w) : NoOverflow w
| const (x : BitVec w) : NoOverflow w

instance {w} : Coe (BitVec w) (NoOverflow w) := ⟨NoOverflow.const⟩

instance {w} : OfNat (NoOverflow w) n  where
  ofNat := NoOverflow.const (BitVec.ofNat w n)

instance {w} : Coe Nat (NoOverflow w) :=
  ⟨fun n => NoOverflow.const (BitVec.ofNat w n)⟩

instance {w} : HAdd (NoOverflow w) (NoOverflow w) (NoOverflow w) where
  hAdd := NoOverflow.add

instance {w} : HMul (NoOverflow w) (NoOverflow w) (NoOverflow w) where
  hMul := NoOverflow.mul

instance {w} : HSub (NoOverflow w) (NoOverflow w) (NoOverflow w) where
  hSub := NoOverflow.sub

def _root_.BitVec.toNonOverflowing {w}
  (x : BitVec w) : NoOverflow w := NoOverflow.const x

/--
Evaluate a `NoOverflow` expression tree, giving the value and the proof that it does not overflow.
-/
@[memory_defs_bv]
def NoOverflow.eval {w} : NoOverflow w → BitVec w × Prop
| .const x => (x, True)
| .add x y =>
  let (vx, hx) := x.eval
  let (vy, hy) := y.eval
  let vout := vx + vy
  let hout := hx ∧ hy ∧ vout ≥ vx ∧ vout ≥ vy
  (vout, hout)
| .sub x y =>
  let (vx, hx) := x.eval
  let (vy, hy) := y.eval
  let vout := vx - vy
  let hout := hx ∧ hy ∧ (vy ≤ vx) -- does this actually suffice?
  (vout, hout)
| .mul x y =>
  let (vx, hx) := x.eval
  let (vy, hy) := y.eval
  let vout := vx * vy
  let hout := hx ∧ hy ∧ (vx < (BitVec.allOnes w).udiv vy)
  (vout, hout)

/-- The assertion that the expression tree does not overflow. -/
@[memory_defs_bv]
def NoOverflow.assert {w} (x : NoOverflow w) : Prop := (x.eval).2
