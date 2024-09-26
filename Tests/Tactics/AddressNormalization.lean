/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat, Tobias Grosser
-/

import Arm.Memory.AddressNormalization

/-! ## Examples -/

set_option trace.Tactic.address_normalization true in
/--
info: [Tactic.address_normalization] ⚙️ reduceModOfLt 'x.toNat % 2 ^ w'
[Tactic.address_normalization] ✅️ reduceModOfLt 'x.toNat % 2 ^ w'
-/
#guard_msgs in theorem eg₁ {w} (x : BitVec w) : x.toNat % 2 ^ w = x.toNat + 0 := by
  simp only [address_normalization]
  rfl

/-- info: 'eg₁' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₁

theorem eg₂ {w} (x y : BitVec w)  (h : x.toNat + y.toNat < 2 ^ w) :
  (x + y).toNat = x.toNat + y.toNat := by
  simp [address_normalization]

/-- info: 'eg₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₂

set_option trace.Tactic.address_normalization true in
/--
info: [Tactic.address_normalization] ⚙️ canonicalizeBinConst '(HAdd.hAdd x y)'
[Tactic.address_normalization] ⚙️ reduceModOfLt 'x.toNat + y.toNat % 2 ^ w'
[Tactic.address_normalization] ⚙️ reduceModSub 'x.toNat + y.toNat % 2 ^ w'
-/
#guard_msgs in theorem eg₃ {w} (x y : BitVec w) :
  (x + y).toNat = (x.toNat + y.toNat) % 2 ^ w := by
  simp [address_normalization]

/-- info: 'eg₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₂

theorem eg₄ {w} (x y z : BitVec w)
  (h₂ : y.toNat + z.toNat < 2 ^ w)
  (h : x.toNat * (y.toNat + z.toNat) < 2 ^ w) :
  (x * (y + z)).toNat = x.toNat * (y.toNat + z.toNat) := by
  simp [address_normalization]

/-- info: 'eg₄' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₄

theorem eg₅ {w} (x y : BitVec w) (h : x.toNat + y.toNat ≥ 2 ^ w) (h' : (x.toNat + y.toNat) - 2 ^ w < 2 ^ w) :
  (x + y).toNat = x.toNat + y.toNat - 2 ^ w := by
  simp [address_normalization]

/-- info: 'eg₅' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eg₅

set_option trace.Tactic.address_normalization true in
/--
info: [Tactic.address_normalization] ⚙️ canonicalizeBinConst '(HAdd.hAdd x 100#w)'
[Tactic.address_normalization] ✅️ canonicalizeBinConst '(HAdd.hAdd x 100#w)'
[Tactic.address_normalization] ⚙️ canonicalizeBinConst '(HAdd.hAdd 100#w x)'
-/
#guard_msgs in theorem eg₆ {w} (x : BitVec w) : x + 100#w = 100#w + x := by
  simp only [address_normalization]

/-- info: 'eg₆' depends on axioms: [propext] -/
#guard_msgs in #print axioms eg₆


theorem eg₇ {w} (x : BitVec w) : 100#w + (200#w + x) = 300#w + x := by
  simp only [address_normalization]

/-- info: 'eg₇' depends on axioms: [propext] -/
#guard_msgs in #print axioms eg₇

theorem eg₈ {w} : 100#w + 200#w = 300#w := by
  simp only [address_normalization]

/-- info: 'eg₈' depends on axioms: [propext] -/
#guard_msgs in #print axioms eg₈
