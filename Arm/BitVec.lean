/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/

-- Kitchen sink file for bitvector theorems

import Std.Data.BitVec.Lemmas
import Std.Tactic.Basic
import Std.Tactic.Ext
import Std.Data.Nat.Lemmas
import Std.Data.Fin.Lemmas
import Std.Data.Nat.Bitwise
import Std.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Contrapose
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Pow

----------------------------------------------------------------------

abbrev BitVec := Std.BitVec

namespace BitVec

open Std.BitVec

----------------------------------------------------------------------
-- Some BitVec definitions

/-- Flatten a list of bitvectors into one bitvector. -/
protected def flatten {n : Nat} (xs : List (BitVec n)) : BitVec (n * xs.length) :=
  match xs with
  | [] => 0#0
  | x :: rest =>
    have h : n + n * List.length rest = n * List.length (x :: rest) := by
      simp [List.length_cons, Nat.mul_one, Nat.mul_add, Nat.succ_eq_one_add]
    Std.BitVec.cast h (x ++ (BitVec.flatten rest))

/-- Generate a random bitvector of width n. The range of the values
can also be specified using lo and hi arguments, which default to 0
and 2^n - 1 (inclusive), respectively. -/
protected def rand (n : Nat) (lo := 0) (hi := 2^n - 1) : IO (BitVec n) := do
  pure (Std.BitVec.ofNat n (← IO.rand lo hi))

def unsigned_compare (a b : BitVec n) : Ordering :=
  if Std.BitVec.ult a b then .lt else if a = b then .eq else .gt

abbrev extract (bv : BitVec n) (hi : Nat) (lo : Nat) : BitVec (hi - lo + 1) :=
  extractLsb hi lo bv

abbrev ror (x : BitVec n) (r : Nat) : BitVec n :=
  rotateRight x r

abbrev partInstall (hi lo : Nat) (val : BitVec (hi - lo + 1)) (x : BitVec n): BitVec n :=
  let mask := allOnes (hi - lo + 1)
  let val_aligned := (zeroExtend n val) <<< lo
  let mask_with_hole := ~~~ ((zeroExtend n mask) <<< lo)
  let x_with_hole := x &&& mask_with_hole
  x_with_hole ||| val_aligned

example : (partInstall 3 0 0xC#4 0xAB0D#16 = 0xAB0C#16) := by native_decide

----------------------------------------------------------------------

attribute [ext] Std.BitVec

instance : Ord (BitVec n) where
  -- Unsigned comparison
  compare := unsigned_compare

instance : Hashable (BitVec n) where
  hash x := ⟨Fin.ofNat' x.toNat (by decide)⟩

example : 5#4 = 5#4 := by decide
example : ¬ 4#4 = 5#4 := by decide

instance Std.BitVec.decLt {n} (a b : Std.BitVec n) : Decidable (LT.lt a b) := Fin.decLt ..
instance Std.BitVec.decLe {n} (a b : Std.BitVec n) : Decidable (LE.le a b) := Fin.decLe ..

-- The following can be discharged by the decide tactic only after
-- creating the instances above.
example : 3#4 < 4#4 := by decide
example : 3#4 <= 4#4 := by decide
example : 4#4 >= 4#4 := by decide
example : 5#4 >= 4#4 := by decide

-------------------------- Fin and BitVec Lemmas ---------------------

@[ext] protected theorem extensionality_fin (idx1 idx2 : BitVec n)
    (h0 : idx1.toFin = idx2.toFin) :
    idx1 = idx2 := by
    ext
    exact congrArg Fin.val h0

protected theorem extensionality_fin_contrapositive
  {idx1 idx2 : BitVec n} (h0 : ¬idx1 = idx2) :
    idx1.toFin ≠ idx2.toFin := by
    contrapose h0
    push_neg at *
    exact BitVec.extensionality_fin idx1 idx2 h0

theorem bitvec_zero_is_unique (x : BitVec 0) :
  x = 0#0 := by
  apply BitVec.extensionality_fin
  apply Fin.ext
  have h := x.toFin.isLt
  refine Nat.eq_of_le_of_lt_succ ?_ h
  simp

theorem fin_bitvec_add (x y : BitVec n) :
  (x.toFin + y.toFin) = (x + y).toFin := by rfl

theorem fin_bitvec_sub (x y : BitVec n) :
  (x.toFin - y.toFin) = (x - y).toFin := by rfl

theorem fin_bitvec_or (x y : BitVec n) :
  (x ||| y).toFin = (x.toFin ||| y.toFin) := by
  have h_x := Std.BitVec.isLt x
  have h_y := Std.BitVec.isLt y
  simp [HOr.hOr, OrOp.or, Std.BitVec.or, Fin.lor, Std.BitVec.toNat, Nat.lor]
  have h_or := @Nat.bitwise_lt_two_pow x.toNat n y.toNat or h_x h_y
  have h_mod := Nat.mod_eq_of_lt h_or
  simp [Std.BitVec.toNat] at h_mod
  simp_all

theorem fin_bitvec_and (x y : BitVec n) :
  (x &&& y).toFin = (x.toFin &&& y.toFin) := by
  have h_x := Std.BitVec.isLt x
  have h_y := Std.BitVec.isLt y
  simp [HAnd.hAnd, AndOp.and, Std.BitVec.and, Fin.land, Std.BitVec.toNat, Nat.land]
  have h_or := @Nat.bitwise_lt_two_pow x.toNat n y.toNat and h_x h_y
  have h_mod := Nat.mod_eq_of_lt h_or
  simp [Std.BitVec.toNat] at h_mod
  simp_all

theorem fin_bitvec_lt (x y : BitVec n) :
  (x.toFin < y.toFin) ↔ (x < y) := by rfl

theorem fin_bitvec_le (x y : BitVec n) :
  (x.toFin <= y.toFin) ↔ (x <= y) := by rfl

-- theorem fin_lt_asymm {n : ℕ} {x y : Fin n} (h : x < y) :
--   ¬ y < x := by
--   simp_all only [not_lt]
--   exact le_of_lt h

-- instance : IsAsymm (Fin n) LT.lt := by infer_instance
-- -- x < y => ¬ y < x

-------------------------- Nat and BitVec Lemmas ---------------------

theorem bitvec_to_nat_of_nat :
  (Std.BitVec.toNat (Std.BitVec.ofNat n x)) = x % 2^n := by
  simp [toNat_ofNat]

theorem bitvec_of_nat_to_nat (n : Nat) (x : BitVec n) :
   (Std.BitVec.ofNat n (Std.BitVec.toNat x)) = x := by
   simp [ofNat_toNat]

@[ext] protected theorem extensionality_nat (idx1 idx2 : BitVec n)
    (h0 : idx1.toNat = idx2.toNat) :
    idx1 = idx2 := by
    ext; unfold Std.BitVec.toNat at h0; assumption

protected theorem extensionality_nat_contrapositive
  {idx1 idx2 : BitVec n} (h0 : ¬idx1 = idx2) :
    idx1.toNat ≠ idx2.toNat := by
    contrapose h0
    push_neg at *
    exact BitVec.extensionality_nat idx1 idx2 h0

theorem nat_bitvec_lt (x y : BitVec n) :
  (x.toNat < y.toNat) ↔ (x < y) := by rfl

theorem nat_bitvec_le (x y : BitVec n) :
  (x.toNat <= y.toNat) ↔ (x <= y) := by rfl

-- set_option trace.Meta.synthInstance true in
theorem nat_bitvec_add (x y : BitVec n) :
  (x + y).toNat = (x.toNat + y.toNat) % 2 ^ n := by
  unfold Std.BitVec.toNat
  rw [←BitVec.fin_bitvec_add];
  simp only [HAdd.hAdd, Add.add, Fin.add, Nat.add_eq]

theorem nat_bitvec_sub (x y : BitVec n) :
  (x - y).toNat = (x.toNat + (2^n - y.toNat)) % 2^n := by
  unfold Std.BitVec.toNat
  rw [←BitVec.fin_bitvec_sub];
  simp only [HSub.hSub, Sub.sub, Fin.sub, Nat.sub_eq]

-- theorem nat_bitvec_or (x y : BitVec n) :
--   (x ||| y).toNat = (x.toNat ||| y.toNat) := ...

-- theorem nat_bitvec_and (x y : BitVec n) :
--   (x &&& y).toNat = (x.toNat &&& y.toNat) := by ...


---------------------------- Comparison Lemmas -----------------------

@[simp] protected theorem not_lt {n : Nat} {a b : BitVec n} : ¬ a < b ↔ b ≤ a := by
  exact Fin.not_lt ..

protected theorem lt_of_le_ne (x y : BitVec n) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  contrapose h2
  push_neg
  have h3 : y <= x := by simp_all only [BitVec.not_lt]
  ext
  simp [←nat_bitvec_le] at h1
  simp [←nat_bitvec_le] at h3
  exact Nat.le_antisymm h1 h3

protected theorem le_of_eq (x y : BitVec n) (h : x = y) :
  x <= y := by
  simp [←nat_bitvec_le]
  exact Nat.le_of_eq (congrArg Std.BitVec.toNat h)

protected theorem lt_iff_val_lt_val {a b : Std.BitVec n} : a < b ↔ a.toNat < b.toNat := by
  exact Fin.lt_iff_val_lt_val ..

protected theorem le_iff_val_le_val {a b : Std.BitVec n} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  exact Fin.le_iff_val_le_val ..

@[simp]
protected theorem val_bitvec_lt {n : ℕ} {a b : Std.BitVec n} : a.toNat < b.toNat ↔ a < b := by
  exact Fin.val_fin_lt ..

@[simp]
protected theorem val_bitvec_le {n : ℕ} {a b : Std.BitVec n} : a.toNat ≤ b.toNat ↔ a ≤ b := by
  exact Fin.val_fin_le ..

protected theorem val_nat_le (x y n : Nat)
  (h0 : x <= y) (h1 : x < 2^n) (h2 : y < 2^n) : x#n <= y#n := by
  rw [BitVec.le_iff_val_le_val]
  simp [bitvec_to_nat_of_nat]
  rw [Nat.mod_eq_of_lt h1]
  rw [Nat.mod_eq_of_lt h2]
  trivial

----------------------------- Add/Sub  Lemmas ------------------------

protected theorem add_comm (x y : BitVec n) : x + y = y + x := by
  ext
  simp [nat_bitvec_add, bitvec_to_nat_of_nat]
  revert x
  simp only [BitVec, Std.BitVec.toNat, Nat.add_comm, forall_const]

@[simp]
protected theorem zero_add (x : BitVec n) : (0#n) + x = x := by
  simp [BitVec.add_comm, Std.BitVec.add_zero]

protected theorem zero_le_sub (x y : BitVec n) :
  0#n <= x - y := by
  refine (BitVec.nat_bitvec_le (0#n) (x - y)).mp ?a
  simp only [toNat_zero, zero_le]

@[simp]
protected theorem sub_zero (x : BitVec n) : x - (0#n) = x := by
  ext
  simp [nat_bitvec_sub, bitvec_to_nat_of_nat]
  revert x
  simp [BitVec, Std.BitVec.toNat, Fin.isLt, Nat.mod_eq_of_lt]

@[simp]
protected theorem sub_self (x : BitVec n) : x - x = (0#n) := by
  ext
  simp [nat_bitvec_sub, bitvec_to_nat_of_nat]
  revert n
  simp [BitVec, Std.BitVec.toNat, Fin.isLt, Nat.mod_eq_of_lt]

----------------------------- Logical  Lemmas ------------------------

@[simp]
protected theorem zero_or (x : BitVec n) : 0#n ||| x = x := by
  unfold HOr.hOr instHOr OrOp.or instOrOpBitVec Std.BitVec.or
  simp only [toNat_zero, Nat.or_zero]
  congr

theorem BitVec.toNat_or (x y : BitVec n):
  Std.BitVec.toNat (x ||| y) = Std.BitVec.toNat x ||| Std.BitVec.toNat y := by
  rw [←Std.BitVec.or_eq]
  simp [Std.BitVec.or]

--------------------- ZeroExtend/Append/Extract  Lemmas ----------------

@[simp]
theorem zeroExtend_zero_width : (zeroExtend 0 x) = 0#0 := by
  unfold zeroExtend
  split <;> simp [bitvec_zero_is_unique]

theorem extractLsb_eq (x : BitVec n) (h : n = n - 1 + 1) :
  Std.BitVec.extractLsb (n - 1) 0 x = Std.BitVec.cast h x := by
  unfold extractLsb extractLsb'
  ext1
  simp [←h]
  have l1 := x.isLt
  rw [Nat.mod_eq_of_lt]
  assumption

protected theorem extract_eq (x : BitVec n) (h : n = n - 1 + 1) :
  extract x (n - 1) 0 = Std.BitVec.cast h x := by
  simp [extract]
  rw [extractLsb_eq]

protected theorem extract_lsb_of_zeroExtend (x : BitVec n) (h : j < i) :
  BitVec.extract (zeroExtend i x) j 0 = zeroExtend (j + 1) x := by
  simp [BitVec.extract, extractLsb, extractLsb']
  ext
  simp [toNat_zeroExtend]
  refine Nat.mod_mod_of_dvd (Std.BitVec.toNat x) ?h  
  exact Nat.pow_dvd_pow_iff_le_right'.mpr h
  done

theorem empty_bitvector_append_left
  (x : Std.BitVec n) (h : 0 + n = n) :
  Std.BitVec.cast h (0#0 ++ x) = x := by
  simp [HAppend.hAppend, Std.BitVec.append, shiftLeftZeroExtend, zeroExtend']
  simp [HOr.hOr, OrOp.or, Std.BitVec.or, Nat.lor]
  unfold Nat.bitwise
  simp [Std.BitVec.cast]
  rfl

-- In case we need ▸ instead of Std.BitVec.cast (and we should really
-- try not to need ▸ because it may break the cast API), applying
-- my_bv_cast_eq_cast and then unfold my_bv_cast should do the trick,
-- like in empty_bitvector_append_left_triangle below.
def my_bv_cast (h : n = m) (x : Std.BitVec n) : Std.BitVec m := h ▸ x

theorem my_bv_cast_eq_cast (x : Std.BitVec n) (h : n = m) :
  my_bv_cast h x = Std.BitVec.cast h x := by
  subst_vars
  simp only [my_bv_cast, Std.BitVec.cast_eq]

theorem empty_bitvector_append_left_triangle
  (x : Std.BitVec n) (h : 0 + n = n) :
  (h ▸ (0#0 ++ x)) = x := by
  have h1 := empty_bitvector_append_left x h
  have h2 := @my_bv_cast_eq_cast
  unfold my_bv_cast at h2
  rw [h2]
  trivial

theorem append_of_extract_general_nat (high low n vn : ℕ) (h : vn < 2 ^ n) :
  ((((vn >>> low) % 2 ^ n) % 2 ^ high) <<< low) ||| (vn % 2 ^ low) =
  (vn % 2 ^ (high + low)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h₀ : (low <= i) ..
  case pos => -- low <= i
    by_cases h₁ : (i < n) ..
    case pos => -- (low <= i) and (i < n)
      simp_all only [decide_True, Bool.true_and]
      have h1 : vn % 2^low < 2^i :=
        calc
         _ < 2^low := by apply Nat.mod_lt; exact Nat.pow_two_pos low
         _ <= 2^i := by apply Nat.pow_le_pow_right; decide; assumption
      simp [Nat.testBit_lt_two h1]
      simp_all only [Nat.testBit_mod_two_pow]
      simp only [Nat.testBit_shiftRight]
      have h3 : i - low < n := by omega
      simp_all [add_tsub_cancel_of_le]
      have h4 : (i - low < high) = (i < high + low) := by 
        rw [tsub_lt_iff_right]; assumption
      simp_all
    case neg => -- (low <= i) and (n <= i)
      simp_all [not_lt, Nat.testBit_mod_two_pow]
      have h4 : (i - low < high) = (i < high + low) := by 
        rw [tsub_lt_iff_right]; assumption
      have h5 : ¬(i - low < n - low) := by omega
      have h6 : ¬(i < low) := by omega
      simp [h5, h6]
      have h8 : 2^(n - low) <= 2^(i - low) := by
        apply Nat.pow_le_pow_right; decide; omega
      have h9 : ¬(i < n) := by omega
      rw [Nat.testBit_lt_two]
      · simp [*]
        have := Nat.testBit_mod_two_pow vn n i
        rw [Nat.mod_eq_of_lt h] at this
        simp [h9] at this
        simp [this]
      · simp [Nat.shiftRight_eq_div_pow]
        by_cases h₂ : n <= low
        case pos => -- (low <= i) and (n <= i) and (n <= low)
          have h10 : vn < 2^low :=
            calc
            _ < 2^n := h
            _ <= 2^low := by apply Nat.pow_le_pow_right; decide; exact h₂
          have := Nat.div_eq_of_lt h10
          simp_all
        case neg => -- (low <= i) and (n <= i) and (low < n)
          simp at h₂
          have h1 : vn / 2^low < 2^(n - low) := by
            rw [Nat.div_lt_iff_lt_mul]
            · simp [←Nat.pow_add]
              rw [Nat.sub_add_cancel]
              exact h
              omega
            · exact Nat.two_pow_pos low
          omega
  case neg => -- (i < low)
    simp [h₀]
    simp_all [Nat.testBit_mod_two_pow]
    have h11 : i < high + low := by omega
    simp_all
  done

theorem append_of_extract (n : Nat) (v : BitVec n)
  (hn0 : 0 < n) (high0 : high = n - low) (low0 : 1 <= low)
  (h : high + (low - 1 - 0 + 1) = n) :
  Std.BitVec.cast h (zeroExtend high (v >>> low) ++ BitVec.extract v (low - 1) 0) = v := by
  ext
  subst high
  simp [Std.BitVec.toNat_cast, Std.BitVec.toNat_append, Std.BitVec.toNat_zeroExtend]
  simp [BitVec.extract, extractLsb, extractLsb', Nat.sub_add_cancel low0]
  simp [HShiftRight.hShiftRight, ushiftRight, ShiftRight.shiftRight]
  simp [HShiftLeft.hShiftLeft, Std.BitVec.shiftLeft, BitVec.bitvec_to_nat_of_nat]
  generalize hv : Std.BitVec.toNat v = vn
  have vlt := v.isLt; simp_all
  have := append_of_extract_general_nat (n - low) low n vn vlt
  simp_all [ShiftLeft.shiftLeft, Nat.sub_add_cancel, Nat.mod_eq_of_lt]
  done

theorem append_of_extract_general (v : BitVec n)
  (hn0 : 0 < n) (low0 : 1 <= low)
  (h1 : high = width)
  (h2 : (high + low - 1 - 0 + 1) = (width + (low - 1 - 0 + 1))) :
  Std.BitVec.cast h1 (zeroExtend high (v >>> low)) ++ BitVec.extract v (low - 1) 0 =
  Std.BitVec.cast h2 (BitVec.extract v (high + low - 1) 0) := by
  ext
  simp [Std.BitVec.toNat_cast, Std.BitVec.toNat_append, Std.BitVec.toNat_zeroExtend]
  simp [BitVec.extract, extractLsb, extractLsb', Nat.sub_add_cancel low0]
  simp [HShiftRight.hShiftRight, ushiftRight, ShiftRight.shiftRight]
  simp [HShiftLeft.hShiftLeft, Std.BitVec.shiftLeft, BitVec.bitvec_to_nat_of_nat]
  generalize hv : Std.BitVec.toNat v = vn
  simp [ShiftLeft.shiftLeft]
  have h_vlt := v.isLt; simp_all
  have := append_of_extract_general_nat high low n vn
  simp [h_vlt, h1] at this
  rw [this]
  rw [Nat.sub_add_cancel]
  exact low0
  done

theorem leftshift_n_or_mod_2n :
  (x <<< n ||| y) % 2 ^ n = y % 2 ^ n := by
  simp [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_mod_two_pow]
  by_cases h₀ : i < n
  case pos =>
    simp [h₀, Nat.testBit_or]
    rw [@Nat.mul_comm x (2^n)]
    simp [Nat.testBit_mul_pow_two]
    have : ¬(n <= i) := by omega
    simp [this]
  case neg =>
    simp [h₀]

protected theorem truncate_to_lsb_of_append (m n : Nat) (x : BitVec m) (y : BitVec n) :
  truncate n (x ++ y) = y := by
  ext
  simp [Std.BitVec.toNat_truncate, Std.BitVec.toNat_append]
  apply Nat.eq_of_testBit_eq; intro i
  have := y.isLt
  rw [leftshift_n_or_mod_2n, Nat.mod_eq_of_lt]
  exact this

----------------------------------------------------------------------

/- Bitvector pattern component syntax category, originally written by
Leonardo de Moura. -/
declare_syntax_cat bvpat_comp
syntax num : bvpat_comp
syntax ident ":" num : bvpat_comp

/--
Bitvector pattern syntax category.
Example: [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5]
-/
declare_syntax_cat bvpat
syntax "[" bvpat_comp,* "]" : bvpat

open Lean

abbrev BVPatComp := TSyntax `bvpat_comp
abbrev BVPat := TSyntax `bvpat

/-- Return the number of bits in a bit-vector component pattern. -/
def BVPatComp.length (c : BVPatComp) : Nat := Id.run do
  match c with
  | `(bvpat_comp| $n:num) =>
    let some str := n.raw.isLit? `num | pure 0
    return str.length
  | `(bvpat_comp| $_:ident : $n:num) =>
    return n.raw.toNat
  | _ =>
    return 0

/--
If the pattern component is a bitvector literal, convert it into a bit-vector term
denoting it.
-/
def BVPatComp.toBVLit? (c : BVPatComp) : MacroM (Option Term) := do
  match c with
  | `(bvpat_comp| $n:num) =>
    let len := c.length
    let some str := n.raw.isLit? `num | Macro.throwErrorAt c "invalid bit-vector literal"
    let bs := str.toList
    let mut val := 0
    for b in bs do
      if b = '1' then
        val := 2*val + 1
      else if b = '0' then
        val := 2*val
      else
        Macro.throwErrorAt c "invalid bit-vector literal, '0'/'1's expected"
    let r ← `(Std.BitVec.ofNat $(quote len) $(quote val))
    return some r
  | _ => return none

/--
If the pattern component is a pattern variable of the form `<id>:<size>` return
`some id`.
-/
def BVPatComp.toBVVar? (c : BVPatComp) : MacroM (Option (TSyntax `ident)) := do
  match c with
  | `(bvpat_comp| $x:ident : $_:num) =>
    return some x
  | _ => return none

def BVPat.getComponents (p : BVPat) : Array BVPatComp :=
  match p with
  | `(bvpat| [$comp,*]) => comp.getElems.reverse
  | _ => #[]

/--
Return the number of bits in a bit-vector pattern.
-/
def BVPat.length (p : BVPat) : Nat := Id.run do
  let mut sz := 0
  for c in p.getComponents do
    sz := sz + c.length
  return sz

/--
Return a term that evaluates to `true` if `var` is an instance of the pattern `pat`.
-/
def genBVPatMatchTest (var : Term) (pat : BVPat) : MacroM Term := do
  let mut shift := 0
  let mut result ← `(true)
  for c in pat.getComponents do
    let len := c.length
    if let some bv ← c.toBVLit? then
      let test ← `(BitVec.extract $var $(quote (shift + (len - 1))) $(quote shift) == $bv)
      result ← `($result && $test)
    shift := shift + len
  return result

/--
Given a variable `var` representing a term that matches the pattern `pat`, and a term `rhs`,
return a term of the form
```
let y₁ := var.extract ..
...
let yₙ := var.extract ..
rhs
```
where `yᵢ`s are the pattern variables in `pat`.
-/
def declBVPatVars (var : Term) (pat : BVPat) (rhs : Term) : MacroM Term := do
  let mut result := rhs
  let mut shift  := 0
  for c in pat.getComponents do
    let len := c.length
    if let some y ← c.toBVVar? then
      let rhs ← `(BitVec.extract $var $(quote (shift + (len - 1))) $(quote shift))
      result ← `(let $y := $rhs; $result)
    shift := shift + len
  return result

/--
Define the `match_bv .. with | bvpat => rhs | _ => rhs`.
The last entry is the `else`-case since we currently do not check whether
the patterns are exhaustive or not.
-/
syntax "match_bv " term "with" (atomic("| " bvpat) " => " term)* ("| " "_ " " => " term) : term
macro_rules
  | `(match_bv $discr:term with
      $[ | $ps:bvpat => $rhss:term ]*
         | _ => $rhsElse:term) => do
  let mut result := rhsElse
  let x ← `(discr)
  for p in ps, rhs in rhss do
    let test ← genBVPatMatchTest x p
    let rhs ← declBVPatVars x p rhs
    result ← `(if $test then $rhs else $result)
  `(let discr := $discr; $result)

-- def test (x : BitVec 32) : BitVec 16 :=
--   match_bv x with
--   | [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5] => sf ++ Rm ++ Rn ++ Rd
--   | [sf:1,0000010000,11111000000,Rn:5,Rd:5] => sf ++ Rn ++ Rd ++ Rd
--   | _ => 0#16

-- #print test

-- def test2 (x : BitVec 4) : BitVec 4 :=
--   match_bv x with
--   | [x1:1, x2:1, x3:1, x4:1] => x4 ++ x3 ++ x2 ++ x1
--   | _ => 0#4

-- #print test2

end BitVec
