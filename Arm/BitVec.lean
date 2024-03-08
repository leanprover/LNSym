/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

-- Kitchen sink file for bitvector theorems

----------------------------------------------------------------------

import Arm.Attr

namespace BitVec

open BitVec

-- Adding some useful simp lemmas to `bitvec_rules`:
attribute [bitvec_rules] BitVec.ofFin_eq_ofNat
attribute [bitvec_rules] BitVec.extractLsb_ofFin
attribute [bitvec_rules] BitVec.zeroExtend_eq
attribute [bitvec_rules] BitVec.ofFin.injEq
attribute [bitvec_rules] BitVec.extractLsb_toNat
-- attribute [bitvec_rules] add_ofFin

----------------------------------------------------------------------
-- Some BitVec definitions

/-- Flatten a list of bitvectors into one bitvector. -/
protected def flatten {n : Nat} (xs : List (BitVec n)) : BitVec (n * xs.length) :=
  match xs with
  | [] => 0#0
  | x :: rest =>
    have h : n + n * List.length rest = n * List.length (x :: rest) := by
      simp [List.length_cons, Nat.mul_one, Nat.mul_add, Nat.succ_eq_one_add]
    BitVec.cast h (x ++ (BitVec.flatten rest))

/-- Generate a random bitvector of width n. The range of the values
can also be specified using lo and hi arguments, which default to 0
and 2^n - 1 (inclusive), respectively. -/
protected def rand (n : Nat) (lo := 0) (hi := 2^n - 1) : IO (BitVec n) := do
  pure (BitVec.ofNat n (← IO.rand lo hi))

def unsigned_compare (a b : BitVec n) : Ordering :=
  if BitVec.ult a b then .lt else if a = b then .eq else .gt

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

attribute [ext] BitVec

instance : Ord (BitVec n) where
  -- Unsigned comparison
  compare := unsigned_compare

instance : Hashable (BitVec n) where
  hash x := ⟨Fin.ofNat' x.toNat (by decide)⟩

example : 5#4 = 5#4 := by decide
example : ¬ 4#4 = 5#4 := by decide

instance BitVec.decLt {n} (a b : BitVec n) : Decidable (LT.lt a b) := Fin.decLt ..
instance BitVec.decLe {n} (a b : BitVec n) : Decidable (LE.le a b) := Fin.decLe ..

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
    idx1.toFin ≠ idx2.toFin :=
  mt (BitVec.extensionality_fin idx1 idx2) h0

theorem bitvec_zero_is_unique (x : BitVec 0) :
  x = 0#0 := by
  apply BitVec.extensionality_fin
  apply Fin.ext
  have h := x.toFin.isLt
  refine Nat.eq_of_le_of_lt_succ ?_ h
  simp only [Nat.pow_zero, Fin.fin_one_eq_zero, Nat.le_refl]

theorem fin_bitvec_add (x y : BitVec n) :
  (x.toFin + y.toFin) = (x + y).toFin := by rfl

theorem fin_bitvec_sub (x y : BitVec n) :
  (x.toFin - y.toFin) = (x - y).toFin := by rfl

theorem fin_bitvec_or (x y : BitVec n) :
  (x ||| y).toFin = (x.toFin ||| y.toFin) := by
  simp

theorem fin_bitvec_and (x y : BitVec n) :
  (x &&& y).toFin = (x.toFin &&& y.toFin) := by
  simp

theorem fin_bitvec_lt (x y : BitVec n) :
  (x.toFin < y.toFin) ↔ (x < y) := by rfl

theorem fin_bitvec_le (x y : BitVec n) :
  (x.toFin <= y.toFin) ↔ (x <= y) := by rfl

-- theorem fin_lt_asymm {n : Nat} {x y : Fin n} (h : x < y) :
--   ¬ y < x := by
--   simp_all only [not_lt]
--   exact le_of_lt h

-- instance : IsAsymm (Fin n) LT.lt := by infer_instance
-- -- x < y => ¬ y < x

-------------------------- Nat and BitVec Lemmas ---------------------

theorem bitvec_to_nat_of_nat :
  (BitVec.toNat (BitVec.ofNat n x)) = x % 2^n := by
  simp [toNat_ofNat]

theorem bitvec_of_nat_to_nat (n : Nat) (x : BitVec n) :
   (BitVec.ofNat n (BitVec.toNat x)) = x := by
   simp [ofNat_toNat]

@[ext] protected theorem extensionality_nat (idx1 idx2 : BitVec n)
    (h0 : idx1.toNat = idx2.toNat) :
    idx1 = idx2 := by
    ext; unfold BitVec.toNat at h0; assumption

protected theorem extensionality_nat_contrapositive
  {idx1 idx2 : BitVec n} (h0 : ¬idx1 = idx2) :
    idx1.toNat ≠ idx2.toNat :=
  mt (BitVec.extensionality_nat idx1 idx2) h0

theorem nat_bitvec_lt (x y : BitVec n) :
  (x.toNat < y.toNat) ↔ (x < y) := by rfl

theorem nat_bitvec_le (x y : BitVec n) :
  (x.toNat <= y.toNat) ↔ (x <= y) := by rfl

theorem nat_bitvec_add (x y : BitVec n) :
  (x + y).toNat = (x.toNat + y.toNat) % 2 ^ n := rfl

theorem nat_bitvec_sub (x y : BitVec n) :
  (x - y).toNat = (x.toNat + (2^n - y.toNat)) % 2^n := rfl

-- theorem nat_bitvec_or (x y : BitVec n) :
--   (x ||| y).toNat = (x.toNat ||| y.toNat) := ...

-- theorem nat_bitvec_and (x y : BitVec n) :
--   (x &&& y).toNat = (x.toNat &&& y.toNat) := by ...


---------------------------- Comparison Lemmas -----------------------

@[simp] protected theorem not_lt {n : Nat} {a b : BitVec n} : ¬ a < b ↔ b ≤ a := by
  exact Fin.not_lt ..

-- protected theorem lt_of_le_ne (x y : BitVec n) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
--   simp only [←nat_bitvec_le] at h1
--   replace h2 := BitVec.extensionality_nat_contrapositive h2
--   simp only [←nat_bitvec_lt]
--   omega

protected theorem le_of_eq (x y : BitVec n) (h : x = y) :
  x <= y := by
  simp [←nat_bitvec_le]
  exact Nat.le_of_eq (congrArg BitVec.toNat h)

protected theorem lt_iff_val_lt_val {a b : BitVec n} : a < b ↔ a.toNat < b.toNat :=
  Iff.rfl

protected theorem le_iff_val_le_val {a b : BitVec n} : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Iff.rfl

@[simp]
protected theorem val_bitvec_lt {n : Nat} {a b : BitVec n} : a.toNat < b.toNat ↔ a < b :=
  Iff.rfl

@[simp]
protected theorem val_bitvec_le {n : Nat} {a b : BitVec n} : a.toNat ≤ b.toNat ↔ a ≤ b :=
  Iff.rfl

protected theorem val_nat_le (x y n : Nat)
  (h0 : x <= y) (h1 : x < 2^n) (h2 : y < 2^n) : x#n <= y#n := by
  rw [BitVec.le_iff_val_le_val]
  simp [bitvec_to_nat_of_nat]
  rw [Nat.mod_eq_of_lt h1]
  rw [Nat.mod_eq_of_lt h2]
  trivial

----------------------------- Add/Sub  Lemmas ------------------------

-- protected theorem add_comm (x y : BitVec n) : x + y = y + x := by
--   ext
--   simp [nat_bitvec_add, bitvec_to_nat_of_nat]
--   revert x
--   simp only [BitVec, BitVec.toNat, Nat.add_comm, forall_const]

-- @[simp]
-- protected theorem zero_add (x : BitVec n) : (0#n) + x = x := by
--   simp [BitVec.add_comm, BitVec.add_zero]

protected theorem zero_le_sub (x y : BitVec n) :
  0#n <= x - y := by
  refine (BitVec.nat_bitvec_le (0#n) (x - y)).mp ?a
  simp only [toNat_ofNat, Nat.zero_mod, toNat_sub, Nat.zero_le]

-- @[simp]
-- protected theorem sub_zero (x : BitVec n) : x - (0#n) = x := by
--   ext
--   simp [nat_bitvec_sub, bitvec_to_nat_of_nat]

-- @[simp]
-- protected theorem sub_self (x : BitVec n) : x - x = (0#n) := by
--   ext
--   simp [nat_bitvec_sub, bitvec_to_nat_of_nat]

----------------------------- Logical  Lemmas ------------------------

@[simp]
protected theorem zero_or (x : BitVec n) : 0#n ||| x = x := by
  unfold HOr.hOr instHOr OrOp.or instOrOpBitVec BitVec.or
  simp only [toNat_ofNat, Nat.or_zero]
  congr

theorem BitVec.toNat_or (x y : BitVec n):
  BitVec.toNat (x ||| y) = BitVec.toNat x ||| BitVec.toNat y := by
  rw [←BitVec.or_eq]
  simp [BitVec.or]

--------------------- ZeroExtend/Append/Extract  Lemmas ----------------

@[simp]
theorem zeroExtend_zero_width : (zeroExtend 0 x) = 0#0 := by
  unfold zeroExtend
  split <;> simp [bitvec_zero_is_unique]

theorem extractLsb_eq (x : BitVec n) (h : n = n - 1 + 1) :
  BitVec.extractLsb (n - 1) 0 x = BitVec.cast h x := by
  unfold extractLsb extractLsb'
  ext1
  simp [←h]

protected theorem extract_lsb_of_zeroExtend (x : BitVec n) (h : j < i) :
    extractLsb j 0 (zeroExtend i x) = zeroExtend (j + 1) x := by
  apply BitVec.eq_of_getLsb_eq
  simp
  intro k
  have q : k < i := by omega
  by_cases h : decide (k ≤ j) <;> simp [q, h]
  simp_all
  omega

theorem empty_bitvector_append_left
  (x : BitVec n) (h : 0 + n = n) :
  BitVec.cast h (0#0 ++ x) = x := by
  simp [HAppend.hAppend, BitVec.append, shiftLeftZeroExtend, zeroExtend']
  simp [HOr.hOr, OrOp.or, BitVec.or, Nat.lor]
  unfold Nat.bitwise
  simp [BitVec.cast]
  rfl

-- In case we need ▸ instead of BitVec.cast (and we should really
-- try not to need ▸ because it may break the cast API), applying
-- my_bv_cast_eq_cast and then unfold my_bv_cast should do the trick,
-- like in empty_bitvector_append_left_triangle below.
def my_bv_cast (h : n = m) (x : BitVec n) : BitVec m := h ▸ x

theorem my_bv_cast_eq_cast (x : BitVec n) (h : n = m) :
  my_bv_cast h x = BitVec.cast h x := by
  subst_vars
  simp only [my_bv_cast, BitVec.cast_eq]

theorem empty_bitvector_append_left_triangle
  (x : BitVec n) (h : 0 + n = n) :
  (h ▸ (0#0 ++ x)) = x := by
  have h1 := empty_bitvector_append_left x h
  have h2 := @my_bv_cast_eq_cast
  unfold my_bv_cast at h2
  rw [h2]
  trivial

theorem append_of_extract_general_nat (high low n vn : Nat) (h : vn < 2 ^ n) :
  ((((vn >>> low) % 2 ^ n) % 2 ^ high) <<< low) ||| (vn % 2 ^ low) =
  (vn % 2 ^ (high + low)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]
  by_cases h₀ : (low <= i) ..
  case pos => -- low <= i
    by_cases h₁ : (i < n) ..
    case pos => -- (low <= i) and (i < n)
      simp_all only [decide_True, Bool.true_and]
      have h1 : vn % 2^low < 2^i :=
        calc
         _ < 2^low := by apply Nat.mod_lt; exact Nat.two_pow_pos low
         _ <= 2^i := by apply Nat.pow_le_pow_right; decide; assumption
      simp only [Nat.testBit_lt_two_pow h1, Bool.or_false]
      simp_all only [Nat.testBit_mod_two_pow]
      simp only [Nat.testBit_shiftRight]
      have h3 : i - low < n := by omega
      simp_all [Nat.add_sub_cancel]
      have h4 : (i - low < high) ↔ (i < high + low) := by omega
      simp_all
    case neg => -- (low <= i) and (n <= i)
      simp_all [Nat.not_lt, Nat.testBit_mod_two_pow]
      have h4 : (i - low < high) ↔ (i < high + low) := by omega
      have h5 : ¬(i - low < n - low) := by omega
      have h6 : ¬(i < low) := by omega
      simp [h5, h6]
      rw [Nat.testBit_lt_two_pow]
      · simp [*]
      · apply Nat.lt_of_lt_of_le h
        rwa [Nat.pow_le_pow_iff_right Nat.one_lt_two]
  case neg => -- (i < low)
    simp [h₀]
    simp_all [Nat.testBit_mod_two_pow]
    have h11 : i < high + low := by omega
    simp_all
  done

theorem append_of_extract (n : Nat) (v : BitVec n)
  (hn0 : 0 < n) (high0 : high = n - low) (low0 : 1 <= low)
  (h : high + (low - 1 - 0 + 1) = n) :
  BitVec.cast h (zeroExtend high (v >>> low) ++ extractLsb (low - 1) 0 v) = v := by
  ext
  subst high
  have vlt := v.isLt; simp_all only [Nat.sub_zero]
  have := append_of_extract_general_nat (n - low) low n (BitVec.toNat v) vlt
  have low_le : low ≤ n := by omega
  simp_all [toNat_zeroExtend, Nat.sub_add_cancel, low_le]
  rw [Nat.mod_eq_of_lt (b := 2 ^ n)] at this
  · rw [this]
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) vlt

theorem append_of_extract_general (v : BitVec n)
  (hn0 : 0 < n) (low0 : 1 <= low)
  (h1 : high = width)
  (h2 : (high + low - 1 - 0 + 1) = (width + (low - 1 - 0 + 1))) :
  BitVec.cast h1 (zeroExtend high (v >>> low)) ++ extractLsb (low - 1) 0 v =
  BitVec.cast h2 (extractLsb (high + low - 1) 0 v) := by
  ext
  have := append_of_extract_general_nat high low n (BitVec.toNat v)
  have h_vlt := v.isLt; simp_all only [Nat.sub_zero, h1]
  simp only [h_vlt, h1, forall_prop_of_true] at this
  have low' : 1 ≤ width + low := Nat.le_trans low0 (Nat.le_add_left low width)
  simp_all [toNat_zeroExtend, Nat.sub_add_cancel]
  rw [Nat.mod_eq_of_lt (b := 2 ^ n)] at this
  · rw [this]
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h_vlt

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
  simp only [truncate_append, Nat.le_refl, ↓reduceDite, zeroExtend_eq]

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
    let r ← `(BitVec.ofNat $(quote len) $(quote val))
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
      let test ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var == $bv)
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
      let rhs ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var)
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
