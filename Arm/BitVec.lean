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
import Std.Data.Fin.Lemmas
import Std.Logic
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

-- Generate ext theorems `Std.BitVec.ext` and `Std.BitVec.ext_iff`
-- for the BitVec structure.
attribute [ext] Std.BitVec

instance : Ord (BitVec n) where
  -- Unsigned comparison
  compare := unsigned_compare

instance : Hashable (BitVec n) where
  hash x := ⟨Fin.ofNat' x.toNat (by decide)⟩

-- Checks that we have all decidable instances we need for
-- comparisons.
example : 5#4 = 5#4 := by decide
example : ¬ 4#4 = 5#4 := by decide
example : 3#4 < 4#4 := by decide
example : 3#4 <= 4#4 := by decide
example : 4#4 >= 4#4 := by decide
example : 5#4 >= 4#4 := by decide

-------------------------- Fin and BitVec Lemmas ---------------------

@[ext] protected theorem extensionality_fin (idx1 idx2 : BitVec n)
    (h0 : idx1.toFin = idx2.toFin) :
    idx1 = idx2 := by ext1; exact h0

protected theorem extensionality_fin_contrapositive
  {idx1 idx2 : BitVec n} (h0 : ¬idx1 = idx2) :
  idx1.toFin ≠ idx2.toFin := by
  have := BitVec.extensionality_fin idx1 idx2
  simp_all only [imp_false, ne_eq, not_false_eq_true]

theorem fin_bitvec_add (x y : BitVec n) :
  (x.toFin + y.toFin) = (x + y).toFin := by rfl

theorem fin_bitvec_sub (x y : BitVec n) :
  (x.toFin - y.toFin) = (x - y).toFin := by rfl

-- (FIXME) Move to Std?
theorem Fin.sub_eq_nat_if_le {n : Nat} {a b : Fin n} :
   b ≤ a -> ↑(a - b) = (a : Nat) - (b : Nat) := by
   intro h
   rw [Fin.mk_le_mk] at h
   simp only [Fin.sub_def]
   simp only [Fin.is_le', ←Nat.add_sub_assoc]
   rw [Nat.sub_add_comm h]
   simp only [Nat.add_mod_right]
   have : ↑a - ↑b < n := by omega
   simp only [Nat.mod_eq_of_lt this]
   done

theorem fin_bitvec_or (x y : BitVec n) :
  (x ||| y).toFin = (x.toFin ||| y.toFin) := by
  have h_x := Std.BitVec.isLt x
  have h_y := Std.BitVec.isLt y
  simp only [HOr.hOr, OrOp.or, Std.BitVec.or, Fin.lor, Std.BitVec.toNat, Nat.lor]
  have h_or := @Nat.bitwise_lt_two_pow x.toNat n y.toNat or h_x h_y
  have h_mod := Nat.mod_eq_of_lt h_or
  simp only [Std.BitVec.toNat] at h_mod
  simp_all only

theorem fin_bitvec_and (x y : BitVec n) :
  (x &&& y).toFin = (x.toFin &&& y.toFin) := by
  have h_x := Std.BitVec.isLt x
  have h_y := Std.BitVec.isLt y
  simp only [HAnd.hAnd, AndOp.and, Std.BitVec.and, Fin.land, Std.BitVec.toNat, Nat.land]
  have h_or := @Nat.bitwise_lt_two_pow x.toNat n y.toNat and h_x h_y
  have h_mod := Nat.mod_eq_of_lt h_or
  simp only [Std.BitVec.toNat] at h_mod
  simp_all only

theorem fin_bitvec_lt (x y : BitVec n) :
  (x.toFin < y.toFin) ↔ (x < y) := by rfl

theorem fin_bitvec_le (x y : BitVec n) :
  (x.toFin <= y.toFin) ↔ (x <= y) := by rfl

-------------------------- Nat and BitVec Lemmas ---------------------

@[ext] protected theorem extensionality_nat (idx1 idx2 : BitVec n)
    (h0 : idx1.toNat = idx2.toNat) :
    idx1 = idx2 := by
    ext; unfold Std.BitVec.toNat at h0; assumption

protected theorem extensionality_nat_contrapositive
  {idx1 idx2 : BitVec n} (h0 : ¬idx1 = idx2) :
  idx1.toNat ≠ idx2.toNat := by
  have := BitVec.extensionality_nat idx1 idx2
  simp_all only [imp_false, ne_eq, not_false_eq_true]

protected theorem toNat_lt  (x y : BitVec n) :
  (x.toNat < y.toNat) ↔ (x < y) := by rfl

protected theorem toNat_le (x y : BitVec n) :
  (x.toNat <= y.toNat) ↔ (x <= y) := by rfl

---------------------------- Comparison Lemmas -----------------------

@[simp] protected theorem not_lt {n : Nat} {a b : BitVec n} : ¬ a < b ↔ b ≤ a := by
  exact Fin.not_lt ..

protected theorem lt_of_le_ne (x y : BitVec n)
  (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  simp [←BitVec.toNat_lt]
  simp [←BitVec.toNat_le] at h1
  have := BitVec.extensionality_nat_contrapositive h2
  simp_all [Nat.lt_of_le_of_ne]

protected theorem le_of_eq (x y : BitVec n) (h : x = y) :
  x <= y := by
  simp [←BitVec.toNat_le]
  exact Nat.le_of_eq (congrArg Std.BitVec.toNat h)

protected theorem lt_iff_val_lt_val {a b : Std.BitVec n} :
  a < b ↔ a.toNat < b.toNat := by
  exact Fin.lt_iff_val_lt_val ..

protected theorem le_iff_val_le_val {a b : Std.BitVec n} :
  a ≤ b ↔ a.toNat ≤ b.toNat := by
  exact Fin.mk_le_mk ..

@[simp]
protected theorem val_bitvec_lt {n : Nat} {a b : Std.BitVec n} :
  a.toNat < b.toNat ↔ a < b := by
  exact Fin.mk_lt_mk ..

@[simp]
protected theorem val_bitvec_le {n : Nat} {a b : Std.BitVec n} :
  a.toNat ≤ b.toNat ↔ a ≤ b := by
  exact Fin.mk_le_mk ..

protected theorem val_nat_le (x y n : Nat)
  (h0 : x <= y) (h1 : x < 2^n) (h2 : y < 2^n) : x#n <= y#n := by
  rw [BitVec.le_iff_val_le_val]
  simp [Std.BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h1]
  rw [Nat.mod_eq_of_lt h2]
  trivial

----------------------------- Add/Sub  Lemmas ------------------------

protected theorem zero_le_sub (x y : BitVec n) :
  0#n <= x - y := by
  refine (BitVec.toNat_le (0#n) (x - y)).mp ?a
  simp only [toNat_ofNat, Nat.zero_mod, Nat.zero_le]

theorem BitVec.sub_eq_nat_if_le {n : Nat} {a b : Std.BitVec n} :
   b ≤ a -> (a - b).toNat = a.toNat - b.toNat := by
   intro h   
   exact Fin.sub_eq_nat_if_le h

----------------------------- Logical  Lemmas ------------------------

@[simp]
protected theorem zero_or (x : BitVec n) : 0#n ||| x = x := by
  ext
  simp only [toNat_or, toNat_ofNat, Nat.zero_mod, Nat.or_zero]

------------------- ZeroExtend/Append/Extract  Lemmas ----------------

@[simp]
theorem zeroExtend_zero_width : (zeroExtend 0 x) = 0#0 := by
  unfold zeroExtend
  split <;> simp only [Std.BitVec.eq_nil]

theorem extractLsb_eq (x : BitVec n) (h : n = n - 1 + 1) :
  Std.BitVec.extractLsb (n - 1) 0 x = Std.BitVec.cast h x := by
  ext1
  simp [←h]

protected theorem extract_lsb_of_zeroExtend (x : BitVec n) (h : j < i) :
  extractLsb j 0 (zeroExtend i x) = zeroExtend (j + 1) x := by
  simp [extractLsb, extractLsb']
  ext
  simp [toNat_zeroExtend]    
  refine Nat.mod_mod_of_dvd (Std.BitVec.toNat x) ?h
  exact Nat.pow_dvd_pow_iff_le_right'.mpr h
  done

theorem empty_bitvector_append_left
  (x : Std.BitVec n) (h : 0 + n = n) :
  Std.BitVec.cast h (0#0 ++ x) = x := by
  ext; simp

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

theorem append_of_extract_general_nat (high low n vn : Nat) (_h : vn < 2 ^ n) :
  (((vn >>> low) % 2 ^ high) <<< low) ||| (vn % 2 ^ low) =
  (vn % 2 ^ (high + low)) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp
  by_cases h₀ : low <= i
  case pos => -- (low <= i)
    simp_all
    have h₀' : ¬(i < low) := by omega
    by_cases h1 : i - low < high
    case pos => -- (low <= i) and (i - low < high)
      have h1' : i < high + low := by omega
      simp [h1, h₀', h1']
    case neg => -- (low <= i) and ¬(i - low < high)
      have h1' : ¬ i < high + low := by omega
      simp [h₀', h1, h1']
  case neg => -- ¬(low <= i)
    have h₀' : i < low := by omega
    simp [h₀, h₀']
    by_cases h1 : i < high + low
    case pos => -- ¬(low <= i) and (i < high + low)
      simp [h1]
    case neg => -- ¬(low <= i) and ¬(i < high + low)
      omega
  done

theorem append_of_extract (n : Nat) (v : BitVec n)
  (hn0 : 0 < n) (high0 : high = n - low) (low0 : 1 <= low)
  (h : high + (low - 1 - 0 + 1) = n) :
  Std.BitVec.cast h (zeroExtend high (v >>> low) ++ extractLsb (low - 1) 0 v) = v := by
  ext
  subst high
  simp [Std.BitVec.toNat_zeroExtend, Nat.sub_add_cancel low0, Std.BitVec.shiftLeft]
  generalize hv : Std.BitVec.toNat v = vn
  have vlt := v.isLt; simp_all
  have := append_of_extract_general_nat (n - low) low n vn vlt
  simp_all [Nat.sub_add_cancel, Nat.mod_eq_of_lt]

theorem append_of_extract_general (v : BitVec n)
  (hn0 : 0 < n) (low0 : 1 <= low)
  (h1 : high = width)
  (h2 : (high + low - 1 - 0 + 1) = (width + (low - 1 - 0 + 1))) :
  Std.BitVec.cast h1 (zeroExtend high (v >>> low)) ++ extractLsb (low - 1) 0 v =
  Std.BitVec.cast h2 (extractLsb (high + low - 1) 0 v) := by
  ext
  simp [Std.BitVec.toNat_cast, Std.BitVec.toNat_append, Std.BitVec.toNat_zeroExtend]
  simp [extractLsb, extractLsb', Nat.sub_add_cancel low0, Std.BitVec.shiftLeft]
  generalize hv : Std.BitVec.toNat v = vn
  have h_vlt := v.isLt; simp_all
  have := append_of_extract_general_nat high low n vn
  simp [h_vlt, h1] at this
  rw [this]
  rw [Nat.sub_add_cancel]
  exact low0

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
---------------------    match_bv   Implementation    ----------------

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
