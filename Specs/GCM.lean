/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Insts.Common

-- References: https://nvlpubs.nist.gov/nistpubs/legacy/sp/nistspecialpublication800-38d.pdf

namespace GCM

open BitVec

/-- NIST Special Publication 800-38D, page 11-12.
    This constant represents, up to x^127, the polynomial for defining GF(2^128)
    -/
def R : (BitVec 128) := 0b11100001#8 ++ 0b0#120

/-- A Cipher type is a function that takes an input of size n and
    a key of size m and returns an encrypted block of size n -/
abbrev Cipher {n : Nat} {m : Nat} :=  BitVec n → BitVec m → BitVec n

/-- The s-bit incrementing function -/
def inc_s (s : Nat) (X : BitVec l) (H₀ : s < l) : BitVec l :=
  let upper := extractLsb' s (l - s) X
  let lower := (extractLsb' 0 s X) + 0b1#s
  have h : l - s + s = l := by omega
  (upper ++ lower).cast h

def mul_aux (i : Nat) (X : BitVec 128) (Z : BitVec 128) (V : BitVec 128)
  : BitVec 128 :=
  if h : 128 ≤ i then
    Z
  else
    let Xi := getMsbD X i
    let Z := if not Xi then Z else Z ^^^ V
    let lsb_v := getLsbD V 0
    let V := if not lsb_v then V >>> 1 else (V >>> 1) ^^^ R
    mul_aux (i + 1) X Z V
  termination_by (128 - i)

/-- The GF(2^128) multiplication -/
def mul (X : BitVec 128) (Y : BitVec 128) : BitVec 128 :=
  mul_aux 0 X 0b0#128 Y

def GHASH_aux (i : Nat) (H : BitVec 128) (X : BitVec n) (Y : BitVec 128)
  (h : 128 ∣ n) : BitVec 128 :=
  if n / 128 ≤ i then
    Y
  else
    let lo := (n/128 - 1 - i) * 128
    let Xi := extractLsb' lo 128 X
    let res := Y ^^^ Xi
    let Y := mul res H
    GHASH_aux (i + 1) H X Y h
  termination_by (n / 128 - i)

/-- GHASH: hashing message X using Galois field multiplication -/
def GHASH (H : BitVec 128) (X : BitVec n) (h : 128 ∣ n) : BitVec 128 :=
  GHASH_aux 0 H X (BitVec.zero 128) h

def GCTR_aux (CIPH : Cipher (n := 128) (m := m))
  (i : Nat) (n : Nat) (K : BitVec m) (ICB : BitVec 128)
  (X : BitVec v) (Y : BitVec v) : BitVec v :=
  if n ≤ i then
    Y
  else
    let lo := (n - i - 1) * 128
    let hi := lo + 127
    have h : 128 = hi - lo + 1 := by omega
    let Xi := extractLsb' lo 128 X
    let Yi := Xi ^^^ CIPH ICB K
    let Y := BitVec.partInstall hi lo (BitVec.cast h Yi) Y
    let ICB := inc_s 32 ICB (by omega)
    GCTR_aux CIPH (i + 1) n K ICB X Y
  termination_by (n - i)

protected def ceiling_in_blocks (w : Nat) := (w - 1) / 128 + 1
protected def ceiling_in_bits (w : Nat) := (GCM.ceiling_in_blocks w) * 128

protected theorem bits_le_ceiling_in_bits (w : Nat) :
  w ≤ (GCM.ceiling_in_bits w) := by
  simp only [GCM.ceiling_in_bits, GCM.ceiling_in_blocks]
  omega

/-- GCTR: encrypting/decrypting message x using Galois counter mode -/
def GCTR (CIPH : Cipher (n := 128) (m := m))
  (K : BitVec m) (ICB : BitVec 128) (X : BitVec v) : (BitVec v) :=
  let n := GCM.ceiling_in_blocks v
  let b := GCM.ceiling_in_bits v
  let s := b - v
  let h : v + s = b := by
    simp only [s]
    apply Nat.add_sub_cancel'
          (by simp only [b]; apply GCM.bits_le_ceiling_in_bits)
  let X' : BitVec b := BitVec.cast h (shiftLeftZeroExtend X s)
  let R := GCTR_aux CIPH 0 n K ICB X' $ BitVec.zero b
  truncate v $ R >>> s

protected theorem initialize_J0_simplification
  (lv : Nat) (x : Nat) (h : lv ≤ x * 128):
  lv + (x * 128 - lv + 64) + 64  = x * 128 + 128 := by omega

protected def initialize_J0 (H : BitVec 128) (IV : BitVec lv) :=
  if h₀ : lv == 96
  then have h₁ : lv + 31 + 1 = 128 := by
         simp only [Nat.succ.injEq]
         exact Nat.eq_of_beq_eq_true h₀
       BitVec.cast h₁ (IV ++ BitVec.zero 31 ++ 0b1#1)
  else let s := GCM.ceiling_in_bits lv - lv
       have h₂ : 128 ∣ (lv + (s + 64) + 64) := by
         simp only [s, GCM.ceiling_in_bits]
         rw [GCM.initialize_J0_simplification lv (GCM.ceiling_in_blocks lv)
             (by apply GCM.bits_le_ceiling_in_bits)]
         omega
       let block := IV ++ (BitVec.zero (s + 64)) ++ (BitVec.ofNat 64 lv)
       GHASH H block h₂

protected theorem GCM_AE_DE_simplification1 (a : Nat) (v : Nat) (p : Nat) (u : Nat) :
  a + v + p + u + 64 + 64 = 128 + (u + p) + (v + a) := by omega

protected theorem GCM_AE_DE_simplification2
  (y : Nat) (x : Nat) (h : y ≤ x):
  (x - y) + y = x := by omega

/-- GCM_AE : Galois Counter Mode Authenticated Encryption -/
def GCM_AE (CIPH : Cipher (n := 128) (m := m))
  (K : BitVec m) (t : Nat) (IV : BitVec lv) (P : BitVec p) (A : BitVec a)
  : (BitVec p) × (BitVec t) :=
  let H := CIPH (BitVec.zero 128) K
  let J0 : BitVec 128 := GCM.initialize_J0 H IV
  let ICB := inc_s 32 J0 (by decide)
  let C := GCTR (m := m) CIPH K ICB P
  let u := GCM.ceiling_in_bits p - p
  let v := GCM.ceiling_in_bits a - a
  let block := A ++ BitVec.zero v ++ C ++ BitVec.zero u
               ++ (BitVec.ofNat 64 a) ++ (BitVec.ofNat 64 p)
  have h : 128 ∣ a + v + p + u + 64 + 64 := by
    rw [GCM.GCM_AE_DE_simplification1]
    simp only [u, v]
    rw [GCM.GCM_AE_DE_simplification2 p (GCM.ceiling_in_bits p)
        (by apply GCM.bits_le_ceiling_in_bits)]
    rw [GCM.GCM_AE_DE_simplification2 a (GCM.ceiling_in_bits a)
        (by apply GCM.bits_le_ceiling_in_bits)]
    simp only [GCM.ceiling_in_bits]
    omega
  let S := GHASH H block h
  let T := truncate t $ GCTR (m := m) CIPH K J0 S
  (C, T)

def length_constraints (_IV : BitVec v) (_A : BitVec a) (_C : BitVec c)
  : Bool :=
     1 ≤ v && v ≤ 2^64 - 1
  && c ≤ 2^39 - 256
  && a ≤ 2^64 - 1

/-- GCM_AD : Galois Counter Mode Authenticated Decryption
    GCM_AD returns none when decryption fails. -/
def GCM_AD (CIPH : Cipher (n := 128) (m := m))
  (K : BitVec m) (IV : BitVec lv) (C : BitVec c) (A : BitVec a) (T : BitVec t)
  : Option (BitVec c) :=
  if not $ length_constraints IV C A then
    none
  else
    let H := CIPH (BitVec.zero 128) K
    let J0 := GCM.initialize_J0 H IV
    let ICB := inc_s 32 J0 (by decide)
    let P := GCTR (m := m) CIPH K ICB C
    let u := GCM.ceiling_in_bits c - c
    let v := GCM.ceiling_in_bits a - a
    let block := A ++ BitVec.zero v ++ C ++ BitVec.zero u
                 ++ (BitVec.ofNat 64 a) ++ (BitVec.ofNat 64 c)
    have h : 128 ∣ a + v + c + u + 64 + 64 := by
      rw [GCM.GCM_AE_DE_simplification1]
      simp only [u, v]
      rw [GCM.GCM_AE_DE_simplification2 c (GCM.ceiling_in_bits c)
          (by apply GCM.bits_le_ceiling_in_bits)]
      rw [GCM.GCM_AE_DE_simplification2 a (GCM.ceiling_in_bits a)
          (by apply GCM.bits_le_ceiling_in_bits)]
      simp only [GCM.ceiling_in_bits]
      omega
    let S := GHASH H block h
    let T' := truncate t $ GCTR (m := m) CIPH K J0 S
    if T == T' then some P else none

end GCM
