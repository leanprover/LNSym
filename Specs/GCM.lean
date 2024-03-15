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

def R : (BitVec 128) := 0b11100001#8 ++ 0b0#120

/-- A Cipher type is a function that takes an input of size n and
    a key of size m and returns an encrypted block of size n -/
abbrev Cipher {n : Nat} {m : Nat} :=  BitVec n → BitVec m → BitVec n

/-- The s-bit incrementing function -/
def inc_s (s : Nat) (X : BitVec l) (H₀ : 0 < s) (H₁ : s < l) : BitVec l :=
  let msb_hi := l - 1
  let msb_lo := s
  let lsb_hi := s - 1
  let lsb_lo := 0
  have h₁ : lsb_hi - lsb_lo + 1 = s := by omega
  let upper := extractLsb msb_hi msb_lo X
  let lower := h₁ ▸ (extractLsb lsb_hi lsb_lo X) + 0b1#s
  have h₂ : msb_hi - msb_lo + 1 + s = l := by omega
  h₂ ▸ (upper ++ lower)

def mul_aux (i : Nat) (X : BitVec 128) (Z : BitVec 128) (V : BitVec 128)
  : BitVec 128 :=
  if h : 128 ≤ i then
    Z
  else
    let Xi := getMsb X i
    let Z := if not Xi then Z else Z ^^^ V
    let lsb_v := getLsb V 0
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
    let lo := i * 128
    let hi := lo + 127
    have h₀ : hi - lo + 1 = 128 := by omega
    let Xi := extractLsb hi lo X
    let res := rev_elems 128 8 (Y ^^^ (h₀ ▸ Xi)) (by decide) (by decide)
    let H_rev := rev_elems 128 8 H (by decide) (by decide)
    let Y := mul res H_rev
    let Y := rev_elems 128 8 Y (by decide) (by decide)
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
    let lo := i * 128
    let hi := lo + 127
    have h : hi - lo + 1 = 128 := by omega
    -- extractLsb will fill upper bits with zeros if hi >= len X
    let Xi := extractLsb hi lo X
    -- reversing counter because AES expects little-endian
    let ICB_rev := rev_elems 128 8 ICB (by decide) (by decide)
    let Yi := h ▸ Xi ^^^ CIPH ICB_rev K
    -- partInstall ignores val indexes that exceeds length of Y
    let Y := BitVec.partInstall hi lo (h.symm ▸ Yi) Y
    let ICB := inc_s 32 ICB (by omega) (by omega)
    GCTR_aux CIPH (i + 1) n K ICB X Y
  termination_by (n - i)

protected def ceiling_in_blocks (w : Nat) := (w - 1) / 128 + 1
protected def ceiling_in_bits (w : Nat) := (GCM.ceiling_in_blocks w) * 128

protected theorem bits_le_ceiling_in_bits (w : Nat) :
  w ≤ (GCM.ceiling_in_blocks w) * 128 := by
  simp only [GCM.ceiling_in_blocks]
  omega

/-- GCTR: encrypting/decrypting message x using Galois counter mode -/
def GCTR {m : Nat} (CIPH : Cipher (n := 128) (m := m))
  (K : BitVec m) (ICB : BitVec 128) (X : BitVec v) : (BitVec v) :=
  let n := GCM.ceiling_in_blocks v
  GCTR_aux CIPH 0 n K ICB X $ BitVec.zero v

protected theorem initialize_J0_simplification
  (lv : Nat) (x : Nat) (h : lv ≤ x * 128):
  lv + (x * 128 - lv + 64) + 64  = x * 128 + 128 := by omega

protected def initialize_J0 (H : BitVec 128) (IV : BitVec lv) :=
  if h₀ : lv == 96
  then have h₁ : lv + 31 + 1 = 128 := by
         simp only [Nat.succ.injEq]
         exact Nat.eq_of_beq_eq_true h₀
       h₁ ▸ (IV ++ BitVec.zero 31 ++ 0b1#1)
  else let s := GCM.ceiling_in_bits lv - lv
       have h₂ : 128 ∣ (lv + (s + 64) + 64) := by
         simp only [s, GCM.ceiling_in_bits]
         rw [GCM.initialize_J0_simplification lv (GCM.ceiling_in_blocks lv)
             (by apply GCM.bits_le_ceiling_in_bits)]
         omega
       have h₃ : 8 ∣ (lv + (s + 64) + 64) := by
         simp only [s, GCM.ceiling_in_bits]
         rw [GCM.initialize_J0_simplification lv (GCM.ceiling_in_blocks lv)
             (by apply GCM.bits_le_ceiling_in_bits)]
         omega
       let block := rev_elems (lv + (s + 64 ) + 64) 8
                      (IV ++ (BitVec.zero (s + 64)) ++ (BitVec.ofNat 64 lv))
                      h₃ (by decide)
       rev_elems 128 8 (GHASH H block h₂) (by decide) (by decide)

protected theorem GCM_AE_DE_simplification1 (a : Nat) (v : Nat) (p : Nat) (u : Nat) :
  64 + 64 + u + p + v + a = 128 + (u + p) + (v + a) := by omega

protected theorem GCM_AE_DE_simplification2
  (y : Nat) (x : Nat) (h : y ≤ x * 128):
  (x * 128 - y) + y = x * 128 := by omega

/-- GCM_AE : Galois Counter Mode Authenticated Encryption -/
def GCM_AE {m : Nat} (CIPH : Cipher (n := 128) (m := m))
  (K : BitVec m) (IV : BitVec lv) (P : BitVec p) (A : BitVec a) (t : Nat)
  : (BitVec p) × (BitVec t) :=
  let H := CIPH (BitVec.zero 128) K
  let J0 : BitVec 128 := GCM.initialize_J0 H IV
  let ICB := inc_s 32 J0 (by decide) (by decide)
  let C := GCTR (m := m) CIPH K ICB P
  let u := GCM.ceiling_in_bits p - p
  let v := GCM.ceiling_in_bits a - a
  let block := rev_elems 64 8 (BitVec.ofNat 64 p) (by decide) (by decide)
               ++ rev_elems 64 8 (BitVec.ofNat 64 a) (by decide) (by decide)
               ++ BitVec.zero u ++ C ++ BitVec.zero v ++ A
  have h : 128 ∣ 64 + 64 + u + p + v + a := by
    rw [GCM.GCM_AE_DE_simplification1]
    simp only [u, v]
    simp only [GCM.ceiling_in_bits]
    rw [GCM.GCM_AE_DE_simplification2 p (GCM.ceiling_in_blocks p)
        (by apply GCM.bits_le_ceiling_in_bits)]
    rw [GCM.GCM_AE_DE_simplification2 a (GCM.ceiling_in_blocks a)
        (by apply GCM.bits_le_ceiling_in_bits)]
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
def GCM_AD {m : Nat} (CIPH : Cipher (n := 128) (m := m))
  (K : BitVec m) (IV : BitVec lv) (C : BitVec c) (A : BitVec a) (T : BitVec t)
  : Option (BitVec c) :=
  if not $ length_constraints IV C A then
    none
  else
    let H := CIPH (BitVec.zero 128) K
    let J0 := GCM.initialize_J0 H IV
    let ICB := inc_s 32 J0 (by decide) (by decide)
    let P := GCTR (m := m) CIPH K ICB C
    let u := GCM.ceiling_in_bits c - c
    let v := GCM.ceiling_in_bits a - a
    let block := rev_elems 64 8 (BitVec.ofNat 64 c) (by decide) (by decide)
                 ++ rev_elems 64 8 (BitVec.ofNat 64 a) (by decide) (by decide)
                 ++ BitVec.zero u ++ C ++ BitVec.zero v ++ A
    have h : 128 ∣ 64 + 64 + u + c + v + a := by
      rw [GCM.GCM_AE_DE_simplification1]
      simp only [u, v]
      simp only [GCM.ceiling_in_bits]
      rw [GCM.GCM_AE_DE_simplification2 c (GCM.ceiling_in_blocks c)
          (by apply GCM.bits_le_ceiling_in_bits)]
      rw [GCM.GCM_AE_DE_simplification2 a (GCM.ceiling_in_blocks a)
          (by apply GCM.bits_le_ceiling_in_bits)]
      omega
    let S := GHASH H block h
    let T' := truncate t $ GCTR (m := m) CIPH K J0 S
    if T == T' then some P else none

end GCM
