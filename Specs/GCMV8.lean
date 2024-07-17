/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Specs.GCM

-- References:
-- https://github.com/GaloisInc/cryptol/blob/master/lib/Cryptol/Reference.cry
-- https://tiny.amazon.com/12296d03c/githGalocrypblob1e31PrimSymm
-- https://tiny.amazon.com/3edw4edm/githawslawslblob02aaSAWspec
-- https://github.com/awslabs/aws-lc-verification/blob/master/SAW/proof/AES/GHASH.saw
-- https://link.springer.com/chapter/10.1007/978-3-031-34671-2_30
-- https://www.rfc-editor.org/rfc/rfc8452.txt

namespace GCMV8

open BitVec

------------------------------------------------------------------------------

def hi (x : BitVec 128) : BitVec 64 :=
  extractLsb 127 64 x

def lo (x : BitVec 128) : BitVec 64 :=
  extractLsb 63 0 x

------------------------------------------------------------------------------
-- Functions related to galois field operations

/-- Performs multiplication of polynomials over GF(2).
  This algorithm is a shift and add multiplication.
  For each bit of y from highest to lowest, if the bit is set,
  it performs a GF add (xor) of x onto the shifted accumulator.
-/
def pmult (x: BitVec (m + 1)) (y : BitVec (n + 1)) : BitVec (m + n + 1) :=
  let rec pmultTR (x: BitVec (m + 1)) (y : BitVec (n + 1)) (i : Nat)
    (acc : BitVec (m + n + 1)) : BitVec (m + n + 1) :=
    if i < n + 1 then
      let acc := acc <<< 1
      have h : n + (m + 1) = m + n + 1 := by omega
      let tmp := if getMsb y i then (BitVec.zero n) ++ x else h ▸ BitVec.zero (m + n + 1)
      let acc := h ▸ acc ^^^ tmp
      pmultTR x y (i + 1) (h ▸ acc)
    else acc
  pmultTR x y 0 (BitVec.zero (m + n + 1))

example: pmult 0b1101#4 0b10#2 = 0b11010#5 := by rfl

/-- Degree of x. -/
protected def degree (x : BitVec n) : Nat :=
  let rec degreeTR (x : BitVec n) (n : Nat) : Nat :=
    if n = 0 then 0
    else if getLsb x n then n else degreeTR x (n - 1)
  degreeTR x (n - 1)
example: GCMV8.degree 0b0101#4 = 2 := by rfl

/-- Subtract x from y if y's x-degree-th bit is 1. -/
protected def reduce (x : BitVec n) (y : BitVec n) : BitVec n :=
  if getLsb y (GCMV8.degree x) then y ^^^ x else y

/-- Performs division of polynomials over GF(2). -/
def pdiv (x: BitVec n) (y : BitVec m) (h : 0 < m): BitVec n :=
  let rec pdivTR (x : BitVec n) (y : BitVec m) (i : Nat) (z : BitVec m)
    (acc : BitVec n) : BitVec n :=
    if i < n then
      have h2 : (n - i - 1) - (n - i - 1) + 1 = 1 := by omega
      let xi : BitVec 1 := h2 ▸ extractLsb (n - i - 1) (n - i - 1) x
      have h3 : m = m - 1 - 0 + 1 := by omega
      let zi : BitVec m := h3 ▸ extractLsb (m - 1) 0 ((GCMV8.reduce y z) ++ xi)
      have h1 : 1 = GCMV8.degree y - GCMV8.degree y + 1 := by omega
      let bit : BitVec 1 := h1 ▸ extractLsb (GCMV8.degree y) (GCMV8.degree y) zi
      have h4 : 1 = (n - i - 1) - (n - i - 1) + 1 := by omega
      let newacc : BitVec n := partInstall (n - i - 1) (n - i - 1) (h4 ▸ bit) acc
      pdivTR x y (i + 1) zi newacc
    else acc
  pdivTR x y 0 (BitVec.zero m) (BitVec.zero n)

example : pdiv 0b1101#4 0b10#2 (by omega) = 0b110#4 := by rfl
example : pdiv 0x1a#5 0b10#2 (by omega) = 0b1101#5 := by rfl
example : pdiv 0b1#1 0b10#2 (by omega) = 0b0#1 := by rfl

/-- Performs modulus of polynomials over GF(2). -/
def pmod (x : BitVec n) (y : BitVec (m + 1)) (H : m > 0) : BitVec m :=
  let rec pmodTR (x : BitVec n) (y : BitVec (m + 1)) (p : BitVec (m + 1))
    (i : Nat) (r : BitVec m) (H : m > 0) : BitVec m :=
    if i < n then
      let xi := getLsb x i
      have h : m - 1 + 1 = m := by omega
      let tmp := if xi then extractLsb (m - 1) 0 p else h ▸ BitVec.zero m
      let r := h ▸ r ^^^ tmp
      pmodTR x y (GCMV8.reduce y (p <<< 1)) (i + 1) (h ▸ r) H
    else r
  if y = 0 then 0 else pmodTR x y (GCMV8.reduce y 1) 0 (BitVec.zero m) H

example: pmod 0b011#3 0b00#2 (by omega) = 0b0#1 := by rfl
example: pmod 0b011#3 0b01#2 (by omega) = 0b0#1 := by rfl
example: pmod 0b011#3 0b10#2 (by omega) = 0b1#1 := by rfl
example: pmod 0b011#3 0b11#2 (by omega) = 0b0#1 := by rfl
example: pmod 0b011#3 0b100#3 (by omega) = 0b11#2 := by rfl
example: pmod 0b011#3 0b1001#4 (by omega) = 0b11#3 := by rfl

------------------------------------------------------------------------------
-- Functions related to GCM
-- In the following section, we use the "GHASH field" to note the GF field with
-- the irreducible polynomial P(x) = <| 1 + x + x^^2 + x^^7 + x^^128 |>.
-- We use the term "POLYVAL field" to note the GF field with the bit-reflected
-- irreducible polynomial Q(x) = <| 1 + x^^121 + x^^126 + x^^127 + x^^128 |>.

/-- Binary representation for
    irreducible polynomial P(x) = <| 1 + x + x^^2 + x^^7 + x^^128 |>
-/
def irrepoly : BitVec 129 := 0x100000000000000000000000000000087#129

/-- Binary representation for
    irreducible polynomial Q(x) = <| 1 + x^^121 + x^^126 + x^^127 + x^^128 |>
    https://link.springer.com/chapter/10.1007/978-3-031-34671-2_30
-/
def refpoly : BitVec 129 := 0x1C2000000000000000000000000000001#129

/-- H_hat : twisted H
  H_hat = x × H (mod Q(x))
  See Remark 5 in paper
    "A New Interpretation for the GHASH Authenticator of AES-GCM"
-/
protected def gcm_init_H (H : BitVec 128) : BitVec 128 :=
  pmod (H ++ 0b0#1) refpoly (by omega)

protected def gcm_polyval_mul (x : BitVec 128) (y : BitVec 128) : BitVec 256 :=
  0b0#1 ++ pmult x y

protected def gcm_polyval_red (x : BitVec 256) : BitVec 128 :=
  reverse $ pmod (reverse x) irrepoly (by omega)

/--
  The following implementation of POLYVAL first does pmult of x and y,
  then reverses the input to project it into the GHASH field,
  then does reduction in GHASH field and finally reverses the result back.
  We could do this because of the following two facts:
  1. Proposition 1 from paper
    "A New Interpretation for the GHASH Authenticator of AES-GCM"
  2. Lemma: reverse (pmult x y) = pmult (reverse x) (reverse y)
-/
protected def gcm_polyval (x : BitVec 128) (y : BitVec 128) : BitVec 128 :=
  GCMV8.gcm_polyval_red $ GCMV8.gcm_polyval_mul x y

/-- GCMInitV8 specification:
    H : [128] -- initial H input
    output : [12][128] -- precomputed Htable values
-/
def GCMInitV8 (H : BitVec 128) : (List (BitVec 128)) :=
  let H0 := GCMV8.gcm_init_H H
  let H2 := GCMV8.gcm_polyval H0 H0
  let H1 := ((hi H2) ^^^ (lo H2)) ++ ((hi H0) ^^^ (lo H0))
  let H3 := GCMV8.gcm_polyval H0 H2
  let H5 := GCMV8.gcm_polyval H0 H3
  let H4 := ((hi H5) ^^^ (lo H5)) ++ ((hi H3) ^^^ (lo H3))
  let H6 := GCMV8.gcm_polyval H0 H5
  let H8 := GCMV8.gcm_polyval H0 H6
  let H7 := ((hi H8) ^^^ (lo H8)) ++ ((hi H6) ^^^ (lo H6))
  let H9 := GCMV8.gcm_polyval H0 H8
  let H11 := GCMV8.gcm_polyval H0 H9
  let H10 := ((hi H11) ^^^ (lo H11)) ++ ((hi H9) ^^^ (lo H9))
  [H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11]

-- TODO: This test could not be proved using rfl
example :  GCMInitV8 0x66e94bd4ef8a2c3b884cfa59ca342b2e#128 =
  [ 0xcdd297a9df1458771099f4b39468565c#128,
    0x62d81a7fe5da3296dd4b631a4b7c0e2b#128,
    0x88d320376963120dea0b3a488cb9209b#128,
    0x8695e702c322faf935c1a04f8bfb2395#128,
    0xb2261b4d0cb1e020b354474d48d9d96c#128,
    0x568bd97348bd9145e4adc23e440c7165#128,
    0xf9151b1f632d10b47d845b630bb0a55d#128,
    0xa674eba8f9d7f2508491407c689db5e9#128,
    0xec87cfb0e19d1c4e4af32418184aee1e#128,
    0x7d1998bcfc545474f109e6e0b31d1eee#128,
    0x7498729da40cd2808c107e5c4f494a9a#128,
    0xd0e417a05fe61ba4a47c653dfbeac924#128 ] := by native_decide

/-- GCMGmultV8 specification:
    H  : [128] -- the first element in Htable, not the initial H input to GCMInitV8
    Xi : [16][8] -- current hash value
    output : [16][8] -- next hash value
-/
def GCMGmultV8 (H : BitVec 128) (Xi : List (BitVec 8)) (h : 8 * Xi.length = 128)
  : (List (BitVec 8)):=
  split (GCMV8.gcm_polyval H (h ▸ BitVec.flatten Xi)) 8 (by omega)

example : GCMGmultV8 0xcdd297a9df1458771099f4b39468565c#128
  [ 0x10#8, 0x54#8, 0x43#8, 0xb0#8, 0x2c#8, 0x4b#8, 0x1f#8, 0x24#8,
    0x3b#8, 0xcd#8, 0xd4#8, 0x87#8, 0x16#8, 0x65#8, 0xb3#8, 0x2b#8 ] (by decide) =
  [ 0xa2#8, 0xc9#8, 0x9c#8, 0x56#8, 0xeb#8, 0xa7#8, 0x91#8, 0xf6#8,
    0x9e#8, 0x15#8, 0xa6#8, 0x00#8, 0x67#8, 0x29#8, 0x7e#8, 0x0f#8 ] := by rfl


protected def gcm_ghash_block (H : BitVec 128) (Xi : BitVec 128)
  (inp : BitVec 128) : BitVec 128 :=
  GCMV8.gcm_polyval H (Xi ^^^ inp)

/-- GCMGhashV8 specification:
    H : [128] -- the first element in Htable, not the initial H input to GCMInitV8
    Xi : [16][8] -- initial hash
    inp : [m][8] -- input message
    output : [16][8] -- final hash
-/
def GCMGhashV8 (H : BitVec 128) (Xi : List (BitVec 8))
  (inp : List (BitVec 8)) (h1 : Xi.length = 16) (h2 : 16 ∣ inp.length)
  : List (BitVec 8) :=
  let rec GCMGhashV8TR {m : Nat} (H : BitVec 128) (Xi : BitVec 128)
    (inp : BitVec m) (i : Nat) (h1 : 128 ∣ m) : BitVec 128 :=
    if i < m / 128 then
      let lo := m - (i + 1) * 128
      let hi := lo + 127
      have h2 : hi - lo + 1 = 128 := by omega
      let inpi : BitVec 128 := h2 ▸ extractLsb hi lo inp
      let Xj := GCMV8.gcm_ghash_block H Xi inpi
      GCMGhashV8TR H Xj inp (i + 1) h1
    else Xi
  have h3 : 128 ∣ 8 * inp.length := by omega
  have h4 : 8 * Xi.length = 128 := by omega
  split (GCMGhashV8TR H (h4 ▸ BitVec.flatten Xi) (BitVec.flatten inp) 0 h3) 8 (by omega)

example : GCMGhashV8 0xcdd297a9df1458771099f4b39468565c#128
  [ 0xa2#8, 0xc9#8, 0x9c#8, 0x56#8, 0xeb#8, 0xa7#8, 0x91#8, 0xf6#8,
    0x9e#8, 0x15#8, 0xa6#8, 0x00#8, 0x67#8, 0x29#8, 0x7e#8, 0x0f#8 ]
  (List.replicate 16 0x2a#8) (by simp) (by simp only [List.length_replicate]; omega) =
  [ 0x20#8, 0x60#8, 0x2e#8, 0x75#8, 0x7a#8, 0x4e#8, 0xec#8, 0x90#8,
    0xc0#8, 0x9d#8, 0x49#8, 0xfd#8, 0xdc#8, 0xf2#8, 0xc9#8, 0x35#8 ] := by rfl

end GCMV8
