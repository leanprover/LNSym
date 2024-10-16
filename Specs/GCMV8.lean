/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Specs.GCM

-- References:
-- https://github.com/GaloisInc/cryptol/blob/master/lib/Cryptol/Reference.cry
-- https://github.com/GaloisInc/cryptol-specs/blob/1e31efb619f4c328845e254577dedeca66669068/Primitive/Symmetric/Cipher/Authenticated/AES_256_GCM.cry#L20
-- https://github.com/awslabs/aws-lc-verification/blob/02aa15c93ed9d2ddc1f7c4742ff05b3e7f05c592/SAW/spec/AES/AES-GCM.cry#L75
-- https://github.com/awslabs/aws-lc-verification/blob/master/SAW/proof/AES/GHASH.saw
-- https://link.springer.com/chapter/10.1007/978-3-031-34671-2_30
-- https://www.rfc-editor.org/rfc/rfc8452.txt

namespace GCMV8

open BitVec

------------------------------------------------------------------------------

def hi (x : BitVec 128) : BitVec 64 :=
  extractLsb' 64 64 x

def lo (x : BitVec 128) : BitVec 64 :=
  extractLsb' 0 64 x

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
    match i with
    | 0 => acc
    | j + 1 =>
      let acc := acc <<< 1
      let tmp := if getMsbD y (n + 1 - i)
                 then partInstall 0 (m + 1) x 0#(m + n + 1)
                 else 0#(m + n + 1)
      let acc := acc ^^^ tmp
      pmultTR x y j acc
  pmultTR x y (n + 1) 0#(m + n + 1)

example: pmult 0b1101#4 0b10#2 = 0b11010#5 := rfl

/-- Degree of x. Defined using non-ite statements. -/
def degree (x : BitVec n) : Nat :=
  let rec degreeTR (x : BitVec n) (n : Nat) (i : Nat) (acc : Nat) : Nat :=
    match n with
    | 0 => acc
    | m + 1 =>
    let is_one := extractLsb' 0 1 (x &&& 1)
    degreeTR (x >>> 1) m (i + 1) (acc + is_one.toNat * (i - acc))
  degreeTR x n 0 0

example: GCMV8.degree 0b0101#4 = 2 := rfl
example: GCMV8.degree 0b1101#4 = 3 := rfl

/-- Subtract x from y if y's x-degree-th bit is 1.
    Defined using non-ite statements. -/
def reduce (x : BitVec n) (y : BitVec n) : BitVec n :=
  let is_one := (y >>> (GCMV8.degree x)) &&& 1
  y ^^^ (is_one * x)

/-- Performs division of polynomials over GF(2). -/
def pdiv (x: BitVec n) (y : BitVec m): BitVec n :=
  let rec pdivTR (x : BitVec n) (y : BitVec m) (i : Nat) (z : BitVec m)
    (acc : BitVec n) : BitVec n :=
    match i with
    | 0 => acc
    | j + 1 =>
      let xi := extractLsb' (i - 1) 1 x
      let zi := extractLsb' 0 m ((GCMV8.reduce y z) ++ xi)
      let bit := extractLsb' (GCMV8.degree y) 1 zi
      let newacc : BitVec n :=
        partInstall (i - 1) 1 bit acc
      pdivTR x y j zi newacc
  pdivTR x y n (BitVec.zero m) (BitVec.zero n)

example : pdiv 0b1101#4 0b10#2 = 0b110#4 := rfl
example : pdiv 0x1a#5 0b10#2 = 0b1101#5 := rfl
example : pdiv 0b1#1 0b10#2 = 0b0#1 := rfl

/-- Performs modulus of polynomials over GF(2).
    Defined using non-ite statements.-/
def pmod (x : BitVec n) (y : BitVec (m + 1)) (H : 0 < m) : BitVec m :=
  let rec pmodTR (x : BitVec n) (y : BitVec (m + 1)) (p : BitVec (m + 1))
    (i : Nat) (r : BitVec m) (H : 0 < m) : BitVec m :=
    match i with
    | 0 => r
    | j + 1 =>
      let is_one := extractLsb' 0 m ((x >>> (n - i)) &&& 1)
      let tmp := is_one * extractLsb' 0 m p
      let r := r ^^^ tmp
      pmodTR x y (GCMV8.reduce y (p <<< 1)) j r H
  if y = 0 then 0 else pmodTR x y (GCMV8.reduce y 1) n (BitVec.zero m) H

example: pmod 0b011#3 0b00#2 (by omega) = 0b0#1 := rfl
example: pmod 0b011#3 0b01#2 (by omega) = 0b0#1 := rfl
example: pmod 0b011#3 0b10#2 (by omega) = 0b1#1 := rfl
example: pmod 0b011#3 0b11#2 (by omega) = 0b0#1 := rfl
example: pmod 0b011#3 0b100#3 (by omega) = 0b11#2 := rfl
example: pmod 0b011#3 0b1001#4 (by omega) = 0b11#3 := rfl

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
def gcm_init_H (H : BitVec 128) : BitVec 128 :=
  pmod (H ++ 0b0#1) refpoly (by omega)

def gcm_polyval_mul (x : BitVec 128) (y : BitVec 128) : BitVec 256 :=
  0b0#1 ++ pmult x y

def gcm_polyval_red (x : BitVec 256) : BitVec 128 :=
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
def gcm_polyval (x : BitVec 128) (y : BitVec 128) : BitVec 128 :=
  GCMV8.gcm_polyval_red $ GCMV8.gcm_polyval_mul x y

/-- GCMInitV8 specification:
    H : [128] -- initial H input
    output : [12][128] -- precomputed Htable values
    See for Hx_rev values: https://github.com/aws/aws-lc/pull/1403
-/
def GCMInitV8 (H : BitVec 128) : (List (BitVec 128)) :=
  let H0 := GCMV8.gcm_init_H H
  let H0_rev := (lo H0) ++ (hi H0)
  let H2 := GCMV8.gcm_polyval H0 H0
  let H2_rev := (lo H2) ++ (hi H2)
  let H1 := ((hi H2) ^^^ (lo H2)) ++ ((hi H0) ^^^ (lo H0))
  let H3 := GCMV8.gcm_polyval H0 H2
  let H3_rev := (lo H3) ++ (hi H3)
  let H5 := GCMV8.gcm_polyval H0 H3
  let H5_rev := (lo H5) ++ (hi H5)
  let H4 := ((hi H5) ^^^ (lo H5)) ++ ((hi H3) ^^^ (lo H3))
  let H6 := GCMV8.gcm_polyval H0 H5
  let H6_rev := (lo H6) ++ (hi H6)
  let H8 := GCMV8.gcm_polyval H0 H6
  let H8_rev := (lo H8) ++ (hi H8)
  let H7 := ((hi H8) ^^^ (lo H8)) ++ ((hi H6) ^^^ (lo H6))
  let H9 := GCMV8.gcm_polyval H0 H8
  let H9_rev := (lo H9) ++ (hi H9)
  let H11 := GCMV8.gcm_polyval H0 H9
  let H11_rev := (lo H11) ++ (hi H11)
  let H10 := ((hi H11) ^^^ (lo H11)) ++ ((hi H9) ^^^ (lo H9))
  [H0_rev, H1, H2_rev, H3_rev, H4, H5_rev, H6_rev,
   H7, H8_rev, H9_rev, H10, H11_rev]

set_option maxRecDepth 8000 in
example :  GCMInitV8 0x66e94bd4ef8a2c3b884cfa59ca342b2e#128 ==
  [ 0x1099f4b39468565ccdd297a9df145877#128,
    0x62d81a7fe5da3296dd4b631a4b7c0e2b#128,
    0xea0b3a488cb9209b88d320376963120d#128,
    0x35c1a04f8bfb23958695e702c322faf9#128,
    0xb2261b4d0cb1e020b354474d48d9d96c#128,
    0xe4adc23e440c7165568bd97348bd9145#128,
    0x7d845b630bb0a55df9151b1f632d10b4#128,
    0xa674eba8f9d7f2508491407c689db5e9#128,
    0x4af32418184aee1eec87cfb0e19d1c4e#128,
    0xf109e6e0b31d1eee7d1998bcfc545474#128,
    0x7498729da40cd2808c107e5c4f494a9a#128,
    0xa47c653dfbeac924d0e417a05fe61ba4#128 ] := rfl

/-- GCMGmultV8 specification:
    H  : [128] -- the first element in Htable, not the initial H input to GCMInitV8
    Xi : [16][8] -- current hash value
    output : [16][8] -- next hash value
-/
def GCMGmultV8 (H : BitVec 128) (Xi : List (BitVec 8)) (h : 8 * Xi.length = 128)
  : (List (BitVec 8)):=
  let H := (lo H) ++ (hi H)
  split (GCMV8.gcm_polyval H (BitVec.cast h (BitVec.flatten Xi))) 8 (by omega)

/-- Alternative GCMGmultV8 specification that does not use lists:
    H  : BitVec 128 -- the first element in Htable, not the initial H input to GCMInitV8
    Xi : BitVec 128 -- current hash value
    output : BitVec 128 -- next hash value
-/
def GCMGmultV8_alt (H : BitVec 128) (Xi : BitVec 128) : BitVec 128 :=
  let H := (lo H) ++ (hi H)
  gcm_polyval H Xi

set_option maxRecDepth 8000 in
example : GCMGmultV8 0x1099f4b39468565ccdd297a9df145877#128
  [ 0x10#8, 0x54#8, 0x43#8, 0xb0#8, 0x2c#8, 0x4b#8, 0x1f#8, 0x24#8,
    0x3b#8, 0xcd#8, 0xd4#8, 0x87#8, 0x16#8, 0x65#8, 0xb3#8, 0x2b#8 ] (by decide) =
  [ 0xa2#8, 0xc9#8, 0x9c#8, 0x56#8, 0xeb#8, 0xa7#8, 0x91#8, 0xf6#8,
    0x9e#8, 0x15#8, 0xa6#8, 0x00#8, 0x67#8, 0x29#8, 0x7e#8, 0x0f#8 ] := rfl


def gcm_ghash_block (H : BitVec 128) (Xi : BitVec 128)
  (inp : BitVec 128) : BitVec 128 :=
  let H := (lo H) ++ (hi H)
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
    match i with
    | 0 => Xi
    | j + 1 =>
      let lo := (i - 1) * 128
      let inpi := extractLsb' lo 128 inp
      let Xj := GCMV8.gcm_ghash_block H Xi inpi
      GCMGhashV8TR H Xj inp j h1
  have h3 : 128 ∣ 8 * inp.length := by omega
  have h4 : 8 * Xi.length = 128 := by omega
  let flat_Xi := BitVec.cast h4 $ BitVec.flatten Xi
  let flat_inp := BitVec.flatten inp
  split (GCMGhashV8TR H flat_Xi flat_inp (8 * inp.length / 128) h3) 8 (by omega)

set_option maxRecDepth 8000 in
example : GCMGhashV8 0x1099f4b39468565ccdd297a9df145877#128
  [ 0xa2#8, 0xc9#8, 0x9c#8, 0x56#8, 0xeb#8, 0xa7#8, 0x91#8, 0xf6#8,
    0x9e#8, 0x15#8, 0xa6#8, 0x00#8, 0x67#8, 0x29#8, 0x7e#8, 0x0f#8 ]
  (List.replicate 16 0x2a#8) (by simp) (by simp only [List.length_replicate]; omega) =
  [ 0x20#8, 0x60#8, 0x2e#8, 0x75#8, 0x7a#8, 0x4e#8, 0xec#8, 0x90#8,
    0xc0#8, 0x9d#8, 0x49#8, 0xfd#8, 0xdc#8, 0xf2#8, 0xc9#8, 0x35#8 ] := rfl

end GCMV8
