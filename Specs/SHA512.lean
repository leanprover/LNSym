/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel, Yan Peng
-/
import Std.Data.BitVec
import Std.Data.LazyList
import Specs.SHA512Common

namespace SHA2

-- Reference: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

-- There are three implementations of the message schedule function here:
--
-- 1) `message_schedule`: Closely follows the NIST standard above, but
--    has suboptimal execution performance.
--
-- 2) `message_schedule_mem`: Faster version, achieved via
--    memoization. We should prove that this function is equivalent to
--    `message_schedule` above.
--
-- 3) `message_schedule_lazy`: Another fast version that uses lazy
--    lists to defer computations until they are really needed, but
--    not amenable to reasoning because a Lean partial function is
--    involved here.

open Std.BitVec
open sha512_helpers

structure Hash where
  a : BitVec 64 -- Least-significant word
  b : BitVec 64
  c : BitVec 64
  d : BitVec 64
  e : BitVec 64
  f : BitVec 64
  g : BitVec 64
  h : BitVec 64
deriving DecidableEq, Repr

/-- Converts a `Hash` to a 512-bit bitvector with the most-significant
word first. -/
def Hash.toBitVec (h : Hash) : BitVec 512 :=
  h.h ++ h.g ++ h.f ++ h.e ++ h.d ++ h.c ++ h.b ++ h.a

def add_hash (h1 h2 : Hash) : Hash :=
  { a := h1.a + h2.a,
    b := h1.b + h2.b,
    c := h1.c + h2.c,
    d := h1.d + h2.d,
    e := h1.e + h2.e,
    f := h1.f + h2.f,
    g := h1.g + h2.g,
    h := h1.h + h2.h }

def message_schedule_word_aux (w1 w2 w3 w4 : BitVec 64) :=
  sigma_1 w1 + w2 + sigma_0 w3 + w4

-----------------------------------------------
-- Non-optimized message schedule, closely following the NIST standard

theorem msg_schd_termination_lemma {t x : Nat}
  (h0 : 16 <= t) (h1 : x <= 16) (h2 : 0 < x) : (t - x < t) := by
  have h_0: x <= t := by
    apply Nat.le_trans h1 h0
  apply Nat.sub_lt_self ?h₀ h_0; simp [h2]

def message_schedule_word (t : Nat) (m : List (BitVec 64)) : BitVec 64 :=
  if h0 : t <= 15 then
    (List.get! m t)
  else
    have h1: t -  2 < t := by
      apply msg_schd_termination_lemma <;> simp only [Nat.not_le] at *; exact h0; (repeat decide)
    have h2: t -  7 < t := by
      apply msg_schd_termination_lemma <;> simp only [Nat.not_le] at *; exact h0; (repeat decide)
    have h3: t - 15 < t := by
      apply msg_schd_termination_lemma <;> simp only [Nat.not_le] at *; exact h0; (repeat decide)
    have h4: t - 16 < t := by
      apply msg_schd_termination_lemma <;> simp only [Nat.not_le] at *; exact h0; (repeat decide)
    let w1 := message_schedule_word (t - 2) m
    let w2 := message_schedule_word (t - 7) m
    let w3 := message_schedule_word (t - 15) m
    let w4 := message_schedule_word (t - 16) m
    message_schedule_word_aux w1 w2 w3 w4
  termination_by t

def message_schedule (i max : Nat) (m : List (BitVec 64)) : List (BitVec 64) :=
  if i < max then
    message_schedule_word i m :: message_schedule (i + 1) max m
  else
    []
  termination_by max - i

-----------------------------------------------
-- Optimized message schedule, via memoization

-- This version of message_schedule_word employs memoization for speed
def message_schedule_mem_word (t : Nat) (m : List (BitVec 64)) (acc : List (BitVec 64)): BitVec 64 :=
  if t <= 15 then
    (List.get! m t)
  else
    let w1 := List.get! acc (t - 2)
    let w2 := List.get! acc (t - 7)
    let w3 := List.get! acc (t - 15)
    let w4 := List.get! acc (t - 16)
    message_schedule_word_aux w1 w2 w3 w4

-- This version of message_schedule employs memoization for speed
def message_schedule_mem (i max : Nat) (acc : List (BitVec 64)) (m : List (BitVec 64)) : List (BitVec 64) :=
  if i < max then
    let updated_acc := acc ++ [(message_schedule_mem_word i m acc)]
    message_schedule_mem (i + 1) max updated_acc m
  else
    acc
  termination_by max - i

-----------------------------------------------
-- Optimized message schedule, via lazylists and thunks

-- Use Lazylists to speed up message_schedule
partial def message_schedule_inf (m : List (BitVec 64)) : (LazyList (BitVec 64)) :=
  match m with
  | [] => LazyList.nil
  | hd :: tl =>
    let w1 := List.get! m 14
    let w2 := List.get! m 9
    let w3 := List.get! m 1
    let w4 := List.get! m 0
    let next := message_schedule_word_aux w1 w2 w3 w4
    LazyList.cons hd $ message_schedule_inf $ tl ++ [next]

def message_schedule_lazy (max : Nat) (m : List (BitVec 64)) : List (BitVec 64) :=
  LazyList.take max $ message_schedule_inf m

-----------------------------------------------

def compression_update_t1 (e f g h kt wt : BitVec 64) : BitVec 64 :=
  h + (sigma_big_1 e) + (ch e f g) + kt + wt

def compression_update_t2 (a b c : BitVec 64) : BitVec 64 :=
  (sigma_big_0 a) + (maj a b c)

def compression_update (wv : Hash) (kt wt : BitVec 64) : Hash :=
  let t1 := compression_update_t1 wv.e wv.f wv.g wv.h kt wt
  let t2 := compression_update_t2 wv.a wv.b wv.c
  let (h, g, f, e, d, c, b, a) := (wv.g, wv.f, wv.e, wv.d + t1, wv.c, wv.b, wv.a, t1 + t2)
  { a, b, c, d, e, f, g, h }

def compression (i max : Nat) (wv : Hash) (k w : List (BitVec 64)) : Hash :=
  if i < max then
    let ki := List.get! k i
    let wi := List.get! w i
    let wv' := compression_update wv ki wi
    compression (i + 1) max wv' k w
  else
    wv
  termination_by max - i

def processBlocks (message_schedule : List (BitVec 64) → List (BitVec 64))
                  (j : Nat) (hash : Hash) (k : List (BitVec 64)) (ms : List (List (BitVec 64))) : Hash :=
  match ms with
  | [] => hash
  | m :: rest =>
    let w := message_schedule m
    let work_vars := compression 0 j hash k w
    let hash' := add_hash hash work_vars
    processBlocks message_schedule j hash' k rest

def j_512 : Nat := 80

def h0_512 : Hash :=
  { a := 0x6a09e667f3bcc908#64,
    b := 0xbb67ae8584caa73b#64,
    c := 0x3c6ef372fe94f82b#64,
    d := 0xa54ff53a5f1d36f1#64,
    e := 0x510e527fade682d1#64,
    f := 0x9b05688c2b3e6c1f#64,
    g := 0x1f83d9abfb41bd6b#64,
    h := 0x5be0cd19137e2179#64 }

/-- SHA-384, SHA-512, SHA-512/224 and SHA-512/256 Constants with the
most-significant word first. -/
def k_512 : List (BitVec 64) :=
  [0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
   0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
   0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
   0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
   0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
   0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
   0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
   0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
   0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
   0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
   0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
   0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
   0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
   0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
   0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
   0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
   0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
   0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
   0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
   0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64]

def sha512 (message_schedule : List (BitVec 64) → List (BitVec 64)) (ms : List (List (BitVec 64))) : Hash :=
  processBlocks message_schedule j_512 h0_512 k_512 ms

end SHA2

----------------------------------------------------------------------
