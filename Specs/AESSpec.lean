/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Hanno Becker
-/

import Arm.BitVec
import Arm.Vec

import Lean
open Lean Meta

open BitVec

/-
  The goal of this file is to provide a model of the AES specification
  that is as close as possible to the original FIPS document.

  TODO: This is work in progress. For the moment, we only have definitions
    of the AES state as a bitvector, byte vector, or byte array, as well as
    conversions between them.
-/

/-
   3.3 Indexing of Byte Sequences
-/

abbrev Byte : Type := BitVec 8

def bitvec_split_byte {k : Nat} (invec : BitVec (8*k)) : Byte × (BitVec (8*(k-1))) :=
  let byte : BitVec 8 := invec.truncate 8
  let remainder := BitVec.extractLsb' 8 (8*(k-1)) invec
  (byte, remainder)

theorem bitvec_split_byte_append {k : Nat} (v : BitVec (8*(k-1))) (b : Byte) (h : 8 * (k-1) + 8 = 8 * k) :
    bitvec_split_byte (BitVec.cast h (v ++ b)) = (b, v) := by simp [bitvec_split_byte]

theorem bitvec_split_byte_append' {k : Nat} (v : BitVec (8*(k+1))):
   let (b, v') := bitvec_split_byte v
   v' ++ b = v := by
  apply eq_of_getLsb_eq
  intro i
  simp [getLsb_append]
  by_cases h: ((i : Nat) < 8)
  · simp [h]
  · simp [h]
    have lt: (i : Nat) - 8 < 8*k := by simp_all; omega
    have e : (8 + ((i : Nat) - 8)) = i := by simp_all
    simp [e, lt]
    done
  done

-- Splitting a bitvector of 8*k entries into bytes, little endian
def bitvec_to_byte_seq (k : Nat) (invec: BitVec (8*k)) : Vec Byte k :=
  if k_gt_0: (k > 0) then
    let (byte, remainder) := bitvec_split_byte invec
    have h: k - 1 + 1 = k := by omega
    h ▸ Vec.cons byte (bitvec_to_byte_seq (k-1) remainder)
 else
    have h: k = 0 := by omega
    h ▸ Vec.empty

-- Concatenating a little endian byte sequence into a bitvector
def byte_seq_to_bitvec: Vec Byte k → BitVec (8*k)
  | ⟨[], h⟩ =>
      let h' : 0 = 8*k := by simp_all; omega
      BitVec.cast h' (BitVec.ofNat 0 0)
  | ⟨a :: as, h⟩ =>
      let g : 8 * (k - 1) + 8 = 8 * k := by simp [←h]; omega
      BitVec.cast g (byte_seq_to_bitvec ⟨as, by simp[←h]⟩ ++ a)

@[simp]
theorem byte_seq_to_bitvec_cons:
  byte_seq_to_bitvec (Vec.cons byte v) = (byte_seq_to_bitvec v) ++ byte := by
    cases v; simp only [Vec.cons, byte_seq_to_bitvec]; rfl

-- Example
def example_bitvec : BitVec 128 := 0x0102030405060708090a0b0c0d0e0f#128
def example_byteseq  := bitvec_to_byte_seq 16 example_bitvec
def example_bitvec'  := byte_seq_to_bitvec example_byteseq
def example_byteseq' := bitvec_to_byte_seq 16 example_bitvec'

#eval example_bitvec
#eval example_bitvec'
#eval example_byteseq
#eval example_byteseq'

@[simp]
def Vec_0_singleton {k : Nat}: (x y : Vec α k) → k = 0 → x = y
  | ⟨[], _⟩, ⟨[], _⟩, _ => by simp
  | ⟨_ :: _, hx⟩, _, h => by simp at hx; omega
  | _, ⟨_ :: _, hy⟩, h => by simp at hy; omega

theorem bitvec_to_byte_seq_invA: ∀(x : Vec Byte k), bitvec_to_byte_seq k (byte_seq_to_bitvec x) = x
 | ⟨[], h⟩ => by
      have h: k = 0 := by simp_all
      rw [byte_seq_to_bitvec]
      rw [bitvec_to_byte_seq]
      simp_all [Vec.empty]
      apply Vec_0_singleton
      assumption
 | ⟨x :: xs, h⟩ => by
    have k_gt_0: k > 0 := by simp_all; omega
    let h' : xs.length = k - 1 := by simp_all; omega
    let x' : Vec Byte (k-1) := ⟨xs, h'⟩
    let h : bitvec_to_byte_seq (k - 1) (byte_seq_to_bitvec x') = x' :=
      bitvec_to_byte_seq_invA x'
    rw [byte_seq_to_bitvec, bitvec_to_byte_seq]
    simp_all [bitvec_split_byte_append, Vec.cons]
    apply Vec.ext''; simp
    done

theorem bitvec_to_byte_seq_invB: ∀(k : Nat) (x : BitVec (8*k)), byte_seq_to_bitvec (bitvec_to_byte_seq k x) = x
 | 0, x => by simp
 | k+1, x => by
    rw [bitvec_to_byte_seq]
    have kp1_gt_0: k + 1 > 0 := by simp
    simp [kp1_gt_0]
    let x' := (bitvec_split_byte x).snd
    have t' : byte_seq_to_bitvec (bitvec_to_byte_seq (k + 1 - 1) x') = x' := by
      exact (bitvec_to_byte_seq_invB k _)
    simp only [t', bitvec_split_byte_append' x]

/-
  3.4 The state
-/

/- We deal with three different presentations of the AES state:
   1/ As a bitvector of length 128
   2/ As a byte vector length 16
   3/ As a 4x4 grid of bytes
-/

/-- Length 16 vectors <-> 4x4 arrays -/

abbrev AESStateBitVec := BitVec 128
abbrev AESStateVec := Vec Byte 16
abbrev AESStateArr := Vec (Vec Byte 4) 4

def AES_State_BitVec_to_Vec (x: AESStateBitVec): AESStateVec := bitvec_to_byte_seq 16 x

def AESStateVec_to_Arr (x : AESStateVec): AESStateArr :=
  ⟨[⟨[x[0], x[4], x[8] , x[12]], by simp⟩,
    ⟨[x[1], x[5], x[9] , x[13]], by simp⟩,
    ⟨[x[2], x[6], x[10], x[14]], by simp⟩,
    ⟨[x[3], x[7], x[11], x[15]], by simp⟩], by simp⟩

def AESStateArr_to_Vec (x : AESStateArr) : AESStateVec :=
  ⟨[ x[0][0], x[1][0], x[2][0], x[3][0],
     x[0][1], x[1][1], x[2][1], x[3][1],
     x[0][2], x[1][2], x[2][2], x[3][2],
     x[0][3], x[1][3], x[2][3], x[3][3] ], by simp⟩

theorem lt_succ_iff_lt_or_eq {n m : Nat} (h : 0 < m) : (n < m) <-> (n < m-1 ∨ n = m-1) := by
  have hs: m = Nat.succ (m - 1) := by omega
  rw [hs, Nat.lt_succ_iff_lt_or_eq]; simp
  done

theorem AESStateVec_to_Arr' (x : AESStateVec) (i j : Nat) (hi: i < 4) (hj: j < 4):
  have h: 4*j + i < 16 := by omega
  (AESStateVec_to_Arr x)[i][j] = x[4*j + i] := by
     simp [lt_succ_iff_lt_or_eq, Nat.not_lt_zero] at hi
     simp [lt_succ_iff_lt_or_eq, Nat.not_lt_zero] at hj
     elim Or.elim <;> try simp_all <;> simp [AESStateVec_to_Arr, Vec.get, GetElem.getElem, GetElem_Vec, List.get]
     done

def AESStateArr_to_Vec_invA (x : AESStateVec): (AESStateArr_to_Vec (AESStateVec_to_Arr x)) = x := by
  simp [AESStateArr_to_Vec, AESStateVec_to_Arr']
  ext
  rename_i i hi
  simp [lt_succ_iff_lt_or_eq, Nat.not_lt_zero] at hi
  elim Or.elim <;> try simp_all <;> simp [AESStateVec_to_Arr, Vec.get, GetElem.getElem, GetElem_Vec, List.get]
  done

def AESStateArr_to_Vec_invB (x : AESStateArr): (AESStateVec_to_Arr (AESStateArr_to_Vec x)) = x := by
  simp [AESStateArr_to_Vec, AESStateVec_to_Arr']
  ext
  rename_i i hi j hj
  simp [lt_succ_iff_lt_or_eq, Nat.not_lt_zero] at hi
  simp [lt_succ_iff_lt_or_eq, Nat.not_lt_zero] at hj
  elim Or.elim <;> try simp_all <;> simp [AESStateVec_to_Arr, Vec.get, GetElem.getElem, GetElem_Vec, List.get]
  done
