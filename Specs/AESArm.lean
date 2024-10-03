/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Insts.DPSFP.Crypto_aes
import Specs.AESCommon

-- References : https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
--              https://csrc.nist.gov/csrc/media/projects/cryptographic-standards-and-guidelines/documents/aes-development/rijndael-ammended.pdf
--
--------------------------------------------------
-- The NIST specification has the following rounds:
--
-- AddRoundKey key0
-- for k in key1 to key9
--   SubBytes
--   ShiftRows
--   MixColumns
--   AddRoundKey
-- SubBytes
-- ShiftRows
-- AddRoundKey key10
--
-- The Arm implementation has an optimization that commute intermediate steps:
--
-- for k in key0 to key8
--   AddRoundKey + ShiftRows + SubBytes (AESE k)
--   MixColumns (AESMC)
-- AddRoundKey + ShiftRows + SubBytes (AESE key9)
-- AddRoundKey key10
--
-- Note: SubBytes and ShiftRows are commutative because
--       SubBytes is a byte-wise operation
--
--------------------------------------------------

namespace AESArm

open BitVec

def WordSize := 32
def BlockSize := 128

-- General comment: Maybe consider Lists vs Vectors?
-- https://github.com/joehendrix/lean-crypto/blob/323ee9b1323deed5240762f4029700a246ecd9d5/lib/Crypto/Vector.lean#L96

def Rcon : List (BitVec WordSize) :=
[ 0x00000001#32,
  0x00000002#32,
  0x00000004#32,
  0x00000008#32,
  0x00000010#32,
  0x00000020#32,
  0x00000040#32,
  0x00000080#32,
  0x0000001b#32,
  0x00000036#32 ]

-------------------------------------------------------
-- types

-- Key-Block-Round Combinations
structure KBR where
  key_len : Nat
  block_size : Nat
  Nk := key_len / 32
  Nb := block_size / 32
  Nr : Nat
  h : block_size = BlockSize
deriving DecidableEq, Repr

def AES128KBR : KBR :=
  {key_len := 128, block_size := BlockSize, Nr := 10, h := by decide}
def AES192KBR : KBR :=
  {key_len := 192, block_size := BlockSize, Nr := 12, h := by decide}
def AES256KBR : KBR :=
  {key_len := 256, block_size := BlockSize, Nr := 14, h := by decide}

def KeySchedule : Type := List (BitVec WordSize)

-- Declare KeySchedule to be an instance HAppend
-- so we can apply `++` to KeySchedules propertly
instance : HAppend KeySchedule KeySchedule KeySchedule where
  hAppend := List.append

-------------------------------------------------------

def sbox (ind : BitVec 8) : BitVec 8 :=
  match_bv ind with
  | [x:4, y:4] =>
    have h : (x.toNat * 128 + y.toNat * 8 + 7) - (x.toNat * 128 + y.toNat * 8) + 1 = 8 :=
      by omega
    BitVec.cast h $ extractLsb
      (x.toNat * 128 + y.toNat * 8 + 7)
      (x.toNat * 128 + y.toNat * 8) $ BitVec.flatten AESCommon.SBOX
  | _ => ind -- unreachable case

-- Note: The RotWord function is written in little endian
def RotWord (w : BitVec WordSize) : BitVec WordSize :=
  match_bv w with
  | [a3:8, a2:8, a1:8, a0:8] => a0 ++ a3 ++ a2 ++ a1
  | _ => w -- unreachable case

def SubWord (w : BitVec WordSize) : BitVec WordSize :=
  match_bv w with
  | [a3:8, a2:8, a1:8, a0:8] => (sbox a3) ++ (sbox a2) ++ (sbox a1) ++ (sbox a0)
  | _ => w -- unreachable case

protected def InitKey {Param : KBR} (i : Nat) (key : BitVec Param.key_len)
  (acc : KeySchedule) : KeySchedule :=
  match i with
  | 0 => acc
  | i' + 1 =>
    let wd := extractLsb' ((i - 1) * 32) 32 key
    AESArm.InitKey (Param := Param) i' key (wd :: acc)

protected def KeyExpansion_helper {Param : KBR} (i : Nat) (ks : KeySchedule)
  : KeySchedule :=
  match i with
  | 0 => ks
  | i' + 1 =>
    let i := 4 * Param.Nr + 4 - i
    let tmp := List.get! ks (i - 1)
    let tmp :=
      if i % Param.Nk == 0 then
        (SubWord (RotWord tmp)) ^^^ (List.get! Rcon $ (i / Param.Nk) - 1)
      else if Param.Nk > 6 && i % Param.Nk == 4 then
        SubWord tmp
      else
        tmp
    let res := (List.get! ks (i - Param.Nk)) ^^^ tmp
    let ks := List.append ks [ res ]
    AESArm.KeyExpansion_helper (Param := Param) i' ks

def KeyExpansion {Param : KBR} (key : BitVec Param.key_len)
  : KeySchedule :=
  let seeded := AESArm.InitKey (Param := Param) Param.Nk key []
  AESArm.KeyExpansion_helper (Param := Param) (4 * Param.Nr + 4 - Param.Nk) seeded

def SubBytes {Param : KBR} (state : BitVec Param.block_size)
  : BitVec Param.block_size :=
  have h : Param.block_size = 128 := by simp only [Param.h, BlockSize]
  BitVec.cast h.symm $ AESCommon.SubBytes (BitVec.cast h state)

def ShiftRows {Param : KBR} (state : BitVec Param.block_size)
  : BitVec Param.block_size :=
  have h : Param.block_size = 128 := by simp only [Param.h, BlockSize]
  BitVec.cast h.symm $ AESCommon.ShiftRows (BitVec.cast h state)

def XTimes (bv : BitVec 8) : BitVec 8 :=
  let res := truncate 7 bv ++ 0b0#1
  if getLsbD bv 7 then res ^^^ 0b00011011#8 else res

def MixColumns {Param : KBR} (state : BitVec Param.block_size)
  : BitVec Param.block_size :=
  have h : Param.block_size = 128 := by simp only [Param.h, BlockSize]
  let FFmul02 := fun (x : BitVec 8) => XTimes x
  let FFmul03 := fun (x : BitVec 8) => x ^^^ XTimes x
  BitVec.cast h.symm $ AESCommon.MixColumns (BitVec.cast h state) FFmul02 FFmul03

-- Convert bitvector quantification into bounded natural number quantification
theorem P_of_bv_to_of_nat {n : Nat} {P : BitVec n -> Prop}:
  (∀(x : Nat), x < 2^n → P (BitVec.ofNat n x)) →
  ∀(p : BitVec n), P p := by
  intro H p
  let x := p.toNat
  have p_eq : p = (BitVec.ofNat n x) := by simp only [x, BitVec.ofNat_toNat, truncate_eq]
  simp only [p_eq]
  apply H
  apply BitVec.isLt

set_option maxRecDepth 1000 in
protected theorem FFmul02_equiv : (fun x => XTimes x) = DPSFP.FFmul02 := by
  funext x
  let P := fun (x : BitVec 8) => XTimes x = DPSFP.FFmul02 x
  apply @P_of_bv_to_of_nat 8 P
  simp only [P]
  decide

set_option maxRecDepth 1000 in
protected theorem FFmul03_equiv : (fun x => x ^^^ XTimes x) = DPSFP.FFmul03 := by
  funext x
  let P := fun (x : BitVec 8) => x ^^^ XTimes x = DPSFP.FFmul03 x
  apply @P_of_bv_to_of_nat 8 P
  simp only [P]
  decide

theorem MixColumns_table_lookup_equiv {Param : KBR}
  (state : BitVec Param.block_size):
  have h : Param.block_size = 128 := by simp only [Param.h, BlockSize]
  MixColumns (Param := Param) state =
  BitVec.cast h.symm (DPSFP.AESMixColumns (BitVec.cast h state)) := by
    simp only [MixColumns, DPSFP.AESMixColumns]
    rw [AESArm.FFmul02_equiv, AESArm.FFmul03_equiv]

def AddRoundKey {Param : KBR} (state : BitVec Param.block_size)
  (roundKey : BitVec Param.block_size) : BitVec Param.block_size :=
  state ^^^ roundKey

protected def getKey {Param : KBR} (n : Nat) (w : KeySchedule) : BitVec Param.block_size :=
  let ind := 4 * n
  have h : WordSize + WordSize + WordSize + WordSize = Param.block_size := by
    simp only [WordSize, BlockSize, Param.h]
  BitVec.cast h
    ((List.get! w (ind + 3)) ++ (List.get! w (ind + 2)) ++
     (List.get! w (ind + 1)) ++ (List.get! w ind))

protected def AES_encrypt_with_ks_loop {Param : KBR} (round : Nat)
  (state : BitVec Param.block_size) (w : KeySchedule)
  : BitVec Param.block_size :=
  match round with
  | 0 => state
  | round' + 1 =>
    let round := Param.Nr - round
    let state := SubBytes state
    let state := ShiftRows state
    let state := MixColumns state
    let state := AddRoundKey state $ AESArm.getKey round w
    AESArm.AES_encrypt_with_ks_loop (Param := Param) round' state w

def AES_encrypt_with_ks {Param : KBR} (input : BitVec Param.block_size)
  (w : KeySchedule) : BitVec Param.block_size :=
  -- have h₀ : WordSize + WordSize + WordSize + WordSize = Param.block_size := by
  --   simp only [WordSize, BlockSize, Param.h]
  let state := AddRoundKey input $ (AESArm.getKey 0 w)
  let state := AESArm.AES_encrypt_with_ks_loop (Param := Param) (Param.Nr - 1) state w
  let state := SubBytes (Param := Param) state
  let state := ShiftRows (Param := Param) state
  AddRoundKey state $ AESArm.getKey Param.Nr w

def AES_encrypt {Param : KBR} (input : BitVec Param.block_size)
  (key : BitVec Param.key_len) : BitVec Param.block_size :=
  let ks := KeyExpansion (Param := Param) key
  AES_encrypt_with_ks (Param := Param) input ks

end AESArm
