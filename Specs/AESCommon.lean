/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
import Data.BitVec

namespace AESCommon

open BitVec

-------------------------------------------------------
-- Constants

def SBOX :=
  --   F E D C B A 9 8 7 6 5 4 3 2 1 0
  [ 0x16bb54b00f2d99416842e6bf0d89a18c#128, -- F
    0xdf2855cee9871e9b948ed9691198f8e1#128, -- E
    0x9e1dc186b95735610ef6034866b53e70#128, -- D
    0x8a8bbd4b1f74dde8c6b4a61c2e2578ba#128, -- C
    0x08ae7a65eaf4566ca94ed58d6d37c8e7#128, -- B
    0x79e4959162acd3c25c2406490a3a32e0#128, -- A
    0xdb0b5ede14b8ee4688902a22dc4f8160#128, -- 9
    0x73195d643d7ea7c41744975fec130ccd#128, -- 8
    0xd2f3ff1021dab6bcf5389d928f40a351#128, -- 7
    0xa89f3c507f02f94585334d43fbaaefd0#128, -- 6
    0xcf584c4a39becb6a5bb1fc20ed00d153#128, -- 5
    0x842fe329b3d63b52a05a6e1b1a2c8309#128, -- 4
    0x75b227ebe28012079a059618c323c704#128, -- 3
    0x1531d871f1e5a534ccf73f362693fdb7#128, -- 2
    0xc072a49cafa2d4adf04759fa7dc982ca#128, -- 1
    0x76abd7fe2b670130c56f6bf27b777c63#128  -- 0
  ]

def ShiftRows (op : BitVec 128) : BitVec 128 :=
  extractLsb 95 88 op ++ extractLsb 55 48 op ++
  extractLsb 15 8 op ++ extractLsb 103 96 op ++
  extractLsb 63 56 op ++ extractLsb 23 16 op ++
  extractLsb 111 104 op ++ extractLsb 71 64 op ++
  extractLsb 31 24 op ++ extractLsb 119 112 op ++
  extractLsb 79 72 op ++ extractLsb 39 32 op ++
  extractLsb 127 120 op ++ extractLsb 87 80 op ++
  extractLsb 47 40 op ++ extractLsb 7 0 op

def SubBytes_aux (i : Nat) (op : BitVec 128) (out : BitVec 128)
  : BitVec 128 :=
  if h₀ : 16 <= i then
    out
  else
    let idx := (extractLsb (i * 8 + 7) (i * 8) op).toNat
    let val := extractLsb (idx * 8 + 7) (idx * 8) $ BitVec.flatten SBOX
    have h₁ : idx * 8 + 7 - idx * 8 + 1 = i * 8 + 7 - i * 8 + 1 := by omega
    let out := BitVec.partInstall (i * 8 + 7) (i * 8) (BitVec.cast h₁ val) out
    have _ : 15 - i < 16 - i := by omega
    SubBytes_aux (i + 1) op out
  termination_by (16 - i)

def SubBytes (op : BitVec 128) : BitVec 128 :=
  SubBytes_aux 0 op (BitVec.zero 128)

def MixColumns_aux (c : Nat)
  (in0 : BitVec 32) (in1 : BitVec 32) (in2 : BitVec 32) (in3 : BitVec 32)
  (out0 : BitVec 32) (out1 : BitVec 32) (out2 : BitVec 32) (out3 : BitVec 32)
  (FFmul02 : BitVec 8 -> BitVec 8) (FFmul03 : BitVec 8 -> BitVec 8)
  : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  if h₀ : 4 <= c then
    (out0, out1, out2, out3)
  else
    let lo := c * 8
    let hi := lo + 7
    have h₁ : hi - lo + 1 = 8 := by omega
    let in0_byte := BitVec.cast h₁ $ extractLsb hi lo in0
    let in1_byte := BitVec.cast h₁ $ extractLsb hi lo in1
    let in2_byte := BitVec.cast h₁ $ extractLsb hi lo in2
    let in3_byte := BitVec.cast h₁ $ extractLsb hi lo in3
    let val0 := BitVec.cast h₁.symm $ (FFmul02 in0_byte ^^^ FFmul03 in1_byte ^^^ in2_byte ^^^ in3_byte)
    let out0 := BitVec.partInstall hi lo val0 out0
    let val1 := BitVec.cast h₁.symm $ (FFmul02 in1_byte ^^^ FFmul03 in2_byte ^^^ in3_byte ^^^ in0_byte)
    let out1 := BitVec.partInstall hi lo val1 out1
    let val2 := BitVec.cast h₁.symm $ (FFmul02 in2_byte ^^^ FFmul03 in3_byte ^^^ in0_byte ^^^ in1_byte)
    let out2 := BitVec.partInstall hi lo val2 out2
    let val3 := BitVec.cast h₁.symm $ (FFmul02 in3_byte ^^^ FFmul03 in0_byte ^^^ in1_byte ^^^ in2_byte)
    let out3 := BitVec.partInstall hi lo val3 out3
    have _ : 3 - c < 4 - c := by omega
    MixColumns_aux (c + 1) in0 in1 in2 in3 out0 out1 out2 out3 FFmul02 FFmul03
  termination_by (4 - c)

def MixColumns (op : BitVec 128) (FFmul02 : BitVec 8 -> BitVec 8)
  (FFmul03 : BitVec 8 -> BitVec 8) : BitVec 128 :=
  let in0 :=
    extractLsb 103 96 op ++ extractLsb 71 64 op ++
    extractLsb 39 32 op ++ extractLsb 7 0 op
  let in1 :=
    extractLsb 111 104 op ++ extractLsb 79 72 op ++
    extractLsb 47 40 op ++ extractLsb 15 8 op
  let in2 :=
    extractLsb 119 112 op ++ extractLsb 87 80 op ++
    extractLsb 55 48 op ++ extractLsb 23 16 op
  let in3 :=
    extractLsb 127 120 op ++ extractLsb 95 88 op ++
    extractLsb 63 56 op ++ extractLsb 31 24 op
  let (out0, out1, out2, out3) :=
    (BitVec.zero 32, BitVec.zero 32,
     BitVec.zero 32, BitVec.zero 32)
  let (out0, out1, out2, out3) :=
    MixColumns_aux 0 in0 in1 in2 in3 out0 out1 out2 out3 FFmul02 FFmul03
  extractLsb 31 24 out3 ++ extractLsb 31 24 out2 ++
  extractLsb 31 24 out1 ++ extractLsb 31 24 out0 ++
  extractLsb 23 16 out3 ++ extractLsb 23 16 out2 ++
  extractLsb 23 16 out1 ++ extractLsb 23 16 out0 ++
  extractLsb 15 8 out3 ++ extractLsb 15 8 out2 ++
  extractLsb 15 8 out1 ++ extractLsb 15 8 out0 ++
  extractLsb 7 0 out3 ++ extractLsb 7 0 out2 ++
  extractLsb 7 0 out1 ++ extractLsb 7 0 out0

end AESCommon
