/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Specs.AESArm

namespace AESV8

open BitVec

structure AESKey where
  rounds : BitVec 64
  rd_key : List (BitVec 32)
deriving DecidableEq, Repr

def AESHWSetEncryptKey {bits : Nat} (user_key : BitVec bits)
  (h : bits = 128 ∨ bits = 192 ∨ bits = 256) : AESKey :=
  let p : AESArm.KBR :=
    if bits = 128 then AESArm.AES128KBR
    else if bits = 192 then AESArm.AES192KBR
    else AESArm.AES256KBR
  have hh : bits = p.key_len := by
    simp only [p]
    simp only [AESArm.AES128KBR, AESArm.AES192KBR, AESArm.AES256KBR]
    cases h
    · rename_i h; simp [h]
    · rename_i h; cases h
      · rename_i h; simp [h]
      · rename_i h; simp [h]
  let rd_key : List (BitVec 32) :=
    AESArm.KeyExpansion (Param := p) (BitVec.cast hh user_key)
  { rounds := p.Nr, rd_key := rd_key }

example : let res :=
  { rounds := 10#64,
    rd_key := [ 0x00#32, 0x00#32, 0x00#32, 0x00#32,
                0x63636362#32, 0x63636362#32, 0x63636362#32, 0x63636362#32,
                0xc998989b#32, 0xaafbfbf9#32, 0xc998989b#32, 0xaafbfbf9#32,
                0x50349790#32, 0xfacf6c69#32, 0x3357f4f2#32, 0x99ac0f0b#32,
                0x7bda06ee#32, 0x81156a87#32, 0xb2429e75#32, 0x2bee917e#32,
                0x882b2e7f#32, 0x93e44f8#32, 0xbb7cda8d#32, 0x90924bf3#32,
                0x854b61ec#32, 0x8c752514#32, 0x3709ff99#32, 0xa79bb46a#32,
                0x87177521#32, 0xb625035#32, 0x3c6bafac#32, 0x9bf01bc6#32,
                0x3303f90e#32, 0x3861a93b#32, 0x40a0697#32, 0x9ffa1d51#32,
                0xe2d8d4b1#32, 0xdab97d8a#32, 0xdeb37b1d#32, 0x4149664c#32,
                0xcb5befb4#32, 0x11e2923e#32, 0xcf51e923#32, 0x8e188f6f#32
                ] : AESKey
    }
  AESHWSetEncryptKey 0#128 (by simp) = res := by native_decide

def AESHWEncrypt (in_block : List (BitVec 8)) (key : AESKey)
  (h1 : key.rounds = 10#64 ∨ key.rounds = 12#64 ∨ key.rounds = 14#64)
  (h2 : 8 * in_block.length = 128)
  : List (BitVec 8) :=
  let p : AESArm.KBR :=
    if key.rounds = 10 then AESArm.AES128KBR
    else if key.rounds = 12 then AESArm.AES192KBR
    else AESArm.AES256KBR
  -- AESArm.AES_encrypt_with_ks is little-endian
  let in_block := BitVec.flatten in_block
  let in_block :=
    rev_elems 128 8 (BitVec.cast h2 in_block) (by decide) (by decide)
  have h : p.block_size = 128 := by
    simp only [ p, AESArm.AES128KBR, AESArm.AES192KBR,
                AESArm.AES256KBR, AESArm.BlockSize ]
    cases h1
    · rename_i h; simp [h]
    · rename_i h; cases h
      · rename_i h; simp [h]
      · rename_i h; simp [h]
  let res_block :=
    AESArm.AES_encrypt_with_ks (Param := p)
      (BitVec.cast h.symm in_block) key.rd_key
  let res_block :=
    rev_elems 128 8 (BitVec.cast h res_block) (by decide) (by decide)
  split res_block 8 (by omega)

example : let in_block := List.replicate 16 0#8
  let key :=
  { rounds := 10#64,
    rd_key := [ 0x00#32, 0x00#32, 0x00#32, 0x00#32,
                0x63636362#32, 0x63636362#32, 0x63636362#32, 0x63636362#32,
                0xc998989b#32, 0xaafbfbf9#32, 0xc998989b#32, 0xaafbfbf9#32,
                0x50349790#32, 0xfacf6c69#32, 0x3357f4f2#32, 0x99ac0f0b#32,
                0x7bda06ee#32, 0x81156a87#32, 0xb2429e75#32, 0x2bee917e#32,
                0x882b2e7f#32, 0x93e44f8#32, 0xbb7cda8d#32, 0x90924bf3#32,
                0x854b61ec#32, 0x8c752514#32, 0x3709ff99#32, 0xa79bb46a#32,
                0x87177521#32, 0xb625035#32, 0x3c6bafac#32, 0x9bf01bc6#32,
                0x3303f90e#32, 0x3861a93b#32, 0x40a0697#32, 0x9ffa1d51#32,
                0xe2d8d4b1#32, 0xdab97d8a#32, 0xdeb37b1d#32, 0x4149664c#32,
                0xcb5befb4#32, 0x11e2923e#32, 0xcf51e923#32, 0x8e188f6f#32
                ] : AESKey
    }
  let out_block :=
    [ 0x66#8, 0xe9#8, 0x4b#8, 0xd4#8, 0xef#8, 0x8a#8, 0x2c#8, 0x3b#8,
      0x88#8, 0x4c#8, 0xfa#8, 0x59#8, 0xca#8, 0x34#8, 0x2b#8, 0x2e#8]
  have h : in_block.length = 16 := by
    simp only [in_block, List.length_replicate]
  AESHWEncrypt in_block key (by simp) (by simp only [h]) = out_block
  := by native_decide

def AESHWCtr32EncryptBlocks_helper {Param : AESArm.KBR} (in_blocks : BitVec m)
  (i : Nat) (len : Nat) (key : AESKey) (ivec : BitVec 128) (acc : BitVec m)
  (h1 : 128 ∣ m) (h2 : m / 128 = len)
  (h3 : Param = AESArm.AES128KBR
      ∨ Param = AESArm.AES192KBR
      ∨ Param = AESArm.AES256KBR)
  : BitVec m :=
  if i >= len then acc
  else
    let lo := m - (i + 1) * 128
    let hi := lo + 127
    have h5 : hi - lo + 1 = 128 := by omega
    let curr_block : BitVec 128 :=
      BitVec.cast h5 $ BitVec.extractLsb hi lo in_blocks
    have h4 : 128 = Param.block_size := by
      cases h3
      · rename_i h; simp only [h, AESArm.AES128KBR, AESArm.BlockSize]
      · rename_i h; cases h
        · rename_i h; simp only [h, AESArm.AES192KBR, AESArm.BlockSize]
        · rename_i h; simp only [h, AESArm.AES256KBR, AESArm.BlockSize]
    let ivec_rev := rev_elems 128 8 ivec (by decide) (by decide)
    let res_block : BitVec 128 :=
      BitVec.cast h4.symm $ AESArm.AES_encrypt_with_ks
        (Param := Param) (BitVec.cast h4 ivec_rev) key.rd_key
    let res_block := rev_elems 128 8 res_block (by decide) (by decide)
    let res_block := res_block ^^^ curr_block
    let new_acc := BitVec.partInstall hi lo (BitVec.cast h5.symm res_block) acc
    AESHWCtr32EncryptBlocks_helper (Param := Param)
      in_blocks (i + 1) len key (ivec + 1#128) new_acc h1 h2 h3
  termination_by (len - i)

def AESHWCtr32EncryptBlocks (in_blocks : List (BitVec 8)) (len : Nat)
  (key : AESKey) (ivec : BitVec 128)
  (h1 : key.rounds = 10#64 ∨ key.rounds = 12#64 ∨ key.rounds = 14#64)
  (h2 : 16 ∣ in_blocks.length) (h3 : in_blocks.length / 16 = len)
  : List (BitVec 8) :=
  let p : AESArm.KBR :=
    if key.rounds = 10 then AESArm.AES128KBR
    else if key.rounds = 12 then AESArm.AES192KBR
    else AESArm.AES256KBR
  have h : p = AESArm.AES128KBR
         ∨ p = AESArm.AES192KBR
         ∨ p = AESArm.AES256KBR := by
    cases h1
    · rename_i h; simp only [p, h]; simp
    · rename_i h; cases h
      · rename_i h; simp only [p, h]; simp
      · rename_i h; simp only [p, h]; simp
  let res := AESHWCtr32EncryptBlocks_helper (Param := p)
    (BitVec.flatten in_blocks) 0 len key ivec
    (BitVec.zero (8 * in_blocks.length)) (by omega) (by omega) h
  split res 8 (by omega)

example : let in_blocks := List.replicate 16 0#8
  let key :=
    { rounds := 10#64,
      rd_key := [ 0x00#32, 0x00#32, 0x00#32, 0x00#32,
                  0x63636362#32, 0x63636362#32, 0x63636362#32, 0x63636362#32,
                  0xc998989b#32, 0xaafbfbf9#32, 0xc998989b#32, 0xaafbfbf9#32,
                  0x50349790#32, 0xfacf6c69#32, 0x3357f4f2#32, 0x99ac0f0b#32,
                  0x7bda06ee#32, 0x81156a87#32, 0xb2429e75#32, 0x2bee917e#32,
                  0x882b2e7f#32, 0x93e44f8#32, 0xbb7cda8d#32, 0x90924bf3#32,
                  0x854b61ec#32, 0x8c752514#32, 0x3709ff99#32, 0xa79bb46a#32,
                  0x87177521#32, 0xb625035#32, 0x3c6bafac#32, 0x9bf01bc6#32,
                  0x3303f90e#32, 0x3861a93b#32, 0x40a0697#32, 0x9ffa1d51#32,
                  0xe2d8d4b1#32, 0xdab97d8a#32, 0xdeb37b1d#32, 0x4149664c#32,
                  0xcb5befb4#32, 0x11e2923e#32, 0xcf51e923#32, 0x8e188f6f#32
                  ] : AESKey
              }
  let ivec := 0#128
  let res := [ 0x66#8, 0xe9#8, 0x4b#8, 0xd4#8, 0xef#8, 0x8a#8, 0x2c#8, 0x3b#8,
               0x88#8, 0x4c#8, 0xfa#8, 0x59#8, 0xca#8, 0x34#8, 0x2b#8, 0x2e#8]
  AESHWCtr32EncryptBlocks in_blocks 1 key ivec
    (by simp) (by simp only [in_blocks, List.length_replicate]; omega)
    (by simp only [in_blocks, List.length_replicate]) = res
    := by native_decide

end AESV8
