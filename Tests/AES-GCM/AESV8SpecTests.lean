/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Specs.AESV8
import Tests.«AES-GCM».AESV8ProgramTests

open BitVec

namespace AESHWSetEncryptKeySpecTest

example : AESV8.AESHWSetEncryptKey 0#128 (by simp)
  = {rounds := (10#64), rd_key := AESHWSetEncryptKeyProgramTest.AES128.rd_key}
  := by native_decide

example : AESV8.AESHWSetEncryptKey 0#192 (by simp)
  = {rounds := (12#64), rd_key := AESHWSetEncryptKeyProgramTest.AES192.rd_key}
  := by native_decide

example : AESV8.AESHWSetEncryptKey 0#256 (by simp)
  = {rounds := (14#64), rd_key := AESHWSetEncryptKeyProgramTest.AES256.rd_key}
  := by native_decide

end AESHWSetEncryptKeySpecTest

namespace AESHWEncryptSpecTest

example : let key :=
  { rounds := (10#64),
    rd_key := AESHWSetEncryptKeyProgramTest.AES128.rd_key : AESV8.AESKey }
  AESV8.AESHWEncrypt (List.replicate 16 0#8) key (by simp) (by simp)
  = AESHWEncryptProgramTest.AES128.out_block := by native_decide

example : let key :=
  { rounds := (12#64),
    rd_key := AESHWSetEncryptKeyProgramTest.AES192.rd_key : AESV8.AESKey }
  AESV8.AESHWEncrypt (List.replicate 16 0#8) key (by simp) (by simp)
  = AESHWEncryptProgramTest.AES192.out_block := by native_decide

example : let key :=
  { rounds := (14#64),
    rd_key := AESHWSetEncryptKeyProgramTest.AES256.rd_key : AESV8.AESKey }
  AESV8.AESHWEncrypt (List.replicate 16 0#8) key (by simp) (by simp)
  = AESHWEncryptProgramTest.AES256.out_block := by native_decide

end AESHWEncryptSpecTest

namespace AESHWCtr32EncryptBlocksSpecTest

example : let key :=
  { rounds := (10#64),
    rd_key := AESHWSetEncryptKeyProgramTest.AES128.rd_key : AESV8.AESKey }
  AESV8.AESHWCtr32EncryptBlocks (List.replicate 16 0#8) 1 key 0#128
    (by simp) (by simp only [List.length_replicate]; omega) (by simp)
  = List.take 16 AESHWCtr32EncryptBlocksProgramTest.AES128Ctr32.buf_res_128
  := by native_decide

example : let key :=
  { rounds := (12#64),
    rd_key := AESHWSetEncryptKeyProgramTest.AES192.rd_key : AESV8.AESKey }
  AESV8.AESHWCtr32EncryptBlocks (List.replicate 16 0#8) 1 key 0#128
    (by simp) (by simp only [List.length_replicate]; omega) (by simp)
  = List.take 16 AESHWCtr32EncryptBlocksProgramTest.AES192Ctr32.buf_res_192
  := by native_decide

example : let key :=
  { rounds := (14#64),
    rd_key := AESHWSetEncryptKeyProgramTest.AES256.rd_key : AESV8.AESKey }
  AESV8.AESHWCtr32EncryptBlocks (List.replicate 16 0#8) 1 key 0#128
    (by simp) (by simp only [List.length_replicate]; omega) (by simp)
  = List.take 16 AESHWCtr32EncryptBlocksProgramTest.AES256Ctr32.buf_res_256
  := by native_decide

example : let key :=
  { rounds := (14#64),
    rd_key := AESHWSetEncryptKeyProgramTest.AES256.rd_key : AESV8.AESKey }
  AESV8.AESHWCtr32EncryptBlocks (List.replicate 80 0#8) 5 key 0#128
    (by simp) (by simp only [List.length_replicate]; omega) (by simp)
  = List.take 80 AESHWCtr32EncryptBlocksProgramTest.AES256Ctr32.buf_res_256
  := by native_decide

end AESHWCtr32EncryptBlocksSpecTest
