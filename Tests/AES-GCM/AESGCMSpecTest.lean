/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Specs.AESArm
import Specs.GCM

-- Reference: https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf

namespace AES256GCMSpecTest

open BitVec

-- Reversing bytes in inputs and output because AES uses little-endian
def revCIPH (CIPH : BitVec n -> BitVec m -> BitVec n)
  (h₀ : 8 ∣ n) (h₁ : 8 ∣ m) (p : BitVec n) (k : BitVec m) :=
  (rev_elems n 8
    (CIPH (rev_elems n 8 p h₀ (by decide)) (rev_elems m 8 k h₁ (by decide)))
    h₀ (by decide))

def CIPH_128' : GCM.Cipher (n := 128) (m := 128) :=
  AESArm.AES_encrypt (Param := AESArm.AES128KBR)

def CIPH_128 : GCM.Cipher (n := 128) (m := 128) :=
  revCIPH CIPH_128' (by decide) (by decide)

def GCM_AE_128 : BitVec 128 → (t : Nat) → BitVec lv → BitVec p → BitVec a
  → (BitVec p) × (BitVec t) := GCM.GCM_AE CIPH_128

def GCM_AD_128 : BitVec 128 → BitVec lv → BitVec c → BitVec a → BitVec t
  → Option (BitVec c) := GCM.GCM_AD CIPH_128

def CIPH_192' : GCM.Cipher (n := 128) (m := 192) :=
  AESArm.AES_encrypt (Param := AESArm.AES192KBR)

def CIPH_192 : GCM.Cipher (n := 128) (m := 192) :=
  revCIPH CIPH_192' (by decide) (by decide)

def GCM_AE_192 : BitVec 192 → (t : Nat) → BitVec lv → BitVec p → BitVec a
  → (BitVec p) × (BitVec t) := GCM.GCM_AE CIPH_192

def GCM_AD_192 : BitVec 192 → BitVec lv → BitVec c → BitVec a → BitVec t
  → Option (BitVec c) := GCM.GCM_AD CIPH_192

def CIPH_256' : GCM.Cipher (n := 128) (m := 256) :=
  AESArm.AES_encrypt (Param := AESArm.AES256KBR)

def CIPH_256 : GCM.Cipher (n := 128) (m := 256) :=
  revCIPH CIPH_256' (by decide) (by decide)

def GCM_AE_256 : BitVec 256 → (t : Nat) → BitVec lv → BitVec p → BitVec a
  → (BitVec p) × (BitVec t) := GCM.GCM_AE CIPH_256

def GCM_AD_256 : BitVec 256 → BitVec lv → BitVec c → BitVec a → BitVec t
  → Option (BitVec c) := GCM.GCM_AD CIPH_256

-- Test Vector 0

def K0 : BitVec 128 := 0
def IV0 : BitVec 96 := 0
def P0 : BitVec 0 := BitVec.nil
def A0 : BitVec 0 := BitVec.nil
def C0 : BitVec 0 := BitVec.nil
def T0 : BitVec 128 := 0x58e2fccefa7e3061367f1d57a4e7455a#128
example : GCM_AE_128 K0 128 IV0 P0 A0 = (C0, T0) := by native_decide
example : GCM_AD_128 K0 IV0 C0 A0 T0 = P0 := by native_decide

-- Test Vector 1

def K1 : BitVec 128 := 0
def IV1 : BitVec 96 := 0
def P1 : BitVec 128 := 0
def A1 : BitVec 0 := BitVec.nil
def C1 : BitVec 128 := 0x0388dace60b6a392f328c2b971b2fe78#128
def T1 : BitVec 128 := 0xab6e47d42cec13bdf53a67b21257bddf#128
example : GCM_AE_128 K1 128 IV1 P1 A1 = (C1, T1) := by native_decide
example : GCM_AD_128 K1 IV1 C1 A1 T1 = P1 := by native_decide

-- Test Vector 2

def K2 : BitVec 128 := 0xfeffe9928665731c6d6a8f9467308308#128
def IV2 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P2 : BitVec 512 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255#512
def A2 : BitVec 0 := BitVec.nil
def C2 : BitVec 512 := 0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985#512
def T2 : BitVec 128 := 0x4d5c2af327cd64a62cf35abd2ba6fab4#128
example : GCM_AE_128 K2 128 IV2 P2 A2 = (C2, T2) := by native_decide
example : GCM_AD_128 K2 IV2 C2 A2 T2 = P2 := by native_decide

-- Test Vector 3

def K3 : BitVec 128 := 0xfeffe9928665731c6d6a8f9467308308#128
def IV3 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P3 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A3 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C3 : BitVec 480 := 0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091#480
def T3 : BitVec 128 := 0x5bc94fbc3221a5db94fae95ae7121a47#128
example : GCM_AE_128 K3 128 IV3 P3 A3 = (C3, T3) := by native_decide
example : GCM_AD_128 K3 IV3 C3 A3 T3 = P3 := by native_decide

-- Test Vector 4

def K4 : BitVec 128 := 0xfeffe9928665731c6d6a8f9467308308#128
def IV4 : BitVec 64 := 0xcafebabefacedbad#64
def P4 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A4 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C4 : BitVec 480 := 0x61353b4c2806934a777ff51fa22a4755699b2a714fcdc6f83766e5f97b6c742373806900e49f24b22b097544d4896b424989b5e1ebac0f07c23f4598#480
def T4 : BitVec 128 := 0x3612d2e79e3b0785561be14aaca2fccb#128
example : GCM_AE_128 K4 128 IV4 P4 A4 = (C4, T4) := by native_decide
example : GCM_AD_128 K4 IV4 C4 A4 T4 = P4 := by native_decide

-- Test Vector 5

def K5 : BitVec 128 := 0xfeffe9928665731c6d6a8f9467308308#128
def IV5 : BitVec 480 := 0x9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b#480
def P5 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A5 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C5 : BitVec 480 := 0x8ce24998625615b603a033aca13fb894be9112a5c3a211a8ba262a3cca7e2ca701e4a9a4fba43c90ccdcb281d48c7c6fd62875d2aca417034c34aee5#480
def T5 : BitVec 128 := 0x619cc5aefffe0bfa462af43c1699d050#128
example : GCM_AE_128 K5 128 IV5 P5 A5 = (C5, T5) := by native_decide
example : GCM_AD_128 K5 IV5 C5 A5 T5 = P5 := by native_decide

-- Test Vector 6

def K6 : BitVec 192 := 0
def IV6 : BitVec 96 := 0
def P6 : BitVec 0 := BitVec.nil
def A6 : BitVec 0 := BitVec.nil
def C6 : BitVec 0 := BitVec.nil
def T6 : BitVec 128 := 0xcd33b28ac773f74ba00ed1f312572435#128
example : GCM_AE_192 K6 128 IV6 P6 A6 = (C6, T6) := by native_decide
example : GCM_AD_192 K6 IV6 C6 A6 T6 = P6 := by native_decide

-- Test Vector 7

def K7 : BitVec 192 := 0
def IV7 : BitVec 96 := 0
def P7 : BitVec 128 := 0
def A7 : BitVec 0 := BitVec.nil
def C7 : BitVec 128 := 0x98e7247c07f0fe411c267e4384b0f600#128
def T7 : BitVec 128 := 0x2ff58d80033927ab8ef4d4587514f0fb#128
example : GCM_AE_192 K7 128 IV7 P7 A7 = (C7, T7) := by native_decide
example : GCM_AD_192 K7 IV7 C7 A7 T7 = P7 := by native_decide

-- Test Vector 8

def K8 : BitVec 192 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c#192
def IV8 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P8 : BitVec 512 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255#512
def A8 : BitVec 0 := BitVec.nil
def C8 : BitVec 512 := 0x3980ca0b3c00e841eb06fac4872a2757859e1ceaa6efd984628593b40ca1e19c7d773d00c144c525ac619d18c84a3f4718e2448b2fe324d9ccda2710acade256#512
def T8 : BitVec 128 := 0x9924a7c8587336bfb118024db8674a14#128
example : GCM_AE_192 K8 128 IV8 P8 A8 = (C8, T8) := by native_decide
example : GCM_AD_192 K8 IV8 C8 A8 T8 = P8 := by native_decide

-- Test Vector 9

def K9 : BitVec 192 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c#192
def IV9 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P9 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A9 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C9 : BitVec 480 := 0x3980ca0b3c00e841eb06fac4872a2757859e1ceaa6efd984628593b40ca1e19c7d773d00c144c525ac619d18c84a3f4718e2448b2fe324d9ccda2710#480
def T9 : BitVec 128 := 0x2519498e80f1478f37ba55bd6d27618c#128
example : GCM_AE_192 K9 128 IV9 P9 A9 = (C9, T9) := by native_decide
example : GCM_AD_192 K9 IV9 C9 A9 T9 = P9 := by native_decide

-- Test Vector 10

def K10 : BitVec 192 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c#192
def IV10 : BitVec 64:= 0xcafebabefacedbad#64
def P10 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A10 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C10 : BitVec 480 := 0x0f10f599ae14a154ed24b36e25324db8c566632ef2bbb34f8347280fc4507057fddc29df9a471f75c66541d4d4dad1c9e93a19a58e8b473fa0f062f7#480
def T10 : BitVec 128 := 0x65dcc57fcf623a24094fcca40d3533f8#128
example : GCM_AE_192 K10 128 IV10 P10 A10 = (C10, T10) := by native_decide
example : GCM_AD_192 K10 IV10 C10 A10 T10 = P10 := by native_decide

-- Test Vector 11

def K11 : BitVec 192 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c#192
def IV11 : BitVec 480 := 0x9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b#480
def P11 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A11 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C11 : BitVec 480 := 0xd27e88681ce3243c4830165a8fdcf9ff1de9a1d8e6b447ef6ef7b79828666e4581e79012af34ddd9e2f037589b292db3e67c036745fa22e7e9b7373b#480
def T11 : BitVec 128 := 0xdcf566ff291c25bbb8568fc3d376a6d9#128
example : GCM_AE_192 K11 128 IV11 P11 A11 = (C11, T11) := by native_decide
example : GCM_AD_192 K11 IV11 C11 A11 T11 = P11 := by native_decide

-- Test Vector 12

def K12 : BitVec 256 := 0
def IV12 : BitVec 96 := 0
def P12 : BitVec 0 := BitVec.nil
def A12 : BitVec 0 := BitVec.nil
def C12 : BitVec 0 := BitVec.nil
def T12 : BitVec 128 := 0x530f8afbc74536b9a963b4f1c4cb738b#128
example : GCM_AE_256 K12 128 IV12 P12 A12 = (C12, T12) := by native_decide
example : GCM_AD_256 K12 IV12 C12 A12 T12 = P12 := by native_decide

-- Test Vector 13

def K13 : BitVec 256 := 0
def IV13 : BitVec 96 := 0
def P13 : BitVec 128 := 0
def A13 : BitVec 0 := BitVec.nil
def C13 : BitVec 128 := 0xcea7403d4d606b6e074ec5d3baf39d18#128
def T13 : BitVec 128 := 0xd0d1c8a799996bf0265b98b5d48ab919#128
example : GCM_AE_256 K13 128 IV13 P13 A13 = (C13, T13) := by native_decide
example : GCM_AD_256 K13 IV13 C13 A13 T13 = P13 := by native_decide

-- Test Vector 14

def K14 : BitVec 256 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256
def IV14 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P14 : BitVec 512 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255#512
def A14 : BitVec 0 := BitVec.nil
def C14 : BitVec 512 := 0x522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad#512
def T14 : BitVec 128 := 0xb094dac5d93471bdec1a502270e3cc6c#128
example : GCM_AE_256 K14 128 IV14 P14 A14 = (C14, T14) := by native_decide
example : GCM_AD_256 K14 IV14 C14 A14 T14 = P14 := by native_decide

-- Test Vector 15

def K15 : BitVec 256 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256
def IV15 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P15 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A15 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C15 : BitVec 480 := 0x522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662#480
def T15 : BitVec 128 := 0x76fc6ece0f4e1768cddf8853bb2d551b#128
example : GCM_AE_256 K15 128 IV15 P15 A15 = (C15, T15) := by native_decide
example : GCM_AD_256 K15 IV15 C15 A15 T15 = P15 := by native_decide

-- Test Vector 16

def K16 : BitVec 256 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256
def IV16 : BitVec 64:= 0xcafebabefacedbad#64
def P16 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A16 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C16 : BitVec 480 := 0xc3762df1ca787d32ae47c13bf19844cbaf1ae14d0b976afac52ff7d79bba9de0feb582d33934a4f0954cc2363bc73f7862ac430e64abe499f47c9b1f#480
def T16 : BitVec 128 := 0x3a337dbf46a792c45e454913fe2ea8f2#128
example : GCM_AE_256 K16 128 IV16 P16 A16 = (C16, T16) := by native_decide
example : GCM_AD_256 K16 IV16 C16 A16 T16 = P16 := by native_decide

-- Test Vector 17

def K17 : BitVec 256 := 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256
def IV17 : BitVec 480 := 0x9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b#480
def P17 : BitVec 480 := 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480
def A17 : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160
def C17 : BitVec 480 := 0x5a8def2f0c9e53f1f75d7853659e2a20eeb2b22aafde6419a058ab4f6f746bf40fc0c3b780f244452da3ebf1c5d82cdea2418997200ef82e44ae7e3f#480
def T17 : BitVec 128 := 0xa44a8266ee1c8eb0c8b5d4cf5ae9f19a#128
example : GCM_AE_256 K17 128 IV17 P17 A17 = (C17, T17) := by native_decide
example : GCM_AD_256 K17 IV17 C17 A17 T17 = P17 := by native_decide

end AES256GCMSpecTest
