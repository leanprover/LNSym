/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Specs.AES
import Specs.GCM

-- Reference: https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf

namespace AES256GCMSpecTest

open BitVec

def CIPH_128 : GCM.Cipher (n := 128) (m := 128) :=
  AES.AES_encrypt (Param := AES.AES128KBR)

def GCM_AE_128 : BitVec 128 → BitVec lv → BitVec p → BitVec a → (t : Nat)
  → (BitVec p) × (BitVec t) := GCM.GCM_AE (m := 128) CIPH_128

def GCM_AD_128 : BitVec 128 → BitVec lv → BitVec c → BitVec a → BitVec t
  → Option (BitVec c) := GCM.GCM_AD (m := 128) CIPH_128

def CIPH_256 : GCM.Cipher (n := 128) (m := 256) :=
  AES.AES_encrypt (Param := AES.AES256KBR)

def GCM_AE_256 : BitVec 256 → BitVec lv → BitVec p → BitVec a → (t : Nat)
  → (BitVec p) × (BitVec t) := GCM.GCM_AE (m := 256) CIPH_256

def GCM_AD_256 : BitVec 256 → BitVec lv → BitVec c → BitVec a → BitVec t
  → Option (BitVec c) := GCM.GCM_AD (m := 256) CIPH_256

-- Test Vector 0

def K0 : BitVec 128 := 0
def IV0 : BitVec 96 := 0
def P0 : BitVec 0 := BitVec.nil
def A0 : BitVec 0 := BitVec.nil
def C0 : BitVec 0 := BitVec.nil
def T0 : BitVec 128 := rev_elems 128 8 0x58e2fccefa7e3061367f1d57a4e7455a#128 (by decide) (by decide)
example : GCM_AE_128 K0 IV0 P0 A0 128 = (C0, T0) := by native_decide
example : GCM_AD_128 K0 IV0 C0 A0 T0 = P0 := by native_decide

-- Test Vector 1

def K1 : BitVec 128 := 0
def IV1 : BitVec 96 := 0
def P1 : BitVec 128 := 0
def A1 : BitVec 0 := BitVec.nil
def C1 : BitVec 128 := rev_elems 128 8 0x0388dace60b6a392f328c2b971b2fe78#128 (by decide) (by decide)
def T1 : BitVec 128 := rev_elems 128 8 0xab6e47d42cec13bdf53a67b21257bddf#128 (by decide) (by decide)
example : GCM_AE_128 K1 IV1 P1 A1 128 = (C1, T1) := by native_decide
example : GCM_AD_128 K1 IV1 C1 A1 T1 = P1 := by native_decide

-- Test Vector 2

def K2 : BitVec 128 := rev_elems 128 8 0xfeffe9928665731c6d6a8f9467308308#128 (by decide) (by decide)
def IV2 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P2 : BitVec 512 := rev_elems 512 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255#512 (by decide) (by decide)
def A2 : BitVec 0 := BitVec.nil
def C2 : BitVec 512 := rev_elems 512 8 0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985#512 (by decide) (by decide)
def T2 : BitVec 128 := rev_elems 128 8 0x4d5c2af327cd64a62cf35abd2ba6fab4#128 (by decide) (by decide)
example : GCM_AE_128 K2 IV2 P2 A2 128 = (C2, T2) := by native_decide
example : GCM_AD_128 K2 IV2 C2 A2 T2 = P2 := by native_decide

-- Test Vector 3

def K3 : BitVec 128 := rev_elems 128 8 0xfeffe9928665731c6d6a8f9467308308#128 (by decide) (by decide)
def IV3 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P3 : BitVec 480 := rev_elems 480 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480 (by decide) (by decide)
def A3 : BitVec 160 := rev_elems 160 8 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160 (by decide) (by decide)
def C3 : BitVec 480 := rev_elems 480 8 0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091#480 (by decide) (by decide)
def T3 : BitVec 128 := rev_elems 128 8 0x5bc94fbc3221a5db94fae95ae7121a47#128 (by decide) (by decide)
example : GCM_AE_128 K3 IV3 P3 A3 128 = (C3, T3) := by native_decide
example : GCM_AD_128 K3 IV3 C3 A3 T3 = P3 := by native_decide

-- Test Vector 4

def K4 : BitVec 128 := rev_elems 128 8 0xfeffe9928665731c6d6a8f9467308308#128 (by decide) (by decide)
def IV4 : BitVec 64 := 0xcafebabefacedbad#64
def P4 : BitVec 480 := rev_elems 480 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480 (by decide) (by decide)
def A4 : BitVec 160 := rev_elems 160 8 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160 (by decide) (by decide)
def C4 : BitVec 480 := rev_elems 480 8 0x61353b4c2806934a777ff51fa22a4755699b2a714fcdc6f83766e5f97b6c742373806900e49f24b22b097544d4896b424989b5e1ebac0f07c23f4598#480 (by decide) (by decide)
def T4 : BitVec 128 := rev_elems 128 8 0x3612d2e79e3b0785561be14aaca2fccb#128 (by decide) (by decide)
example : GCM_AE_128 K4 IV4 P4 A4 128 = (C4, T4) := by native_decide
example : GCM_AD_128 K4 IV4 C4 A4 T4 = P4 := by native_decide

-- Test Vector 5

def K5 : BitVec 128 := rev_elems 128 8 0xfeffe9928665731c6d6a8f9467308308#128 (by decide) (by decide)
def IV5 : BitVec 480 := 0x9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b#480
def P5 : BitVec 480 := rev_elems 480 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480 (by decide) (by decide)
def A5 : BitVec 160 := rev_elems 160 8 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160 (by decide) (by decide)
def C5 : BitVec 480 := rev_elems 480 8 0x8ce24998625615b603a033aca13fb894be9112a5c3a211a8ba262a3cca7e2ca701e4a9a4fba43c90ccdcb281d48c7c6fd62875d2aca417034c34aee5#480 (by decide) (by decide)
def T5 : BitVec 128 := rev_elems 128 8 0x619cc5aefffe0bfa462af43c1699d050#128 (by decide) (by decide)
example : GCM_AE_128 K5 IV5 P5 A5 128 = (C5, T5) := by native_decide
example : GCM_AD_128 K5 IV5 C5 A5 T5 = P5 := by native_decide

-- Test Vector 6

def K6 : BitVec 256 := 0
def IV6 : BitVec 96 := 0
def P6 : BitVec 0 := BitVec.nil
def A6 : BitVec 0 := BitVec.nil
def C6 : BitVec 0 := BitVec.nil
def T6 : BitVec 128 := rev_elems 128 8 0x530f8afbc74536b9a963b4f1c4cb738b#128 (by decide) (by decide)
example : GCM_AE_256 K6 IV6 P6 A6 128 = (C6, T6) := by native_decide
example : GCM_AD_256 K6 IV6 C6 A6 T6 = P6 := by native_decide

-- Test Vector 7

def K7 : BitVec 256 := 0
def IV7 : BitVec 96 := 0
def P7 : BitVec 128 := 0
def A7 : BitVec 0 := BitVec.nil
def C7 : BitVec 128 := rev_elems 128 8 0xcea7403d4d606b6e074ec5d3baf39d18#128 (by decide) (by decide)
def T7 : BitVec 128 := rev_elems 128 8 0xd0d1c8a799996bf0265b98b5d48ab919#128 (by decide) (by decide)
example : GCM_AE_256 K7 IV7 P7 A7 128 = (C7, T7) := by native_decide
example : GCM_AD_256 K7 IV7 C7 A7 T7 = P7 := by native_decide

-- Test Vector 8

def K8 : BitVec 256 := rev_elems 256 8 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256 (by decide) (by decide)
def IV8 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P8 : BitVec 512 := rev_elems 512 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255#512 (by decide) (by decide)
def A8 : BitVec 0 := BitVec.nil
def C8 : BitVec 512 := rev_elems 512 8 0x522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad#512 (by decide) (by decide)
def T8 : BitVec 128 := rev_elems 128 8 0xb094dac5d93471bdec1a502270e3cc6c#128 (by decide) (by decide)
example : GCM_AE_256 K8 IV8 P8 A8 128 = (C8, T8) := by native_decide
example : GCM_AD_256 K8 IV8 C8 A8 T8 = P8 := by native_decide

-- Test Vector 9

def K9 : BitVec 256 := rev_elems 256 8 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256 (by decide) (by decide)
def IV9 : BitVec 96 := 0xcafebabefacedbaddecaf888#96
def P9 : BitVec 480 := rev_elems 480 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480 (by decide) (by decide)
def A9 : BitVec 160 := rev_elems 160 8 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160 (by decide) (by decide)
def C9 : BitVec 480 := rev_elems 480 8 0x522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662#480 (by decide) (by decide)
def T9 : BitVec 128 := rev_elems 128 8 0x76fc6ece0f4e1768cddf8853bb2d551b#128 (by decide) (by decide)
example : GCM_AE_256 K9 IV9 P9 A9 128 = (C9, T9) := by native_decide
example : GCM_AD_256 K9 IV9 C9 A9 T9 = P9 := by native_decide

-- Test Vector 10 (17)

def K10 : BitVec 256 := rev_elems 256 8 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256 (by decide) (by decide)
def IV10 : BitVec 64:= 0xcafebabefacedbad#64
def P10 : BitVec 480 := rev_elems 480 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480 (by decide) (by decide)
def A10 : BitVec 160 := rev_elems 160 8 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160 (by decide) (by decide)
def C10 : BitVec 480 := rev_elems 480 8 0xc3762df1ca787d32ae47c13bf19844cbaf1ae14d0b976afac52ff7d79bba9de0feb582d33934a4f0954cc2363bc73f7862ac430e64abe499f47c9b1f#480 (by decide) (by decide)
def T10 : BitVec 128 := rev_elems 128 8 0x3a337dbf46a792c45e454913fe2ea8f2#128 (by decide) (by decide)
example : GCM_AE_256 K10 IV10 P10 A10 128 = (C10, T10) := by native_decide
example : GCM_AD_256 K10 IV10 C10 A10 T10 = P10 := by native_decide

-- Test Vector 11

def K11 : BitVec 256 := rev_elems 256 8 0xfeffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308#256 (by decide) (by decide)
def IV11 : BitVec 480 := 0x9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b#480
def P11 : BitVec 480 := rev_elems 480 8 0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39#480 (by decide) (by decide)
def A11 : BitVec 160 := rev_elems 160 8 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2#160 (by decide) (by decide)
def C11 : BitVec 480 := rev_elems 480 8 0x5a8def2f0c9e53f1f75d7853659e2a20eeb2b22aafde6419a058ab4f6f746bf40fc0c3b780f244452da3ebf1c5d82cdea2418997200ef82e44ae7e3f#480 (by decide) (by decide)
def T11 : BitVec 128 := rev_elems 128 8 0xa44a8266ee1c8eb0c8b5d4cf5ae9f19a#128 (by decide) (by decide)
example : GCM_AE_256 K11 IV11 P11 A11 128 = (C11, T11) := by native_decide
example : GCM_AD_256 K11 IV11 C11 A11 T11 = P11 := by native_decide

end AES256GCMSpecTest
