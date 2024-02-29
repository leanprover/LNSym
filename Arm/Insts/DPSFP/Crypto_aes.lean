/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
-- AESE, AESMC

import Arm.Decode
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open BitVec

def SBox :=
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

def AESShiftRows (op : BitVec 128) : BitVec 128 :=
  extractLsb 95 88 op ++ extractLsb 55 48 op ++
  extractLsb 15 8 op ++ extractLsb 103 96 op ++
  extractLsb 63 56 op ++ extractLsb 23 16 op ++
  extractLsb 111 104 op ++ extractLsb 71 64 op ++
  extractLsb 31 24 op ++ extractLsb 119 112 op ++
  extractLsb 79 72 op ++ extractLsb 39 32 op ++
  extractLsb 127 120 op ++ extractLsb 87 80 op ++
  extractLsb 47 40 op ++ extractLsb 7 0 op

def AESSubBytes_aux (i : Nat) (op : BitVec 128) (out : BitVec 128)
  : BitVec 128 :=
  if h₀ : 16 <= i then
    out
  else
    let idx := (extractLsb (i * 8 + 7) (i * 8) op).toNat
    let val := extractLsb (idx * 8 + 7) (idx * 8) $ BitVec.flatten SBox
    have h₁ : idx * 8 + 7 - idx * 8 = i * 8 + 7 - i * 8 := by omega
    let out := BitVec.partInstall (i * 8 + 7) (i * 8) (h₁ ▸ val) out
    have _ : 15 - i < 16 - i := by omega
    AESSubBytes_aux (i + 1) op out
  termination_by (16 - i)

def AESSubBytes (op : BitVec 128) : BitVec 128 :=
  AESSubBytes_aux 0 op (BitVec.zero 128)

@[state_simp_rules]
def exec_aese
  (inst : Crypto_aes_cls) (s : ArmState) : ArmState :=
  -- Assumes IsFeatureImplemented(FEAT_AES)
  -- AArch64.CheckFPAdvSIMDEnabled();
  let operand1 := read_sfp 128 inst.Rd s
  let operand2 := read_sfp 128 inst.Rn s
  let result := operand1 ^^^ operand2
  let result := AESSubBytes $ AESShiftRows result
  -- State Updates
  let s := write_sfp 128 inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

def FFmul02 (b : BitVec 8) : BitVec 8 :=
  let FFmul_02 :=
    --   F E D C B A 9 8 7 6 5 4 3 2 1 0
    [ 0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB#128, -- F
      0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB#128, -- E
      0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB#128, -- D
      0x858781838D8F898B959791939D9F999B#128, -- C
      0x656761636D6F696B757771737D7F797B#128, -- B
      0x454741434D4F494B555751535D5F595B#128, -- A
      0x252721232D2F292B353731333D3F393B#128, -- 9
      0x050701030D0F090B151711131D1F191B#128, -- 8
      0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0#128, -- 7
      0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0#128, -- 6
      0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0#128, -- 5
      0x9E9C9A98969492908E8C8A8886848280#128, -- 4
      0x7E7C7A78767472706E6C6A6866646260#128, -- 3
      0x5E5C5A58565452504E4C4A4846444240#128, -- 2
      0x3E3C3A38363432302E2C2A2826242220#128, -- 1
      0x1E1C1A18161412100E0C0A0806040200#128  -- 0
    ]
  let lo := b.toNat * 8
  let hi := lo + 7
  have h : hi - lo + 1 = 8 := by omega
  h ▸ extractLsb hi lo $ BitVec.flatten FFmul_02

def FFmul03 (b : BitVec 8) : BitVec 8 :=
  let FFmul_03 :=
    --   F E D C B A 9 8 7 6 5 4 3 2 1 0
    [ 0x1A191C1F16151013020104070E0D080B#128, -- F
      0x2A292C2F26252023323134373E3D383B#128, -- E
      0x7A797C7F76757073626164676E6D686B#128, -- D
      0x4A494C4F46454043525154575E5D585B#128, -- C
      0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB#128, -- B
      0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB#128, -- A
      0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB#128, -- 9
      0x8A898C8F86858083929194979E9D989B#128, -- 8
      0x818287848D8E8B88999A9F9C95969390#128, -- 7
      0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0#128, -- 6
      0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0#128, -- 5
      0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0#128, -- 4
      0x414247444D4E4B48595A5F5C55565350#128, -- 3
      0x717277747D7E7B78696A6F6C65666360#128, -- 2
      0x212227242D2E2B28393A3F3C35363330#128, -- 1
      0x111217141D1E1B18090A0F0C05060300#128  -- 0
    ]
  let lo := b.toNat * 8
  let hi := lo + 7
  have h : hi - lo + 1 = 8 := by omega
  h ▸ extractLsb hi lo $ BitVec.flatten FFmul_03

def AESMixColumns_aux (c : Nat)
  (in0 : BitVec 32) (in1 : BitVec 32) (in2 : BitVec 32) (in3 : BitVec 32)
  (out0 : BitVec 32) (out1 : BitVec 32) (out2 : BitVec 32) (out3 : BitVec 32)
  : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  if h₀ : 4 <= c then
    (out0, out1, out2, out3)
  else
    let lo := c * 8
    let hi := lo + 7
    have h₁ : hi - lo + 1 = 8 := by omega
    let in0_byte := h₁ ▸ extractLsb hi lo in0
    let in1_byte := h₁ ▸ extractLsb hi lo in1
    let in2_byte := h₁ ▸ extractLsb hi lo in2
    let in3_byte := h₁ ▸ extractLsb hi lo in3
    let val0 := h₁.symm ▸ (FFmul02 in0_byte ^^^ FFmul03 in1_byte ^^^ in2_byte ^^^ in3_byte)
    let out0 := BitVec.partInstall hi lo val0 out0
    let val1 := h₁.symm ▸ (FFmul02 in1_byte ^^^ FFmul03 in2_byte ^^^ in3_byte ^^^ in0_byte)
    let out1 := BitVec.partInstall hi lo val1 out1
    let val2 := h₁.symm ▸ (FFmul02 in2_byte ^^^ FFmul03 in3_byte ^^^ in0_byte ^^^ in1_byte)
    let out2 := BitVec.partInstall hi lo val2 out2
    let val3 := h₁.symm ▸ (FFmul02 in3_byte ^^^ FFmul03 in0_byte ^^^ in1_byte ^^^ in2_byte)
    let out3 := BitVec.partInstall hi lo val3 out3
    have _ : 3 - c < 4 - c := by omega
    AESMixColumns_aux (c + 1) in0 in1 in2 in3 out0 out1 out2 out3
  termination_by (4 - c)

def AESMixColumns (op : BitVec 128) : BitVec 128 :=
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
    AESMixColumns_aux 0 in0 in1 in2 in3 out0 out1 out2 out3
  extractLsb 31 24 out3 ++ extractLsb 31 24 out2 ++
  extractLsb 31 24 out1 ++ extractLsb 31 24 out0 ++
  extractLsb 23 16 out3 ++ extractLsb 23 16 out2 ++
  extractLsb 23 16 out1 ++ extractLsb 23 16 out0 ++
  extractLsb 15 8 out3 ++ extractLsb 15 8 out2 ++
  extractLsb 15 8 out1 ++ extractLsb 15 8 out0 ++
  extractLsb 7 0 out3 ++ extractLsb 7 0 out2 ++
  extractLsb 7 0 out1 ++ extractLsb 7 0 out0

@[state_simp_rules]
def exec_aesmc
  (inst : Crypto_aes_cls) (s : ArmState) : ArmState :=
  -- Assumes IsFeatureImplemented(FEAT_AES)
  -- AArch64.CheckFPAdvSIMDEnabled();
  let operand := read_sfp 128 inst.Rn s
  let result := AESMixColumns operand
  -- State Updates
  let s := write_sfp 128 inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_crypto_aes
  (inst : Crypto_aes_cls) (s : ArmState) : ArmState :=
  match inst.size, inst.opcode with
  | 0b00#2, 0b00100#5 => exec_aese inst s
  | 0b00#2, 0b00110#5 => exec_aesmc inst s
  | _, _ => write_err
    (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

----------------------------------------------------------------------

def Crypto_aes_cls.aese.rand : IO (Option (BitVec 32)) := do
  let (inst : Crypto_aes_cls) :=
    { size := 0b00#2,
      opcode := 0b00100#5,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5
    }
  pure (some inst.toBitVec32)

def Crypto_aes_cls.aesmc.rand : IO (Option (BitVec 32)) := do
  let (inst : Crypto_aes_cls) :=
    { size := 0b00#2,
      opcode := 0b00110#5,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5
    }
  pure (some inst.toBitVec32)

/-- Generate random instructions of Crypto_aes_cls class. -/
def Crypto_aes_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Crypto_aes_cls.aese.rand,
    Crypto_aes_cls.aesmc.rand ]

end DPSFP
