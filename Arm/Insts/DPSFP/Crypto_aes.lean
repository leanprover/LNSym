/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
-- AESE, AESMC

import Arm.Decode
import Arm.Insts.Common
import Specs.AESCommon

----------------------------------------------------------------------

namespace DPSFP

open BitVec

@[state_simp_rules]
def exec_aese
  (inst : Crypto_aes_cls) (s : ArmState) : ArmState :=
  -- Assumes IsFeatureImplemented(FEAT_AES)
  -- AArch64.CheckFPAdvSIMDEnabled();
  let operand1 := read_sfp 128 inst.Rd s
  let operand2 := read_sfp 128 inst.Rn s
  let result := operand1 ^^^ operand2
  let result := AESCommon.SubBytes $ AESCommon.ShiftRows result
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
  BitVec.cast (by omega) $ extractLsb hi lo $ BitVec.flatten FFmul_02

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
  BitVec.cast (by omega) $ extractLsb hi lo $ BitVec.flatten FFmul_03

def AESMixColumns (op : BitVec 128) : BitVec 128 :=
  AESCommon.MixColumns op FFmul02 FFmul03

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
