/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Nevine Ebeid
-/
-- EOR3

import Arm.Decode
import Arm.State
import Arm.Insts.Common
import Arm.BitVec
import Arm.Insts.CosimM

----------------------------------------------------------------------

namespace DPSFP

open BitVec

@[lnsimp, state_simp_rules]
def exec_crypto_four_reg (inst : Crypto_four_reg_cls) (s : ArmState) : ArmState :=
  -- This function assumes IsFeatureImplemented(FEAT_SHA3) is true
  -- and that AArch64.CheckFPAdvSIMDEnabled() returns successfully
  if inst.Op0 ≠ 0b00#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 128
    let opdm := read_sfp datasize inst.Rm s
    let opdn := read_sfp datasize inst.Rn s
    let opda := read_sfp datasize inst.Ra s
    let result := opdm ^^^ opdn ^^^ opda
    let s := write_sfp datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

----------------------------------------------------------------------

def Crypto_four_reg_cls.eor3.rand : Cosim.CosimM (Option (BitVec 32)) := do
  if ← Cosim.sha3? then
    -- SHA3 feature supported.
    let (inst : Crypto_four_reg_cls) :=
      { Op0    := ← pure 0b00#2,
        Rm     := ← BitVec.rand 5,
        Rn     := ← BitVec.rand 5,
        Ra     := ← BitVec.rand 5,
        Rd     := ← BitVec.rand 5 }
    pure (some inst.toBitVec32)
  else
    pure none

/-- Generate random instructions of Crypto_four_reg_cls class. -/
def Crypto_four_reg_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [Crypto_four_reg_cls.eor3.rand]


end DPSFP
