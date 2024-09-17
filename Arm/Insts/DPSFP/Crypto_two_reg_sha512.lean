/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- SHA512SU0

import Arm.Decode
import Arm.Insts.Common
import Specs.SHA512Common
import Arm.Insts.CosimM

----------------------------------------------------------------------

namespace DPSFP

open BitVec

def sha512su0 (x : BitVec 128) (w : BitVec 128)
  : BitVec 128 :=
  open sha512_helpers in
  let w_127_64    := extractLsb 127 64 w
  let w_63_0      := extractLsb 63 0 w
  let sig0        := sigma_0 w_127_64
  let x_63_0      := extractLsb 63 0 x
  let vtmp_63_0   := w_63_0 + sig0
  let sig0        := sigma_0 x_63_0
  let vtmp_127_64 := w_127_64 + sig0
  let result      := vtmp_127_64 ++ vtmp_63_0
  result

@[lnsimp, state_simp_rules]
def exec_crypto_two_reg_sha512
  (inst : Crypto_two_reg_sha512_cls) (s : ArmState) : ArmState :=
  open BitVec in
  let x := read_sfp 128 inst.Rn s
  let w := read_sfp 128 inst.Rd s
  let result :=
    match inst.opcode with
    | 0b00#2 => some (sha512su0 x w)
    | _ => none
  -- State Updates
  if result.isNone then
    write_err
      (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!")
    s
  else
    let s' := write_pc ((read_pc s) + 4#64) s
    let s' := write_sfp 128 inst.Rd result.get! s'
    s'

----------------------------------------------------------------------

def Crypto_two_reg_sha512_cls.sha512su0.rand : Cosim.CosimM (Option (BitVec 32)) := do
  if ← Cosim.sha512? then
    -- SHA512 feature supported.
    let (inst : Crypto_two_reg_sha512_cls) :=
      { opcode := ← pure 0b00#2,
        Rn     := ← BitVec.rand 5,
        Rd     := ← BitVec.rand 5 }
    pure (some inst.toBitVec32)
  else
    pure none

/-- Generate random instructions of Crypto_two_reg_sha512_cls class. -/
def Crypto_two_reg_sha512_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [Crypto_two_reg_sha512_cls.sha512su0.rand]

end DPSFP
