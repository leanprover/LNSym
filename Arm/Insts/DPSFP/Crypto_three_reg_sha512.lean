/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- SHA512H, SHA512H2, SHA512SU1

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec
import Specs.SHA512Common

----------------------------------------------------------------------

namespace DPSFP

open BitVec

def sha512h (x : BitVec 128) (y : BitVec 128) (w : BitVec 128)
  : BitVec 128 :=
  open sha512_helpers in
  let y_127_64    := extractLsb 127 64 y
  let y_63_0      := extractLsb 63 0 y
  let msigma1     := sigma_big_1 y_127_64
  let x_63_0      := extractLsb 63 0 x
  let x_127_64    := extractLsb 127 64 x
  let vtmp_127_64 := ch y_127_64 x_63_0 x_127_64
  let w_127_64    := extractLsb 127 64 w
  let w_63_0      := extractLsb 63 0 w
  let vtmp_127_64 := vtmp_127_64 + msigma1 + w_127_64
  let tmp         := vtmp_127_64 + y_63_0
  let msigma1     := sigma_big_1 tmp
  let vtmp_63_0   := ch tmp y_127_64 x_63_0
  let vtmp_63_0   := vtmp_63_0 + msigma1 + w_63_0
  let result      := vtmp_127_64 ++ vtmp_63_0
  result

def sha512h2 (x : BitVec 128) (y : BitVec 128) (w : BitVec 128) :
    BitVec 128 :=
    open sha512_helpers in
    let y_63_0      := extractLsb 63 0 y
    let y_127_64    := extractLsb 127 64 y
    let nsigma0     := sigma_big_0 y_63_0
    let x_63_0      := extractLsb 63 0 x
    let vtmp_127_64 := maj x_63_0 y_127_64 y_63_0
    let w_127_64    := extractLsb 127 64 w
    let vtmp_127_64 := vtmp_127_64 + nsigma0 + w_127_64
    let nsigma0     := sigma_big_0 vtmp_127_64
    let vtmp_63_0   := maj vtmp_127_64 y_63_0 y_127_64
    let w_63_0      := extractLsb 63 0 w
    let vtmp_63_0   := vtmp_63_0 + nsigma0 + w_63_0
    let result      := vtmp_127_64 ++ vtmp_63_0
    result

def sha512su1 (x : BitVec 128) (y : BitVec 128) (w : BitVec 128)
  : BitVec 128 :=
  open sha512_helpers in
  let x_127_64    := extractLsb 127 64 x
  let sig1        := sigma_1 x_127_64
  let w_127_64    := extractLsb 127 64 w
  let y_127_64    := extractLsb 127 64 y
  let vtmp_127_64 := w_127_64 + sig1 + y_127_64
  let x_63_0      := extractLsb 63 0 x
  let sig1        := sigma_1 x_63_0
  let w_63_0      := extractLsb 63 0 w
  let y_63_0      := extractLsb 63 0 y
  let vtmp_63_0   := w_63_0 + sig1 + y_63_0
  let result      := vtmp_127_64 ++ vtmp_63_0
  result

@[state_simp_rules]
def exec_crypto_three_reg_sha512
  (inst : Crypto_three_reg_sha512_cls) (s : ArmState) : ArmState :=
  open BitVec in
  let x := read_sfp 128 inst.Rn s
  let y := read_sfp 128 inst.Rm s
  let w := read_sfp 128 inst.Rd s
  let result :=
    match inst.O, inst.opcode with
    | 0b0#1, 0b00#2 => some (sha512h x y w)
    | 0b0#1, 0b01#2 => some (sha512h2 x y w)
    | 0b0#1, 0b10#2 => some (sha512su1 x y w)
    | _, _ => none
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

def Crypto_three_reg_sha512_cls.sha512.rand : IO (Option (BitVec 32)) := do
  let feat_check ←
      IO.Process.output
      { cmd  := "Arm/Insts/Cosim/platform_check.sh",
        args := #["-f", "sha512"] }
  if feat_check.exitCode == 0 then
    let (inst : Crypto_three_reg_sha512_cls) :=
      { Rm     := ← BitVec.rand 5,
        O      := ← pure 0b0#1,
        opcode := ← BitVec.rand 2 (lo := 0) (hi := 0b10),
        Rn     := ← BitVec.rand 5,
        Rd     := ← BitVec.rand 5 }
    pure (some inst.toBitVec32)
  else
    pure none

/-- Generate random instructions of Crypto_three_reg_sha512_cls class. -/
def Crypto_three_reg_sha512_cls.rand : List (IO (Option (BitVec 32))) :=
  [Crypto_three_reg_sha512_cls.sha512.rand]


end DPSFP
