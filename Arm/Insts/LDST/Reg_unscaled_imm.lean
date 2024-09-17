/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- LDUR, STUR (SIMD&FP)

import Arm.Decode
import Arm.Insts.Common

----------------------------------------------------------------------

namespace LDST

open BitVec

@[lnsimp, state_simp_rules]
def exec_ldstur
  (inst : Reg_unscaled_imm_cls) (s : ArmState) : ArmState :=
  let scale := (extractLsb 1 1 inst.opc ++ inst.size).toNat
  if scale > 4 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let offset := signExtend 64 inst.imm9
    let memop := if getLsbD inst.opc 0 then MemOp.MemOp_LOAD else MemOp.MemOp_STORE
    let datasize := 8 <<< scale
    let address := read_gpr 64 inst.Rn s
    if inst.Rn = 31#5 ∧ ¬(CheckSPAlignment s) then
      write_err (StateError.Fault s!"[Inst: {inst}] SP {address} is not aligned!") s
    else
      let address := address + offset
      -- State Updates
      let s := if memop = MemOp.MemOp_STORE then
                 have h : datasize = datasize / 8 * 8 := by omega
                 let data := read_sfp datasize inst.Rt s
                 write_mem_bytes (datasize / 8) address (BitVec.cast h data) s
               else
                 have h : datasize / 8 * 8 = datasize := by omega
                 let data := read_mem_bytes (datasize / 8) address s
                 write_sfp datasize inst.Rt (BitVec.cast h data) s
      let s := write_pc ((read_pc s) + 4#64) s
      s

@[lnsimp, state_simp_rules]
def exec_reg_unscaled_imm
  (inst : Reg_unscaled_imm_cls) (s : ArmState) : ArmState :=
  if inst.VR = 0b1#1 then
    exec_ldstur inst s
  else
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

end LDST
