/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

-- B, BL

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

namespace BR

open BitVec

@[simp]
def Uncond_branch_imm_inst.branch_taken_pc (inst : Uncond_branch_imm_inst) (pc : BitVec 64) : BitVec 64 :=
  let offset := signExtend 64 (inst.imm26 <<< 2)
  pc + offset

@[simp]
def exec_uncond_branch_imm (inst : Uncond_branch_imm_inst) (s : ArmState) : ArmState :=
    let orig_pc := read_pc s
    let next_pc := Uncond_branch_imm_inst.branch_taken_pc inst orig_pc
    -- State Updates
    let s := if inst.op = 0#1 then
               -- B
               s
             else
               -- BL
               write_gpr 64 30#5 (orig_pc + 4#64) s
    let s := write_pc next_pc s
    s

end BR
