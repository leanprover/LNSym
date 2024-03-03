/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- ADR, ADRP

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

namespace DPI

open BitVec

@[state_simp_rules]
def exec_pc_rel_addressing (inst : PC_rel_addressing_cls) (s : ArmState) : ArmState :=
  let orig_pc := read_pc s
  let imm := if inst.op = 0#1 then
                signExtend 64 (inst.immhi ++ inst.immlo) -- ADR
             else
                signExtend 64 ((inst.immhi ++ inst.immlo) <<< 12) -- ADRP
  let result := if inst.op = 0#1 then
                   orig_pc + imm -- ADR
                else
                   (BitVec.partInstall 11 0 0#12 orig_pc) + imm
  -- State Updates
  let s := write_gpr_zr 64 inst.Rd result s
  let s := write_pc (orig_pc + 4#64) s
  s

end DPI
