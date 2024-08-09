/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

-- CBZ, CBNZ -- 32 and 64-bit variants

import Arm.Decode
import Arm.State
import Arm.Insts.Common

namespace BR

open BitVec

-- The functions Compare_branch_inst.branch_taken_pc and
-- Compare_branch_inst.condition_holds are also used in control-flow
-- analysis; see Arm/Cfg/Cfg.lean.

@[state_simp_rules]
def Compare_branch_inst.branch_taken_pc (inst : Compare_branch_cls) (pc : BitVec 64) : BitVec 64 :=
  let offset := signExtend 64 (inst.imm19 <<< 2)
  let branch_taken_pc := pc + offset
  branch_taken_pc

@[state_simp_rules]
def Compare_branch_inst.condition_holds (inst : Compare_branch_cls) (s : ArmState) : Bool :=
  let datasize := if inst.sf = 1#1 then 64 else 32
  let operand1 := read_gpr datasize inst.Rt s
  let operand1_is_zero := operand1 = BitVec.zero datasize
  if inst.op = 0#1 then
    -- CBZ
    operand1_is_zero
  else
    -- CBNZ
    (not operand1_is_zero)

@[state_simp_rules]
def exec_compare_branch (inst : Compare_branch_cls) (s : ArmState) : ArmState :=
    let orig_pc := read_pc s
    let branch_taken := Compare_branch_inst.condition_holds inst s
    let next_pc := if branch_taken then
                      (Compare_branch_inst.branch_taken_pc inst orig_pc)
                   else
                     orig_pc + 4#64
    -- State Updates
    let s            := write_pc next_pc s
    s

end BR
