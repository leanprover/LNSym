/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/

-- B.cond

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

namespace BR

open BitVec

@[state_simp_rules]
def Cond_branch_imm_inst.branch_taken_pc
  (inst : Cond_branch_imm_inst) (pc : BitVec 64) : BitVec 64 :=
  let offset := signExtend 64 (inst.imm19 <<< 2)
  pc + offset

@[state_simp_rules]
def Cond_branch_imm_inst.condition_holds
  (inst : Cond_branch_imm_inst) (s : ArmState) : Bool :=
  let Z := read_flag PFlag.Z s
  let C := read_flag PFlag.C s
  let N := read_flag PFlag.N s
  let V := read_flag PFlag.V s
  let result :=
    match (extractLsb 3 1 inst.cond) with
    | 0b000#3 => Z == 1#1
    | 0b001#3 => C == 1#1
    | 0b010#3 => N == 1#1
    | 0b011#3 => V == 1#1
    | 0b100#3 => C == 1#1 && Z == 0#1
    | 0b101#3 => N == V
    | 0b110#3 => N == V && Z == 0#1
    | 0b111#3 => true
  let result :=
    if extractLsb 0 0 inst.cond == 1#1 && inst.cond != 0b1111#4
    then !result
    else result
  result

@[state_simp_rules]
def exec_cond_branch_imm (inst : Cond_branch_imm_inst) (s : ArmState)
  : ArmState :=
  let orig_pc := read_pc s
  let next_pc := Cond_branch_imm_inst.branch_taken_pc inst orig_pc
  -- State Updates
  let s :=
    if Cond_branch_imm_inst.condition_holds inst s
    then write_pc next_pc s
    else s
  s

end BR
