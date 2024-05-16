/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

-- RET

import Arm.Decode
import Arm.Memory
import Arm.Insts.Common
import Arm.BitVec

namespace BR

open BitVec

-- (FIXME) Extend Cfg.addToGraphs when more instructions in this
-- category are implemented.
@[state_simp_rules]
def exec_uncond_branch_reg (inst : Uncond_branch_reg_cls) (s : ArmState) : ArmState :=
    -- Only RET is implemented.
    if not (inst.opc == 0b0010#4 && inst.op2 = 0b11111#5 && 
            inst.op3 = 0b000000#6 && inst.op4 = 0b00000#5) then
       write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
    else
      let target := read_gpr 64 inst.Rn s
      -- State Updates
      let s := write_pc target s
      s

end BR
