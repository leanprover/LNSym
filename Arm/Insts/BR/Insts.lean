/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.BR.Compare_branch
import Arm.Insts.BR.Uncond_branch_imm
import Arm.Insts.BR.Uncond_branch_reg
import Arm.Insts.BR.Cond_branch_imm
import Arm.Insts.BR.Hints

/-- List of functions to generate random instructions of the
BR class. -/
def BR.rand : List (IO (Option (BitVec 32))) :=
  [ BR.Hints_cls.rand ]
