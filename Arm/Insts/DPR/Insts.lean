/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPR.Add_sub_carry
import Arm.Insts.DPR.Conditional_select
import Arm.Insts.DPR.Logical_shifted_reg

/-- List of functions to generate random instructions of the
DPR class. -/
def DPR.rand : List (IO (Option (BitVec 32))) :=
  [DPR.Add_sub_carry_cls.rand,
   DPR.Conditional_select_cls.rand,
   DPR.Logical_shifted_reg_cls.rand]
