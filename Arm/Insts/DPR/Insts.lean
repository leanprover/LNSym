/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPR.Add_sub_carry
import Arm.Insts.DPR.Add_sub_shifted_reg
import Arm.Insts.DPR.Conditional_select
import Arm.Insts.DPR.Data_processing_one_source
import Arm.Insts.DPR.Data_processing_two_source
import Arm.Insts.DPR.Logical_shifted_reg

/-- List of functions to generate random instructions of the
DPR class. -/
def DPR.rand : List (IO (Option (BitVec 32))) :=
  [DPR.Add_sub_carry_cls.rand,
   DPR.Add_sub_shifted_reg_cls.rand,
   DPR.Conditional_select_cls.rand,
   DPR.Data_processing_one_source_cls.rand,
   DPR.Logical_shifted_reg_cls.rand] ++
  DPR.Data_processing_two_source_cls.rand
