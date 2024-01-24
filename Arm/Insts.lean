/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPI.Insts
import Arm.Insts.DPR.Insts
import Arm.Insts.BR.Insts
import Arm.Insts.DPSFP.Insts
import Arm.Insts.LDST.Insts

def Insts.rand : List (IO (Option (BitVec 32))) :=
  DPI.rand ++
  DPR.rand ++
  DPSFP.rand
