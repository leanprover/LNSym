/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPI.Add_sub_imm
import Arm.Insts.DPI.PC_rel_addressing
import Arm.Insts.DPI.Logical_imm

/-- List of functions to generate random instructions of the
DPI class. -/
def DPI.rand : List (IO (Option (BitVec 32))) :=
  [ DPI.Add_sub_imm_cls.rand,
    DPI.Logical_imm_cls.rand ]
