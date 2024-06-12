/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPI.Add_sub_imm
import Arm.Insts.DPI.PC_rel_addressing
import Arm.Insts.DPI.Logical_imm
import Arm.Insts.DPI.Bitfield
import Arm.Insts.DPI.Move_wide_imm

/-- List of functions to generate random instructions of the
DPI class. -/
def DPI.rand : List (IO (Option (BitVec 32))) :=
  DPI.Add_sub_imm_cls.rand ++
  DPI.Logical_imm_cls.rand ++
  DPI.Bitfield_cls.rand ++
  DPI.Move_wide_imm_cls.rand
