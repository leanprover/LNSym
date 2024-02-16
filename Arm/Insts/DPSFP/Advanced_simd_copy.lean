/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Yan Peng
-/
-- DUP, INS, SMOV, UMOV

import Arm.Decode
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open Std.BitVec

@[simp]
def exec_advanced_simd_copy
  (inst : Advanced_simd_copy_cls) (s : ArmState) : ArmState :=
  sorry
  

----------------------------------------------------------------------

/-- Generate random instructions of Advanced_simd_copy class. -/
def Advanced_simd_copy_cls.rand : List (IO (Option (BitVec 32))) :=
  []

end DPSFP
