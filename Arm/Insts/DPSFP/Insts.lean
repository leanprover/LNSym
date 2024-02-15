/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Insts.DPSFP.Advanced_simd_two_reg_misc
import Arm.Insts.DPSFP.Advanced_simd_extract
import Arm.Insts.DPSFP.Advanced_simd_three_same
import Arm.Insts.DPSFP.Crypto_aes
import Arm.Insts.DPSFP.Crypto_two_reg_sha512
import Arm.Insts.DPSFP.Crypto_three_reg_sha512
        
/-- List of functions to generate random instructions of the
DPSFP class. -/
def DPSFP.rand : List (IO (Option (BitVec 32))) :=
  DPSFP.Advanced_simd_extract_cls.rand ++
  DPSFP.Advanced_simd_three_same_cls.rand ++
  DPSFP.Advanced_simd_two_reg_misc_cls.rand ++
  DPSFP.Crypto_three_reg_sha512_cls.rand ++
  DPSFP.Crypto_two_reg_sha512_cls.rand
