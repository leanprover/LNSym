/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Tests.«AES-GCM».AESGCMEncKernelProgram
import Tactics.Sym
import Tactics.StepThms
import Correctness.ArmSpec

namespace AESGCMEncKernelProgram

set_option maxHeartbeats 2000000 in
#genStepEqTheorems aes_gcm_enc_kernel_program

end AESGCMEncKernelProgram
