/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Tests.«AES-GCM».GCMInitV8Program
import Tactics.StepThms

namespace GCMInitV8Program

set_option maxHeartbeats 1000000 in
#genStepEqTheorems gcm_init_v8_program

end GCMInitV8Program
