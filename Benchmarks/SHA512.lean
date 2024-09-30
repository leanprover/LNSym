/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Proofs.SHA512.SHA512StepLemmas

/-!
### Symbolic Simulation for SHA512
This file sets up the basic shape of a simulation of SHA512
for a set number of instructions
-/

namespace Benchmarks

def SHA512Bench (nSteps : Nat) : Prop :=
  ∀ (s0 sf : ArmState)
    (_h_s0_num_blocks : r (.GPR 2#5) s0 = 10)
    (_h_s0_pc : read_pc s0 = 0x1264c0#64)
    (_h_s0_err : read_err s0 = StateError.None)
    (_h_s0_sp_aligned : CheckSPAlignment s0)
    (_h_s0_program : s0.program = SHA512.program)
    (_h_run : sf = run nSteps s0),
    r StateField.ERR sf = StateError.None
    ∧ r (.GPR 2#5) sf = BitVec.ofNat _ (9 - (nSteps / 485))
