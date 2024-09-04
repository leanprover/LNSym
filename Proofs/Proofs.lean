/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat
-/
import «Proofs».MultiInsts
import «Proofs».«SHA512».SHA512
import Proofs.«AES-GCM».GCM
import Proofs.Popcount32

/- Experiments we use to test proof strategies and automation ideas. -/
import Proofs.Experiments.Summary1
import Proofs.Experiments.MemoryAliasing
import Proofs.Experiments.SHA512MemoryAliasing
import Proofs.Experiments.Max.MaxTandem
import Proofs.Experiments.Abs.Abs
import Proofs.Experiments.Abs.AbsVCG
import Proofs.Experiments.Abs.AbsVCGTandem
import Proofs.Experiments.AddLoop.AddLoop
import Proofs.Experiments.AddLoop.AddLoopTandem
import Proofs.Experiments.MemCpyVCG
