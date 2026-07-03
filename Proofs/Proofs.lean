/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat
-/
import «Proofs».MultiInsts
import «Proofs».«SHA512».SHA512
import Proofs.«AES-GCM».GCM
import Proofs.Popcount32

-- /- Experiments we use to test proof strategies and automation ideas. -/
import Proofs.Experiments.Summary1
import Proofs.Experiments.MemoryAliasing
import Proofs.Experiments.SHA512MemoryAliasing
import Proofs.Experiments.Max.MaxTandem
import Proofs.Experiments.Abs.Abs
import Proofs.Experiments.Abs.AbsVCG
-- (v4.23) EXCLUDED from the aggregator: `AbsVCGTandem`, `AddLoop`, `AddLoopTandem`.
-- Their per-cutpoint `stepi_*_cut` and `partial_correctness`/`correctness` goals
-- unfold `run`/`cut`/`Spec'.assert` through the `Spec'` `extends` typeclass
-- projection; at v4.23 `simp`'s nested `whnf`/`isDefEq` does NOT converge — the
-- inner `whnf` times out at the (default 200000) heartbeat limit REGARDLESS of any
-- `set_option maxHeartbeats` (verified: a per-theorem `maxHeartbeats 4000000` still
-- reports the 200000 limit and times out — genuine non-termination, not a budget
-- shortfall). This is the reference branch's v4.26 `Spec'`-`extends` regression
-- landing early at v4.23. Files are left INTACT (NOT sorry'd); the real fix is
-- restructuring Correctness/Spec' away from `extends`. Re-enable once addressed.
-- import Proofs.Experiments.Abs.AbsVCGTandem
-- import Proofs.Experiments.AddLoop.AddLoop
-- import Proofs.Experiments.AddLoop.AddLoopTandem
import Proofs.Experiments.Memcpy.MemCpyVCG
