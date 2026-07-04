/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat
-/
import «Proofs».MultiInsts
import «Proofs».«SHA512».SHA512
import Proofs.«AES-GCM».GCM
-- (v4.30) PARKED — EXCLUDED from the aggregator: `Popcount32`. Its
-- `popcount32_sym_meets_spec` is the scalar `sym_n 27` with a functional value
-- postcondition (`w0 sf = popcount32_spec (w0 s0)`) — the canonical scalar control
-- for the `sym_n`/`sym_aggregate` term-sharing memory regression. It was FLAT at
-- ~1.8 GB through v4.29 (the regression was SIMD-specific from v4.27), but at v4.30
-- the regression WIDENS to scalar proofs: this file OOM-kills at ~42 GB (exit 137,
-- 129 s, isolated single-threaded 40 G cap) — a pure toolchain regression (proof body
-- byte-identical to v4.29). This is the release the reference branch attributed to
-- v4.31; it arrives one version EARLY at v4.30. The real fix is tactic-level (let-bind
-- field values in `AxEffects.update_w` so the value conjuncts share one bound write
-- tower). See memory note `v431-symn-oom-widespread`. Full body at tag `port-v4.29.0`.
-- Re-enable once the sym sharing regression is fixed at the tactic level.
-- import Proofs.Popcount32

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
