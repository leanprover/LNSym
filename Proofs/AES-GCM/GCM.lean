/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Proofs.«AES-GCM».GCMGmultV8Sym
-- (v4.30) PARKED — EXCLUDED from the aggregator: the three remaining AES-GCM
-- symbolic-simulation proofs. They are `sym_n` value/step-postcondition proofs that
-- were green (part of the whole-Proofs build) through v4.29 but OOM-kill at ~42 GB
-- (exit 137, each verified standalone, isolated single-threaded 40 G cap) at v4.30 —
-- the release where the `sym_n`/`sym_aggregate` term-sharing memory regression WIDENS
-- from SIMD-only (v4.27, which parked GCMGmult's `run_27`) to all sym-value proofs
-- (see the Popcount32 park note in `Proofs/Proofs.lean` and memory note
-- `v431-symn-oom-widespread`; the reference branch attributed this to v4.31, it arrives
-- at v4.30). The real fix is tactic-level (let-bind field values in `AxEffects.update_w`
-- so the value conjuncts share one bound write tower). Full bodies at tag `port-v4.29.0`.
--   - GCMInitV8Sym:       `gcm_init_v8_program_correct` (`sym_n 152`)   → 42.1 GB OOM
--   - AESHWEncryptSym:    `aes_hw_encrypt_program_run_60` (~54 steps: sym_n 12 + 6×sym_n 7
--                         at sN; OOMs despite its TRIVIAL `read_err = .None` postcondition —
--                         the `at sN` continuations accumulate)                → 42.0 GB OOM
--   - AESGCMEncKernelSym: `aes_gcm_enc_kernel_program_run_xx` (`sym_n 138`) → 41.8 GB OOM
-- GCMGmultV8Sym above stays imported: its heavy `run_27` proof was already parked at
-- v4.27, so the file itself builds green (~1.4 GB). Re-enable once addressed.
-- import Proofs.«AES-GCM».GCMInitV8Sym
-- import Proofs.«AES-GCM».AESHWEncryptSym
-- import Proofs.«AES-GCM».AESGCMEncKernelSym
