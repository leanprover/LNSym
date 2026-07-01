/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Proofs.SHA512.SHA512_block_armv8_rules
import Proofs.SHA512.SHA512Sym
-- PARKED at v4.15 (toolchain-stepping): `SHA512BlockSym`'s `sha512_loop_sym`
-- (485-step `sym_block`, byte-identical to `main`) elaborates fine but the v4.15
-- kernel takes ~30+ min to type-check the resulting very large proof term (CPU-bound,
-- ~1.1GB, NOT an OOM — distinct from the v4.31 sym_n memory blowup). It still builds
-- standalone with `set_option maxHeartbeats 0` (kept in the file); it is excluded from
-- this aggregator only so per-version builds stay fast. The reference branch ran it
-- with `maxHeartbeats 0` at v4.21 and parked it outright at v4.31.
-- Re-enable once the sym_n kernel-cost regression is addressed. Verify standalone:
--   LEAN_NUM_THREADS=4 ~/bin/lakeb Proofs.SHA512.SHA512BlockSym
-- import Proofs.SHA512.SHA512BlockSym
