/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- This module serves as the root of the `Tactics` library.
-- Import modules here that should be built as part of the library.
import «Tactics».Sym
import «Tactics».StepThms
import «Tactics».Rename
import «Tactics».Name
import «Tactics».ClearNamed
-- NOTE: `Tactics/ArmConstr.lean` was never committed to `main` (the import line was
-- added by #246 but the file was not), so importing it breaks a fresh `make all`.
-- The reflection types `prune_updates` relies on live in `Tactics/PruneUpdatesLogic.lean`
-- (`namespace ArmConstr` there); the missing module is a separate experimental/generated
-- test file that survives only on the `aggr_dsl*` branches in a divergent organization.
-- Dropping the dangling import restores a green build; recovering the experimental
-- module is tracked separately.
-- import «Tactics».ArmConstr
