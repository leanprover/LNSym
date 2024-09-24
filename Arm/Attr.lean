/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

import Lean

-- A minimal theory, safe for all LNSym proofs
register_simp_attr minimal_theory
-- Non-interference lemmas for simplifying terms involving state
-- accessors and updaters.
register_simp_attr state_simp_rules
-- Rules for bitvector lemmas
register_simp_attr bitvec_rules
-- Rules for memory lemmas
register_simp_attr memory_rules
