import Lean

-- A minimal theory, safe for all LNSym proofs
register_simp_attr minimal_theory
-- Non-interference lemmas for simplifying terms involving state
-- accessors and updaters.
register_simp_attr state_simp_rules
-- Rules for bitvector lemmas
register_simp_attr bitvec_rules
-- Rules for memory lemmas
register_simp_attr memory_simp_rules

/-
syntax "state_simp" : tactic
macro_rules
  | `(tactic| state_simp) => `(tactic| simp only [state_simp_rules])

syntax "state_simp?" : tactic
macro_rules
  | `(tactic| state_simp?) => `(tactic| simp? only [state_simp_rules])

syntax "state_simp_all" : tactic
macro_rules
  | `(tactic| state_simp_all) => `(tactic| simp_all only [state_simp_rules])

syntax "state_simp_all?" : tactic
macro_rules
  | `(tactic| state_simp_all?) => `(tactic| simp_all? only [state_simp_rules])
-/
