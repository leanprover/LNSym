import Lean

-- Non-interference lemmas for simplifying terms involving state
-- accessors and updaters.
register_simp_attr state_simp_rules

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
