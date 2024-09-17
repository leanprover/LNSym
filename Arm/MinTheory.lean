import Arm.Attr

-- These lemmas are from lean/Init/SimpLemmas.lean.
attribute [lnsimp, minimal_theory] eq_self
attribute [lnsimp, minimal_theory] ne_eq
attribute [lnsimp, minimal_theory] ite_true
attribute [lnsimp, minimal_theory] ite_false
attribute [lnsimp, minimal_theory] dite_true
attribute [lnsimp, minimal_theory] dite_false
attribute [lnsimp, minimal_theory] ite_self

/-
Notice how both `and_true : ?p ∧ True = ?p` and `and_self : ?p ∧ ?p = ?p` may
be attempted by `simp` on a goal of the shape `_ ∧ True`, as they are both
a match where the discrimination tree is concerned.

However, assuming the left conjunct is not def-eq to `True`, an attempt of
`and_self` will fail to unify, which causes a fallback to `and_true`.
For the latter simp lemma, on the other hand, we know that if the discrimination
tree gives a match, then the lemma should be applicable.
This is because the variable `?p` is used only once in the pattern (i.e.,
the pattern is linear), and the first unification of an unassigned metavariable
is always successful.

Another possibly expensive lemma is
  `and_iff_left_of_imp : {a b : Prop} (ha : a → b) : a ∧ b ↔ a`
The pattern of this lemma (`?a ∧ ?b`) is perfectly linear, but to apply such
a lemma, `simp` first has to discharge the `(ha : a → b)` side-condition,
which might fail and might be expensive.

Thus, the rationale we follow is that only linear, side-condition free lemmas
get the `high` priority, and everything else gets the default prioriry.
This ensures that `and_true` gets tried before `and_self` or
`and_iff_left_of_imp` -/
attribute [lnsimp high, minimal_theory high] and_true
attribute [lnsimp high, minimal_theory high] true_and
attribute [lnsimp high, minimal_theory high] and_false
attribute [lnsimp high, minimal_theory high] false_and
attribute [lnsimp, minimal_theory] and_self
attribute [lnsimp, minimal_theory] and_not_self
attribute [lnsimp, minimal_theory] not_and_self
attribute [lnsimp, minimal_theory] and_imp
attribute [lnsimp high, minimal_theory high] not_and
attribute [lnsimp, minimal_theory] or_self
attribute [lnsimp high, minimal_theory high] or_true
attribute [lnsimp high, minimal_theory high] true_or
attribute [lnsimp high, minimal_theory high] or_false
attribute [lnsimp high, minimal_theory high] false_or
attribute [lnsimp high, minimal_theory high] if_true_left
attribute [lnsimp high, minimal_theory high] if_true_right
attribute [lnsimp high, minimal_theory high] if_false_left
attribute [lnsimp high, minimal_theory high] if_false_right
attribute [lnsimp, minimal_theory] iff_self
attribute [lnsimp high, minimal_theory high] iff_true
attribute [lnsimp high, minimal_theory high] true_iff
attribute [lnsimp high, minimal_theory high] iff_false
attribute [lnsimp high, minimal_theory high] false_iff
attribute [lnsimp high, minimal_theory high] eq_iff_iff
attribute [lnsimp high, minimal_theory high] false_implies
attribute [lnsimp high, minimal_theory high] implies_true
attribute [lnsimp high, minimal_theory high] true_implies
attribute [lnsimp high, minimal_theory high] not_false_eq_true
attribute [lnsimp high, minimal_theory high] not_true_eq_false
attribute [lnsimp, minimal_theory] not_iff_self
attribute [lnsimp, minimal_theory] and_self_left
attribute [lnsimp, minimal_theory] and_self_right
attribute [lnsimp, minimal_theory] and_congr_right_iff
attribute [lnsimp, minimal_theory] and_congr_left_iff
attribute [lnsimp, minimal_theory] and_iff_left_iff_imp
attribute [lnsimp, minimal_theory] and_iff_right_iff_imp
attribute [lnsimp, minimal_theory] iff_self_and
attribute [lnsimp, minimal_theory] iff_and_self
attribute [lnsimp, minimal_theory] or_self_left
attribute [lnsimp, minimal_theory] or_self_right
attribute [lnsimp, minimal_theory] or_iff_right_of_imp
attribute [lnsimp, minimal_theory] or_iff_left_of_imp
attribute [lnsimp, minimal_theory] or_iff_left_iff_imp
attribute [lnsimp, minimal_theory] or_iff_right_iff_imp

attribute [lnsimp high, minimal_theory high] Bool.or_false
attribute [lnsimp high, minimal_theory high] Bool.or_true
attribute [lnsimp high, minimal_theory high] Bool.false_or
attribute [lnsimp high, minimal_theory high] Bool.false_eq_true
attribute [lnsimp high, minimal_theory high] Bool.true_or
attribute [lnsimp, minimal_theory] Bool.or_self
attribute [lnsimp high, minimal_theory high] Bool.or_eq_true
attribute [lnsimp high, minimal_theory high] Bool.and_false
attribute [lnsimp high, minimal_theory high] Bool.and_true
attribute [lnsimp high, minimal_theory high] Bool.false_and
attribute [lnsimp high, minimal_theory high] Bool.true_and
attribute [lnsimp, minimal_theory] Bool.and_self
attribute [lnsimp high, minimal_theory high] Bool.and_eq_true
attribute [lnsimp high, minimal_theory high] Bool.not_not
attribute [lnsimp high, minimal_theory high] Bool.not_true
attribute [lnsimp high, minimal_theory high] Bool.not_false
attribute [lnsimp high, minimal_theory high] beq_true
attribute [lnsimp high, minimal_theory high] beq_false
attribute [lnsimp high, minimal_theory high] Bool.not_eq_true'
attribute [lnsimp high, minimal_theory high] Bool.not_eq_false'
attribute [lnsimp high, minimal_theory high] Bool.beq_to_eq
attribute [lnsimp high, minimal_theory high] Bool.not_beq_to_not_eq
attribute [lnsimp high, minimal_theory high] Bool.not_eq_true
attribute [lnsimp high, minimal_theory high] Bool.not_eq_false
attribute [lnsimp high, minimal_theory high] decide_eq_true_eq
attribute [lnsimp high, minimal_theory high] decide_not
attribute [lnsimp high, minimal_theory high] not_decide_eq_true

-- NOTE: `heq_eq_eq` might look linear, but if we consider implicit variables,
-- the pattern is `@HEq ?α ?a ?α ?b`; `?α` is used non-linearly
attribute [lnsimp, minimal_theory] heq_eq_eq

attribute [lnsimp high, minimal_theory high] cond_true
attribute [lnsimp high, minimal_theory high] cond_false
attribute [lnsimp, minimal_theory] beq_self_eq_true
attribute [lnsimp, minimal_theory] beq_self_eq_true'
attribute [lnsimp, minimal_theory] bne_self_eq_false
attribute [lnsimp, minimal_theory] bne_self_eq_false'
attribute [lnsimp high, minimal_theory high] decide_False
attribute [lnsimp high, minimal_theory high] decide_True
attribute [lnsimp high, minimal_theory high] decide_eq_false_iff_not
attribute [lnsimp high, minimal_theory high] decide_eq_true_iff
attribute [lnsimp high, minimal_theory high] bne_iff_ne
attribute [lnsimp high, minimal_theory high] Bool.false_eq
attribute [lnsimp high, minimal_theory high] Bool.and_eq_false_imp

attribute [lnsimp high, minimal_theory high] Decidable.not_not

attribute [lnsimp high, minimal_theory high] Nat.le_zero_eq
attribute [lnsimp high, minimal_theory high] Nat.zero_add
attribute [lnsimp high, minimal_theory high] Nat.zero_eq
attribute [lnsimp high, minimal_theory high] Nat.succ.injEq
attribute [lnsimp high, minimal_theory high] Nat.succ_ne_zero
attribute [lnsimp high, minimal_theory high] Nat.sub_zero

attribute [lnsimp, minimal_theory] Nat.le_refl

@[lnsimp, minimal_theory]
theorem option_get_bang_of_some [Inhabited α] (v : α) :
  Option.get! (some v) = v := by rfl
attribute [lnsimp, minimal_theory] Option.isNone_some

attribute [lnsimp, minimal_theory] Fin.isValue
attribute [lnsimp high, minimal_theory high] Fin.zero_eta
attribute [lnsimp high, minimal_theory high] Fin.mk.injEq

-- attribute [lnsimp, minimal_theory] ↓reduceIte
attribute [lnsimp, minimal_theory] reduceCtorEq
