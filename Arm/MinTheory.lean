import Arm.Attr

-- These lemmas are from lean/Init/SimpLemmas.lean.
attribute [minimal_theory] eq_self
attribute [minimal_theory] ne_eq
attribute [minimal_theory] ite_true
attribute [minimal_theory] ite_false
attribute [minimal_theory] dite_true
attribute [minimal_theory] dite_false
attribute [minimal_theory] ite_self
attribute [minimal_theory] and_true
attribute [minimal_theory] true_and
attribute [minimal_theory] and_false
attribute [minimal_theory] false_and
attribute [minimal_theory] and_self
attribute [minimal_theory] and_not_self
attribute [minimal_theory] not_and_self
attribute [minimal_theory] and_imp
attribute [minimal_theory] not_and
attribute [minimal_theory] or_self
attribute [minimal_theory] or_true
attribute [minimal_theory] true_or
attribute [minimal_theory] or_false
attribute [minimal_theory] false_or
attribute [minimal_theory] if_true_left
attribute [minimal_theory] if_true_right
attribute [minimal_theory] if_false_left
attribute [minimal_theory] if_false_right
attribute [minimal_theory] iff_self
attribute [minimal_theory] iff_true
attribute [minimal_theory] true_iff
attribute [minimal_theory] iff_false
attribute [minimal_theory] false_iff
attribute [minimal_theory] eq_iff_iff
attribute [minimal_theory] false_implies
attribute [minimal_theory] implies_true
attribute [minimal_theory] true_implies
attribute [minimal_theory] not_false_eq_true
attribute [minimal_theory] not_true_eq_false
attribute [minimal_theory] not_iff_self
attribute [minimal_theory] and_self_left
attribute [minimal_theory] and_self_right
attribute [minimal_theory] and_congr_right_iff
attribute [minimal_theory] and_congr_left_iff
attribute [minimal_theory] and_iff_left_iff_imp
attribute [minimal_theory] and_iff_right_iff_imp
attribute [minimal_theory] iff_self_and
attribute [minimal_theory] iff_and_self
attribute [minimal_theory] or_self_left
attribute [minimal_theory] or_self_right
attribute [minimal_theory] or_iff_right_of_imp
attribute [minimal_theory] or_iff_left_of_imp
attribute [minimal_theory] or_iff_left_iff_imp
attribute [minimal_theory] or_iff_right_iff_imp
attribute [minimal_theory] Bool.or_false
attribute [minimal_theory] Bool.or_true
attribute [minimal_theory] Bool.false_or
attribute [minimal_theory] Bool.false_eq_true
attribute [minimal_theory] Bool.true_or
attribute [minimal_theory] Bool.or_self
attribute [minimal_theory] Bool.or_eq_true
attribute [minimal_theory] Bool.and_false
attribute [minimal_theory] Bool.and_true
attribute [minimal_theory] Bool.false_and
attribute [minimal_theory] Bool.true_and
attribute [minimal_theory] Bool.and_self
attribute [minimal_theory] Bool.and_eq_true
attribute [minimal_theory] Bool.not_not
attribute [minimal_theory] Bool.not_true
attribute [minimal_theory] Bool.not_false
attribute [minimal_theory] beq_true
attribute [minimal_theory] beq_false
attribute [minimal_theory] Bool.not_eq_true'
attribute [minimal_theory] Bool.not_eq_false'
attribute [minimal_theory] Bool.beq_to_eq
attribute [minimal_theory] Bool.not_beq_to_not_eq
attribute [minimal_theory] Bool.not_eq_true
attribute [minimal_theory] Bool.not_eq_false
attribute [minimal_theory] decide_eq_true_eq
attribute [minimal_theory] decide_not
attribute [minimal_theory] not_decide_eq_true
attribute [minimal_theory] heq_eq_eq
attribute [minimal_theory] cond_true
attribute [minimal_theory] cond_false
attribute [minimal_theory] beq_self_eq_true
attribute [minimal_theory] beq_self_eq_true'
attribute [minimal_theory] bne_self_eq_false
attribute [minimal_theory] bne_self_eq_false'
attribute [minimal_theory] decide_False
attribute [minimal_theory] decide_True
attribute [minimal_theory] decide_eq_false_iff_not
attribute [minimal_theory] decide_eq_true_iff
attribute [minimal_theory] bne_iff_ne
attribute [minimal_theory] Bool.false_eq
attribute [minimal_theory] Bool.and_eq_false_imp

attribute [minimal_theory] Decidable.not_not

attribute [minimal_theory] Nat.le_zero_eq
attribute [minimal_theory] Nat.zero_add
attribute [minimal_theory] Nat.zero_eq
attribute [minimal_theory] Nat.succ.injEq
attribute [minimal_theory] Nat.succ_ne_zero
attribute [minimal_theory] Nat.sub_zero

attribute [minimal_theory] Nat.le_refl

@[minimal_theory]
theorem option_get_bang_of_some [Inhabited α] (v : α) :
  Option.get! (some v) = v := by rfl
attribute [minimal_theory] Option.isNone_some

attribute [minimal_theory] Fin.isValue
attribute [minimal_theory] Fin.zero_eta
attribute [minimal_theory] Fin.mk.injEq

-- attribute [minimal_theory] ↓reduceIte
