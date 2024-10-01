/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.State
import Arm.Memory.Separate
import Std.Tactic.BVDecide

----------------------------------------------------------------------

section MemoryProofs

open BitVec

set_option sat.timeout 60

----------------------------------------------------------------------
---- Some helpful bitvector lemmas ----

theorem n_minus_1_lt_2_64_1 (n : Nat)
  (h1 : Nat.succ 0 ≤ n) (h2 : n < 2 ^ 64) :
  (BitVec.ofNat 64 (n - 1)) < (BitVec.ofNat 64 (2^64 - 1)) := by
  refine BitVec.val_bitvec_lt.mp ?a
  simp [BitVec.bitvec_to_nat_of_nat]
  have : n - 1 < 2 ^ 64 := by omega
  simp_all [Nat.mod_eq_of_lt]
  exact Nat.sub_lt_left_of_lt_add h1 h2

-- (FIXME) Prove for all bitvector widths.
theorem BitVec.add_sub_self_left_64 (a m : BitVec 64) :
  a + m - a = m := by
  bv_omega

-- (FIXME) Prove for all bitvector widths.
theorem BitVec.add_sub_self_right_64 (a m : BitVec 64) :
  a + m - m = a := by
  bv_omega

-- (FIXME) Prove for all bitvector widths.
theorem BitVec.add_sub_add_left (a m n : BitVec 64) :
  a + m - (a + n) = m - n := by
  bv_omega

-- (FIXME) Prove for all bitvector widths, using general assoc/comm
-- BitVec lemmas.
theorem BitVec.sub_of_add_is_sub_sub (a b c : BitVec 64) :
  (a - (b + c)) = a - b - c := by
  bv_omega

-- (FIXME) Prove for all bitvector widths, using general assoc/comm
-- BitVec lemmas.
theorem BitVec.add_of_sub_sub_of_add (a b c : BitVec 64) :
  (a + b - c) = a - c + b := by
  bv_omega

theorem nat_bitvec_sub1 (x y : BitVec 64)
  (_h : y.toNat <= x.toNat) :
  (x - y).toNat = (x.toNat - y.toNat) % 2^64 := by
  bv_omega

theorem nat_bitvec_sub2 (x y : Nat)
  (h : y <= x) (xub : x < 2^64) :
  BitVec.ofNat 64 (x - y) =
  (BitVec.ofNat 64 x) - (BitVec.ofNat 64 y) := by
  bv_omega

theorem addr_add_one_add_m_sub_one  (n : Nat) (addr : BitVec 64)
  (h_lb : Nat.succ 0 ≤ n) (h_ub : n + 1 ≤ 2 ^ 64) :
  (addr + 1#64 + (BitVec.ofNat 64 (n - 1))) = addr + (BitVec.ofNat 64 n) := by
  bv_omega

----------------------------------------------------------------------
---- mem_subset ----

theorem mem_subset_refl : mem_subset a1 a2 a1 a2 := by
  simp [mem_subset]
  bv_check "lrat_files/SeparateProofs.lean-mem_subset_refl-78-2.lrat"

theorem mem_subsets_overlap (h : mem_subset a1 a2 b1 b2) :
  mem_overlap a1 a2 b1 b2 := by
  revert h
  simp [mem_subset, mem_overlap]
  bv_check "lrat_files/SeparateProofs.lean-mem_subsets_overlap-84-2.lrat"

theorem mem_subset_eq : mem_subset a a b b = (a = b)  := by
  simp [mem_subset]
  bv_check "lrat_files/SeparateProofs.lean-mem_subset_eq-88-2.lrat"

theorem mem_subset_first_address (h : mem_subset a b c d) :
  mem_subset a a c d := by
  revert h
  simp_all [mem_subset]
  bv_check "lrat_files/SeparateProofs.lean-mem_subset_first_address-94-2.lrat"

theorem mem_subset_one_addr_neq (h1 : a ≠ b1)
  (h : mem_subset a a b1 b2) :
  mem_subset a a (b1 + 1#64) b2 := by
  revert h
  simp_all [mem_subset]
  bv_check "lrat_files/SeparateProofs.lean-mem_subset_one_addr_neq-101-2.lrat"

theorem mem_subset_same_address_different_sizes
  (h : mem_subset addr (addr + n1) addr (addr + n2)) :
  n1 <= n2 := by
  revert h
  simp [mem_subset]
  bv_check "lrat_files/SeparateProofs.lean-mem_subset_same_address_different_sizes-108-2.lrat" -- wow, crazy.


theorem first_address_is_subset_of_region :
  mem_subset a a a (a + n) := by
  simp [mem_subset]
  bv_check "lrat_files/SeparateProofs.lean-first_address_is_subset_of_region-114-2.lrat"

private theorem first_address_add_one_is_subset_of_region_helper (n addr : BitVec 64)
  (_h_lb : 0#64 < n) :
  addr + n - addr = 18446744073709551615#64 ∨
  addr + n - addr ≤ addr + n - addr ∧ addr + 1#64 - addr ≤ addr + n - addr := by
  bv_check
    "lrat_files/SeparateProofs.lean-_private.Arm.Memory.SeparateProofs.0.first_address_add_one_is_subset_of_region_helper-120-2.lrat"

theorem first_address_add_one_is_subset_of_region (n : Nat) (addr : BitVec 64)
  (_h_lb : 0 < n) (h_ub : n < 2 ^ 64) :
  mem_subset (addr + 1#64) (addr + (BitVec.ofNat 64 n)) addr (addr + (BitVec.ofNat 64 n)) := by
  simp only [mem_subset]
  have : 0#64 < (BitVec.ofNat 64 n) := by
    bv_omega
  bv_check "lrat_files/SeparateProofs.lean-first_address_add_one_is_subset_of_region-129-2.lrat"

private theorem first_addresses_add_one_is_subset_of_region_general_helper
  (n m addr1 addr2 : BitVec 64) (h0 : 0#64 < m) :
  addr2 + n - addr2 = 18446744073709551615#64 ∨
    addr1 + m - addr2 ≤ addr2 + n - addr2 ∧ addr1 - addr2 ≤ addr1 + m - addr2 →
  addr2 + n - addr2 = 18446744073709551615#64 ∨
    addr1 + m - addr2 ≤ addr2 + n - addr2 ∧ addr1 + 1#64 - addr2 ≤ addr1 + m - addr2 := by
    bv_check
      "lrat_files/SeparateProofs.lean-_private.Arm.Memory.SeparateProofs.0.first_addresses_add_one_is_subset_of_region_general_helper-137-4.lrat"

theorem first_addresses_add_one_is_subset_of_region_general
  (h0 : 0 < m) (h1 : m < 2 ^ 64) (h2 : n < 2 ^ 64)
  (h3 : mem_subset addr1 (addr1 + (BitVec.ofNat 64 m)) addr2 (addr2 + (BitVec.ofNat 64 n))) :
  mem_subset (addr1 + 1#64) (addr1 + (BitVec.ofNat 64 m)) addr2 (addr2 + (BitVec.ofNat 64 n)) := by
  -- auto creates an uninterpreted function for the exponentiation, so
  -- we evaluate it here.
  have : (2^64 = 0x10000000000000000) := by decide
  simp_all [this]
  revert h3
  simp [mem_subset]
  apply first_addresses_add_one_is_subset_of_region_general_helper
  bv_omega

private theorem first_addresses_add_one_preserves_subset_same_addr_helper (h1l : 0#64 < m) :
  m - 1#64 ≤ (BitVec.ofNat 64 (2^64 - 1)) - 1#64 := by
  revert h1l
  bv_check
    "lrat_files/SeparateProofs.lean-_private.Arm.Memory.SeparateProofs.0.first_addresses_add_one_preserves_subset_same_addr_helper-156-2.lrat"

theorem first_addresses_add_one_preserves_subset_same_addr
  (h1l : 0 < m) (h1u : m < 2 ^ 64)
  (h2l : 0 < n) (h2u : n < 2 ^ 64)
  (h3 : mem_subset addr (addr + (BitVec.ofNat 64 m)) addr (addr + (BitVec.ofNat 64 n))) :
  mem_subset (addr + 1#64) (addr + (BitVec.ofNat 64 m)) (addr + 1#64) (addr + (BitVec.ofNat 64 n)) := by
  simp [mem_subset]
  apply Or.inr
  apply And.intro
  case left =>
    rw [BitVec.add_sub_add_left]
    rw [BitVec.add_sub_add_left]
    simp [mem_subset] at h3
    cases h3
    case inl =>
      rename_i h3
      simp [BitVec.add_sub_self_left_64] at h3
      rw [h3]
      apply first_addresses_add_one_preserves_subset_same_addr_helper
      rw [←BitVec.val_bitvec_lt]
      simp [BitVec.bitvec_to_nat_of_nat]
      simp_all [Nat.mod_eq_of_lt]
    case inr =>
      rename_i h3
      have ⟨h3_0, h3_1⟩ := h3
      rw [BitVec.add_sub_self_left_64] at h3_0
      rw [BitVec.add_sub_self_left_64] at h3_0
      rw [←BitVec.nat_bitvec_le] at h3_0
      simp_all [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt]
      apply (BitVec.nat_bitvec_le ((BitVec.ofNat 64 m) - 1#64) ((BitVec.ofNat 64 n) - 1#64)).mp
      rw [nat_bitvec_sub1]; rw [nat_bitvec_sub1]
      simp [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt]
      · rw [Nat.mod_eq_of_lt h1u]
        rw [Nat.mod_eq_of_lt h2u]
        rw [Nat.mod_eq_of_lt (by omega)]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact Nat.sub_le_sub_right h3_0 1
      · simp [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt, h2u]
        exact h2l
      · simp [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt, h1u]
        exact h1l
  case right =>
    rw [BitVec.add_sub_add_left]
    simp [BitVec.zero_le_sub]

private theorem mem_subset_one_addr_region_lemma_helper (n1 addr1 addr2 : BitVec 64) :
  addr1 + n1 - 1#64 - addr2 ≤ 0#64 ∧ addr1 - addr2 ≤ addr1 + n1 - 1#64 - addr2 →
  n1 = 1 ∧ addr1 = addr2 := by
  bv_check
    "lrat_files/SeparateProofs.lean-_private.Arm.Memory.SeparateProofs.0.mem_subset_one_addr_region_lemma_helper-206-2.lrat"

theorem mem_subset_one_addr_region_lemma (addr1 addr2 : BitVec 64) (h : n1 <= 2 ^ 64) :
  mem_subset addr1 (addr1 + (BitVec.ofNat 64 n1) - 1#64) addr2 addr2 → (n1 = 1) ∧ (addr1 = addr2) := by
  simp [mem_subset]
  have h0 := mem_subset_one_addr_region_lemma_helper (BitVec.ofNat 64 n1) addr1 addr2
  have h1 : 0#64 ≠ 18446744073709551615#64 := by bv_omega
  simp_all only [ofNat_eq_ofNat, and_imp, ne_eq, false_or]
  have h2 : (BitVec.ofNat 64 n1) = 1#64 → n1 = 1 := by bv_omega
  intro h₀ h₁
  simp_all only [true_implies, BitVec.sub_self, BitVec.and_self]
  bv_normalize

theorem mem_subset_one_addr_region_lemma_alt (addr1 addr2 : BitVec 64)
  (h : n1 < 2 ^ 64) :
  mem_subset addr1 (addr1 + (BitVec.ofNat 64 n1)) addr2 addr2 → (n1 = 0) ∧ (addr1 = addr2) := by
  simp only [mem_subset, bitvec_rules, minimal_theory]
  have h1 : 0#64 ≠ 18446744073709551615#64 := by bv_omega
  simp_all only [ne_eq, false_or, and_imp]
  bv_omega

theorem mem_subset_same_region_lemma
  (h0 : 0 < n)
  (h1 : Nat.succ n ≤ 2 ^ 64) :
  mem_subset (addr + 1#64) (addr + 1#64 + (BitVec.ofNat 64 (n - 1))) addr (addr + (BitVec.ofNat 64 (Nat.succ n - 1))) := by
  simp [mem_subset]
  bv_omega
  done

/-- slow proof. -/
theorem mem_subset_trans
  (h1 : mem_subset a1 a2 b1 b2)
  (h2 : mem_subset b1 b2 c1 c2) :
  mem_subset a1 a2 c1 c2 := by
  revert h1 h2
  simp [mem_subset]
  bv_check "lrat_files/SeparateProofs.lean-mem_subset_trans-243-2.lrat"
----------------------------------------------------------------------
---- mem_separate ----

theorem mem_separate_commutative :
  mem_separate a1 a2 b1 b2 = mem_separate b1 b2 a1 a2 := by
  simp [mem_separate, mem_overlap]
  bv_check "lrat_files/SeparateProofs.lean-mem_separate_commutative-250-2.lrat"

theorem mem_separate_starting_addresses_neq :
  mem_separate a1 a2 b1 b2 → a1 ≠ b1 := by
  simp [mem_separate, mem_overlap]
  bv_check "lrat_files/SeparateProofs.lean-mem_separate_starting_addresses_neq-255-2.lrat"

theorem mem_separate_neq :
  a ≠ b ↔ mem_separate a a b b := by
  simp [mem_separate, mem_overlap]
  bv_check "lrat_files/SeparateProofs.lean-mem_separate_neq-260-2.lrat"

theorem mem_separate_first_address_separate (h : mem_separate a b c d) :
  mem_separate a a c d := by
  revert h
  simp [mem_separate, mem_overlap]
  bv_check "lrat_files/SeparateProofs.lean-mem_separate_first_address_separate-266-2.lrat"

/-- Slow proof. -/
theorem mem_separate_contiguous_regions (a k n : BitVec 64)
  (hn : n < ((BitVec.ofNat 64 (2^64 - 1)) - k)) :
  mem_separate a (a + k) (a + k + 1#64) (a + k + 1#64 + n) := by
  revert hn
  simp [mem_separate, mem_overlap]
  bv_check "lrat_files/SeparateProofs.lean-mem_separate_contiguous_regions-274-2.lrat"

private theorem mem_separate_contiguous_regions_one_address_helper (n' addr : BitVec 64)
  (h : n' < 0xffffffffffffffff) :
(¬addr + 1#64 - addr ≤ 0#64 ∧ ¬addr + 1#64 + n' - addr ≤ 0#64) ∧
    ¬addr - (addr + 1#64) ≤ addr + 1#64 + n' - (addr + 1#64) := by
  bv_check
    "lrat_files/SeparateProofs.lean-_private.Arm.Memory.SeparateProofs.0.mem_separate_contiguous_regions_one_address_helper-280-2.lrat"

-- TODO: Perhaps use/modify mem_separate_contiguous_regions instead?
theorem mem_separate_contiguous_regions_one_address (addr : BitVec 64) (h : n' < 2 ^ 64) :
  mem_separate addr addr (addr + 1#64) (addr + 1#64 + (BitVec.ofNat 64 (n' - 1))) := by
  simp [mem_separate, mem_overlap]
  have h' : (BitVec.ofNat 64 (n' - 1)) < 0xffffffffffffffff#64 := by
    bv_omega
  bv_check "lrat_files/SeparateProofs.lean-mem_separate_contiguous_regions_one_address-289-2.lrat"

----------------------------------------------------------------------
---- mem_subset and mem_separate -----

/-- Slow proof, bv_decide just times out, bv_omega solves this instantly. -/
theorem mem_separate_for_subset2
  (h1 : mem_separate a1 a2 b1 b2) (h2 : mem_subset c1 c2 b1 b2) :
  mem_separate a1 a2 c1 c2 := by
  revert h1 h2
  simp [mem_subset, mem_separate, mem_overlap]
  bv_omega

theorem mem_separate_for_subset1
  (h1 : mem_separate a1 a2 b1 b2) (h2 : mem_subset c1 c2 a1 a2) :
  mem_separate c1 c2 b1 b2 := by
  rw [mem_separate_commutative] at *
  rw [@mem_separate_for_subset2 b1 b2 a1 a2 c1 c2 h1 h2]

theorem mem_separate_for_subset_general
  (h1 : mem_separate a1 a2 b1 b2)
  (h2 : mem_subset c1 c2 a1 a2)
  (h3 : mem_subset d1 d2 b1 b2):
  mem_separate c1 c2 d1 d2 := by
  have h₁ := @mem_separate_for_subset2 a1 a2 b1 b2 d1 d2
  have h₂ := @mem_separate_for_subset1 a1 a2 d1 d2 c1 c2
  simp_all only

----------------------------------------------------------------------

end MemoryProofs
