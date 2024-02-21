/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Memory
import Auto

-- In this file, we have memory-related proofs that depend on auto.

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.timeout 20 -- seconds
set_option auto.smt.save true
-- set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true -- Print the SMT solver's output
set_option trace.auto.smt.model true  -- Print the counterexample, if any
set_option trace.auto.smt.proof false -- Do not print the proof.

----------------------------------------------------------------------

section MemoryProofs

open Std.BitVec

----------------------------------------------------------------------
---- Some helpful bitvector lemmas ----

theorem n_minus_1_lt_2_64_1 (n : Nat)
  (h1 : Nat.succ 0 ≤ n) (h2 : n + 1 ≤ 2 ^ 64) :
  (n - 1)#64 < (2 ^ 64 - 1)#64 := by
  refine BitVec.val_bitvec_lt.mp ?a
  simp [BitVec.bitvec_to_nat_of_nat]
  have : n - 1 < 2 ^ 64 := by omega
  simp_all [Nat.mod_eq_of_lt]
  exact Nat.sub_lt_left_of_lt_add h1 h2

-- (FIXME) Prove for all bitvector widths, without using auto.
set_option auto.smt.savepath "/tmp/BitVec.add_sub_self_left_64.smt2" in
theorem BitVec.add_sub_self_left_64 (a m : BitVec 64) :
  a + m - a = m := by
  auto

-- (FIXME) Prove for all bitvector widths, without using auto.
set_option auto.smt.savepath "/tmp/BitVec.add_sub_self_right_64.smt2" in
theorem BitVec.add_sub_self_right_64 (a m : BitVec 64) :
  a + m - m = a := by
  auto

-- (FIXME) Prove for all bitvector widths, without using auto.
set_option auto.smt.savepath "/tmp/BitVec.add_sub_add_left.smt2" in
theorem BitVec.add_sub_add_left (a m n : BitVec 64) :
  a + m - (a + n) = m - n := by
  auto

-- (FIXME) Prove without auto using general assoc/comm BitVec lemmas.
set_option auto.smt.savepath "/tmp/BitVec.sub_of_add_is_sub_sub.smt2" in
theorem BitVec.sub_of_add_is_sub_sub (a b c : BitVec 64) :
  (a - (b + c)) = a - b - c := by
  auto

-- (FIXME) Prove without auto using general assoc/comm BitVec lemmas.
set_option auto.smt.savepath "/tmp/BitVec.add_of_sub_sub_of_add.smt2" in
theorem BitVec.add_of_sub_sub_of_add (a b c : BitVec 64) :
  (a + b - c) = a - c + b := by
  auto

set_option auto.smt.savepath "/tmp/nat_bitvec_sub1.smt2" in
theorem nat_bitvec_sub1 (x y : BitVec 64)
  (_h : y.toNat <= x.toNat) :
  (x - y).toNat = (x.toNat - y.toNat) % 2^64 := by
  rw [BitVec.nat_bitvec_sub]
  generalize hx1 : Std.BitVec.toNat x = x1
  generalize hy1 : Std.BitVec.toNat y = y1
  have : x1 < 2^64 := by subst x1; exact x.isLt
  have : y1 < 2^64 := by subst y1; exact y.isLt
  -- Let's reduce 2^64 to a constant for SMT solvers.
  simp (config := {ground := true}) only
  rw [Nat.mod_eq_sub_mod]
  auto; auto

theorem nat_bitvec_sub2 (x y : Nat)
  (h : y <= x) (xub : x < 2^64) :
  (x - y)#64 = x#64 - y#64 := by
  have yub : y < 2^64 := calc
    _ ≤ x := h
    _ < _ := xub
  ext
  rw [nat_bitvec_sub1]
  simp only [BitVec.bitvec_to_nat_of_nat]
  have xmyub : x - y < 2^64 := calc
    x - y ≤ x := Nat.sub_le x y
    _ < _ := xub
  rw [Nat.mod_eq_of_lt xmyub]
  conv =>
    pattern (x % 2 ^ 64 - y % 2 ^ 64)
    rw [Nat.mod_eq_of_lt xub, Nat.mod_eq_of_lt yub]
  rw [Nat.mod_eq_of_lt xmyub]
  simp only [BitVec.bitvec_to_nat_of_nat]
  rw [Nat.mod_eq_of_lt xub, Nat.mod_eq_of_lt yub]
  exact h

theorem addr_add_one_add_m_sub_one  (n : Nat) (addr : BitVec 64)
  (h_lb : Nat.succ 0 ≤ n) (h_ub : n + 1 ≤ 2 ^ 64) :
  (addr + 1#64 + (n - 1)#64) = addr + n#64 := by
  have h_ub' : n < 2^64 := by exact h_ub
  rw [nat_bitvec_sub2 n 1 h_lb h_ub']
  ext
  rw [Std.BitVec.toNat_add]
  rw [←nat_bitvec_sub2 n 1 h_lb h_ub]
  simp [BitVec.bitvec_to_nat_of_nat]
  rw [←Nat.add_sub_assoc h_lb]
  omega

----------------------------------------------------------------------
---- mem_subset ----

-- (FIXME) As for Dec. 2023, lean-auto cannot resolve <[=] to
-- Std.BitVec.ul[t/e].
def lt_and_bitvec_lt (x y : BitVec n) : x < y ↔ Std.BitVec.ult x y := by
  simp [LT.lt, Std.BitVec.ult]

def le_and_bitvec_le (x y : BitVec n) : x <= y ↔ Std.BitVec.ule x y := by
  simp [LE.le, Std.BitVec.ule]

def mem_overlap_for_auto (a1 a2 b1 b2 : BitVec 64) : Bool :=
  Std.BitVec.ule (b1 - a1) (a2 - a1) ||
  Std.BitVec.ule (b2 - a1) (a2 - a1) ||
  Std.BitVec.ule (a1 - b1) (b2 - b1) ||
  Std.BitVec.ule (a2 - b1) (b2 - b1)

theorem mem_overlap_and_mem_overlap_for_auto :
  mem_overlap a1 a2 b1 b2 = mem_overlap_for_auto a1 a2 b1 b2 := by
  unfold mem_overlap mem_overlap_for_auto
  simp [le_and_bitvec_le]

def mem_subset_for_auto (a1 a2 b1 b2 : BitVec 64) : Bool :=
  ((b2 - b1) = 18446744073709551615#64) ||
  (Std.BitVec.ule (a2 - b1) (b2 - b1) &&
   Std.BitVec.ule (a1 - b1) (a2 - b1))

theorem mem_subset_and_mem_subset_for_auto :
  mem_subset a1 a2 b1 b2 = mem_subset_for_auto a1 a2 b1 b2 := by
  unfold mem_subset mem_subset_for_auto
  have : 2^64 - 1 = 18446744073709551615 := by decide
  simp [le_and_bitvec_le, this]

set_option auto.smt.savepath "/tmp/mem_subset_refl.smt2" in
theorem mem_subset_refl : mem_subset a1 a2 a1 a2 := by
  simp [mem_subset_and_mem_subset_for_auto]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/mem_subsets_overlap.smt2" in
theorem mem_subsets_overlap (h : mem_subset a1 a2 b1 b2) :
  mem_overlap a1 a2 b1 b2 := by
  revert h
  simp [mem_subset_and_mem_subset_for_auto, mem_overlap_and_mem_overlap_for_auto]
  auto d[mem_overlap_for_auto, mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/mem_subset_eq.smt2" in
theorem mem_subset_eq : mem_subset a a b b = (a = b)  := by
  simp [mem_subset_and_mem_subset_for_auto]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/mem_subset_first_address.smt2" in
theorem mem_subset_first_address (h : mem_subset a b c d) :
  mem_subset a a c d := by
  revert h
  simp_all [mem_subset_and_mem_subset_for_auto, le_and_bitvec_le, lt_and_bitvec_lt]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/mem_subset_one_addr_neq.smt2" in
theorem mem_subset_one_addr_neq (h1 : a ≠ b1)
  (h : mem_subset a a b1 b2) :
  mem_subset a a (b1 + 1#64) b2 := by
  revert h
  simp_all [mem_subset_and_mem_subset_for_auto, le_and_bitvec_le, lt_and_bitvec_lt]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/mem_subset_same_address_different_sizes.smt2" in
theorem mem_subset_same_address_different_sizes
  (h : mem_subset addr (addr + n1) addr (addr + n2)) :
  n1 <= n2 := by
  revert h
  simp [mem_subset_and_mem_subset_for_auto, le_and_bitvec_le]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/first_address_is_subset_of_region.smt2" in
theorem first_address_is_subset_of_region :
  mem_subset a a a (a + n) := by
  simp [mem_subset_and_mem_subset_for_auto]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/first_address_add_one_is_subset_of_region.smt2" in
theorem first_address_add_one_is_subset_of_region (n : Nat) (addr : BitVec 64)
  (_h_lb : 0 < n) (h_ub : n < 2 ^ 64) :
  mem_subset (addr + 1#64) (addr + n#64) addr (addr + n#64) := by
  simp [mem_subset_and_mem_subset_for_auto]
  -- auto creates an uninterpreted function for the exponentiation, so
  -- we evaluate it here.
  have : (2^64 = 0x10000000000000000) := by decide
  simp [this] at h_ub
  auto d[mem_subset_for_auto]

set_option auto.smt.timeout 30 in
set_option auto.smt.savepath "/tmp/first_addresses_add_one_is_subset_of_region_general.smt2" in
theorem first_addresses_add_one_is_subset_of_region_general
  (h0 : 0 < m) (h1 : m < 2 ^ 64) (h2 : n < 2 ^ 64)
  (h3 : mem_subset addr1 (addr1 + m#64) addr2 (addr2 + n#64)) :
  mem_subset (addr1 + 1#64) (addr1 + m#64) addr2 (addr2 + n#64) := by
  -- auto creates an uninterpreted function for the exponentiation, so
  -- we evaluate it here.
  have : (2^64 = 0x10000000000000000) := by decide
  simp_all [this]
  revert h3
  simp [mem_subset_and_mem_subset_for_auto]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/first_addresses_add_one_preserves_subset_same_addr_helper.smt2" in
private theorem first_addresses_add_one_preserves_subset_same_addr_helper (h1l : 0#64 < m) :
  m - 1#64 ≤ (2 ^ 64 - 1)#64 - 1#64 := by
  revert h1l
  simp [lt_and_bitvec_lt, le_and_bitvec_le]
  have : (2 ^ 64 - 1) = 18446744073709551615 := by decide
  simp [this]
  auto

theorem first_addresses_add_one_preserves_subset_same_addr
  (h1l : 0 < m) (h1u : m < 2 ^ 64)
  (h2l : 0 < n) (h2u : n < 2 ^ 64)
  (h3 : mem_subset addr (addr + m#64) addr (addr + n#64)) :
  mem_subset (addr + 1#64) (addr + m#64) (addr + 1#64) (addr + n#64) := by
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
      apply (BitVec.nat_bitvec_le (m#64 - 1#64) (n#64 - 1#64)).mp
      rw [nat_bitvec_sub1]; rw [nat_bitvec_sub1]
      simp [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt]
      · rw [Nat.mod_eq_of_lt h1u]
        rw [Nat.mod_eq_of_lt h2u]
        rw [Nat.mod_eq_of_lt (by exact tsub_lt_of_lt h1u)]
        rw [Nat.mod_eq_of_lt (by exact tsub_lt_of_lt h2u)]
        exact Nat.sub_le_sub_right h3_0 1
      · simp [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt, h2u]
        exact h2l
      · simp [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt, h1u]
        exact h1l
  case right =>
    rw [BitVec.add_sub_add_left]
    simp [BitVec.zero_le_sub]

set_option auto.smt.savepath "/tmp/mem_subset_one_addr_region_lemma.smt2" in
theorem mem_subset_one_addr_region_lemma (addr1 addr2 : BitVec 64) (h : n1 <= 2 ^ 64) :
  mem_subset addr1 (addr1 + n1#64 - 1#64) addr2 addr2 → (n1 = 1) ∧ (addr1 = addr2) := by
  simp (config := {ground := true}) at h
  revert h
  simp [mem_subset_and_mem_subset_for_auto]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/mem_subset_one_addr_region_lemma_alt.smt2" in
theorem mem_subset_one_addr_region_lemma_alt (addr1 addr2 : BitVec 64)
  (h : n1 < 2 ^ 64) :
  mem_subset addr1 (addr1 + n1#64) addr2 addr2 → (n1 = 0) ∧ (addr1 = addr2) := by
  simp (config := {ground := true}) at h
  revert h
  simp [mem_subset_and_mem_subset_for_auto]
  auto d[mem_subset_for_auto]

set_option auto.smt.savepath "/tmp/mem_subset_same_region_lemma.smt2" in
theorem mem_subset_same_region_lemma
  (h0 : 0 < n)
  (h1 : Nat.succ n ≤ 2 ^ 64) :
  mem_subset (addr + 1#64) (addr + 1#64 + (n - 1)#64) addr (addr + (Nat.succ n - 1)#64) := by
  simp (config := {ground := true}) at h1
  revert h0 h1
  simp [mem_subset_and_mem_subset_for_auto, le_and_bitvec_le]
  auto d[mem_subset_for_auto]

-- (FIXME) This is a theorem; see
-- Arm/mem_separate_for_subset.smt2. This can be solved by z3 in ~10s
-- if only lean-auto would map Lean definitions to SMT definitions.
set_option auto.smt.savepath "/tmp/mem_subset_trans.smt2" in
theorem mem_subset_trans
  (h1 : mem_subset a1 a2 b1 b2)
  (h2 : mem_subset b1 b2 c1 c2) :
  mem_subset a1 a2 c1 c2 := by
  revert h1 h2
  simp [mem_subset_and_mem_subset_for_auto]
  -- auto d[mem_subset_for_auto]
  sorry

----------------------------------------------------------------------
---- mem_separate ----

set_option auto.smt.savepath "/tmp/mem_separate_commutative.smt2" in
theorem mem_separate_commutative :
  mem_separate a1 a2 b1 b2 = mem_separate b1 b2 a1 a2 := by
  simp [mem_separate, mem_overlap_and_mem_overlap_for_auto]
  auto d[mem_overlap_for_auto]

set_option auto.smt.savepath "/tmp/mem_separate_starting_addresses_neq.smt2" in
theorem mem_separate_starting_addresses_neq :
  mem_separate a1 a2 b1 b2 → a1 ≠ b1 := by
  simp [mem_separate, mem_overlap_and_mem_overlap_for_auto]
  auto d[mem_overlap_for_auto]

set_option auto.smt.savepath "/tmp/mem_separate_neq.smt2" in
theorem mem_separate_neq :
  a ≠ b ↔ mem_separate a a b b := by
  simp [mem_separate, mem_overlap_and_mem_overlap_for_auto]
  auto d[mem_overlap_for_auto]

set_option auto.smt.savepath "/tmp/mem_separate_first_addresses_separate.smt2" in
theorem mem_separate_first_address_separate (h : mem_separate a b c d) :
  mem_separate a a c d := by
  revert h
  simp [mem_separate, mem_overlap_and_mem_overlap_for_auto, lt_and_bitvec_lt]
  auto d[mem_overlap_for_auto]

set_option auto.smt.savepath "/tmp/mem_separate_contiguous_regions.smt2" in
theorem mem_separate_contiguous_regions (a k n : BitVec 64)
  (hn : n < ((Std.BitVec.ofNat 64 (2^64 - 1)) - k)) :
  mem_separate a (a + k) (a + k + 1#64) (a + k + 1#64 + n) := by
  revert hn
  simp [mem_separate, mem_overlap_and_mem_overlap_for_auto, lt_and_bitvec_lt]
  have h' : (2 ^ 64 - 1)#64 = 18446744073709551615#64 := by rfl
  simp [h']
  auto d[mem_overlap_for_auto]

-- TODO: Perhaps use/modify mem_separate_contiguous_regions instead?
set_option auto.smt.savepath "/tmp/mem_separate_contiguous_regions_one_address.smt2" in
theorem mem_separate_contiguous_regions_one_address (addr : BitVec 64) (h : n' < 2 ^ 64) :
  mem_separate addr addr (addr + 1#64) (addr + 1#64 + (n' - 1)#64) := by
  revert h
  simp [mem_separate, mem_overlap_and_mem_overlap_for_auto, lt_and_bitvec_lt]
  have h' : (2 ^ 64) = 18446744073709551616 := by rfl
  simp [h']
  auto d[mem_overlap_for_auto]

----------------------------------------------------------------------
---- mem_subset and mem_separate -----

-- set_option auto.smt.savepath "/tmp/test.smt2" in
-- theorem test (h0 : 0 < n1) (h1 : n1 ≤ 2 ^ 64)
--   (h2 : 0 < n2) (h3 : n2 <= 2^64)
--   (h4 : addr1 < addr1 + (n1 - 1)#64)
--   (h5 : addr2 < addr2 + (n2 - 1)#64)
--   (h6 : addr1 ≠ addr2)
--   (h7 : mem_subset addr2 (addr2 + (n2 - 1)#64) addr1 (addr1 + (n1 - 1)#64)) :
--   addr2 - addr1 < (2^64 - 1)#64 := by
--   revert h0 h1 h2 h3 h4 h5 h6 h7
--   have _ : 2^64 = 18446744073709551616 := by decide
--   have _ : 2^64 - 1 = 18446744073709551615 := by decide
--   simp_all [mem_subset_and_mem_subset_for_auto]
--   auto d[mem_subset_for_auto]


-- (FIXME) This is a theorem; see Arm/mem_separate_for_subset.smt2,
-- which was solved by z3 in ~130s (also: by bitwuzla in ~60s, which
-- is unsupported by lean-auto right now).  If only lean-auto would
-- map Lean definitions to SMT definitions instead of inlining them,
-- we'd be able to prove this theorem here.
-- Also note that mem_separate_for_subset2 is somehow easier to prove
-- than mem_separate_for_subset1 using SMT solvers.
set_option auto.smt.savepath "/tmp/mem_separate_for_subset2.smt2" in
-- set_option trace.auto.smt.printCommands true in
-- set_option trace.Meta.synthInstance true in
theorem mem_separate_for_subset2
  (h1 : mem_separate a1 a2 b1 b2) (h2 : mem_subset c1 c2 b1 b2) :
  mem_separate a1 a2 c1 c2 := by
  revert h1 h2
  simp [mem_subset_and_mem_subset_for_auto, mem_separate, mem_overlap_and_mem_overlap_for_auto]
  -- auto d[mem_overlap_for_auto, mem_subset_for_auto]
  sorry

theorem mem_separate_for_subset1
  (h1 : mem_separate a1 a2 b1 b2) (h2 : mem_subset c1 c2 a1 a2) :
  mem_separate c1 c2 b1 b2 := by
  rw [mem_separate_commutative] at *
  rw [@mem_separate_for_subset2 b1 b2 a1 a2 c1 c2 h1 h2]

----------------------------------------------------------------------

end MemoryProofs
