/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.SeparateProofs
import Arm.FromMathlib

-- In this file, we have memory (non-)interference proofs.

----------------------------------------------------------------------

section MemoryProofs

open BitVec

----------------------------------------------------------------------
-- Key theorem: read_mem_bytes_of_write_mem_bytes_same

theorem mem_separate_preserved_second_start_addr_add_one
  (h0 : 0 < m) (h1 : m < 2^64)
  (h2 : mem_separate a b c (c + (BitVec.ofNat 64 m))) :
  mem_separate a b (c + 1#64) (c + (BitVec.ofNat 64 m)) := by
  rw [mem_separate_for_subset2 h2]
  unfold mem_subset;
  simp only [Nat.reducePow, Nat.succ_sub_succ_eq_sub, Nat.sub_zero,
             Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  simp only [BitVec.le_of_eq, true_and]
  rw [BitVec.add_sub_self_left_64 c (BitVec.ofNat 64 m)]
  rw [BitVec.add_sub_self_left_64 c 1#64]
  apply Or.inr
  apply BitVec.val_nat_le 1 m 64 h0 (_ : 1 < 2^64) h1
  decide

theorem read_mem_of_write_mem_bytes_different (hn1 : n <= 2^64)
  (h : mem_separate addr1 addr1 addr2 (addr2 + (BitVec.ofNat 64 (n - 1)))) :
  read_mem addr1 (write_mem_bytes n addr2 v s) = read_mem addr1 s := by
  by_cases hn0 : n = 0
  case pos => -- n = 0
    subst n; simp only [write_mem_bytes]
  case neg => -- n ≠ 0
    have hn0' : 0 < n := by omega
    induction n, hn0' using Nat.le_induction generalizing addr2 s
    case base =>
      have h' : addr1 ≠ addr2 := by apply mem_separate_starting_addresses_neq h
      simp only [write_mem_bytes]
      apply read_mem_of_write_mem_different h'
    case succ =>
      have h' : addr1 ≠ addr2 := by refine mem_separate_starting_addresses_neq h
      rename_i m hn n_ih
      simp_all only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero,
                     Nat.succ_ne_zero, not_false_eq_true, ne_eq,
                     write_mem_bytes, Nat.add_eq, Nat.add_zero]
      rw [n_ih]
      · rw [read_mem_of_write_mem_different h']
      · omega
      · rw [addr_add_one_add_m_sub_one m addr2 hn hn1]
        rw [mem_separate_preserved_second_start_addr_add_one hn hn1 h]
      · omega
  done

theorem append_byte_of_extract_rest_same_cast (n : Nat) (v : BitVec ((n + 1) * 8))
  (hn0 : Nat.succ 0 ≤ n)
  (h : (n * 8 + (7 - 0 + 1)) = (n + 1) * 8) :
  BitVec.cast h (zeroExtend (n * 8) (v >>> 8) ++ extractLsb 7 0 v) = v := by
  apply BitVec.append_of_extract
  · omega
  · omega
  · omega
  done

@[state_simp_rules]
theorem read_mem_bytes_of_write_mem_bytes_same (hn1 : n <= 2^64) :
  read_mem_bytes n addr (write_mem_bytes n addr v s) = v := by
  by_cases hn0 : n = 0
  case pos =>
    subst n
    unfold read_mem_bytes
    simp only [of_length_zero]
  case neg => -- n ≠ 0
   have hn0' : 0 < n := by omega
   induction n, hn0' using Nat.le_induction generalizing addr s
   case base =>
     simp only [read_mem_bytes, write_mem_bytes,
                read_mem_of_write_mem_same, BitVec.cast_eq]
     have l1 := BitVec.extractLsb_eq v
     simp only [Nat.reduceSucc, Nat.one_mul, Nat.succ_sub_succ_eq_sub,
                Nat.sub_zero, Nat.reduceAdd, BitVec.cast_eq,
                forall_const] at l1
     rw [l1]
     have l2 := BitVec.empty_bitvector_append_left v
     simp only [Nat.reduceSucc, Nat.one_mul, Nat.zero_add,
                BitVec.cast_eq, forall_const] at l2
     exact l2
   case succ =>
     rename_i n hn n_ih
     simp only [read_mem_bytes, Nat.add_eq, Nat.add_zero, write_mem_bytes]
     rw [n_ih]
     rw [read_mem_of_write_mem_bytes_different]
     · simp only [Nat.add_eq, Nat.add_zero, read_mem_of_write_mem_same]
       rw [append_byte_of_extract_rest_same_cast n v hn]
     · omega
     · have := mem_separate_contiguous_regions addr 0#64 (BitVec.ofNat 64 (n - 1))
       simp only [Nat.reducePow, Nat.succ_sub_succ_eq_sub, Nat.sub_zero,
                  BitVec.sub_zero, ofNat_lt_ofNat, Nat.reduceMod,
                  BitVec.add_zero] at this
       apply this
       simp only [Nat.reducePow] at hn1
       omega
     · omega
     · omega
  done

----------------------------------------------------------------------
-- Key theorem: read_mem_bytes_of_write_mem_bytes_different

@[state_simp_rules]
theorem read_mem_bytes_of_write_mem_bytes_different
  (hn1 : n1 <= 2^64) (hn2 : n2 <= 2^64)
  (h : mem_separate addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))) addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1)))) :
  read_mem_bytes n1 addr1 (write_mem_bytes n2 addr2 v s) =
  read_mem_bytes n1 addr1 s := by
  by_cases h1 : n1 = 0
  case pos =>
    subst n1; simp only [read_mem_bytes]
  case neg => -- n1 ≠ 0
   have h1' : 0 < n1 := by omega
   induction n1, h1' using Nat.le_induction generalizing addr1 s
   case base =>
     simp only [read_mem_bytes, BitVec.cast_eq]
     rw [read_mem_of_write_mem_bytes_different hn2]
     simp only [Nat.reduceSucc, Nat.succ_sub_succ_eq_sub,
                Nat.sub_self, BitVec.add_zero] at h
     exact h
   case succ =>
     rename_i n1 hn n_ih
     simp only [read_mem_bytes, Nat.add_eq, Nat.add_zero]
     simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h
     rw [read_mem_of_write_mem_bytes_different hn2]
     · rw [n_ih]
       · omega
       · rw [mem_separate_for_subset1 h]
         rw [addr_add_one_add_m_sub_one n1 addr1 hn hn1]
         rw [first_address_add_one_is_subset_of_region n1 addr1 hn hn1]
       · omega
     · rw [@mem_separate_for_subset1
           addr1 (addr1 + (BitVec.ofNat 64 n1)) addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))) addr1 addr1]
       · assumption
       · rw [first_address_is_subset_of_region]
  done

----------------------------------------------------------------------
-- Key theorem: write_mem_bytes_of_write_mem_bytes_commute

theorem write_mem_of_write_mem_commute
  (h : mem_separate addr2 addr2 addr1 addr1) :
  write_mem addr2 val2 (write_mem addr1 val1 s) =
  write_mem addr1 val1 (write_mem addr2 val2 s) := by
  simp_all only [write_mem, ArmState.mk.injEq, and_self, and_true, true_and]
  unfold write_store
  have := @mem_separate_starting_addresses_neq addr2 addr2 addr1 addr1
  simp [h] at this
  funext x
  split <;> simp_all only [ite_false]
  done

theorem write_mem_of_write_mem_bytes_commute
  (h0 : n <= 2^64)
  (h1 : mem_separate addr2 addr2 addr1 (addr1 + (BitVec.ofNat 64 (n - 1)))) :
  write_mem addr2 val2 (write_mem_bytes n addr1 val1 s) =
  write_mem_bytes n addr1 val1 (write_mem addr2 val2 s) := by
  by_cases h : n = 0
  case pos => subst n; simp only [write_mem_bytes]
  case neg => -- n ≠ 0
    have h' : 0 < n := by omega
    induction n, h' using Nat.le_induction generalizing addr1 addr2 val2 s
    case base =>
      simp_all only [Nat.succ_sub_succ_eq_sub, Nat.sub_self,
                     BitVec.add_zero, Nat.succ_ne_zero,
                     not_false_eq_true, write_mem_bytes]
      rw [write_mem_of_write_mem_commute]; assumption
    case succ =>
      rename_i n' h' n_ih
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h1
      simp only [write_mem_bytes, Nat.add_eq, Nat.add_zero]
      rw [n_ih]
      · rw [write_mem_of_write_mem_commute]
        rw [mem_separate_for_subset2 h1]
        simp only [first_address_is_subset_of_region]
      · omega
      · rw [@mem_separate_for_subset2 addr2 addr2 addr1 (addr1 + (BitVec.ofNat 64 n'))]
        · assumption
        · rw [addr_add_one_add_m_sub_one _ _ h' h0]
          rw [first_address_add_one_is_subset_of_region n' addr1 h' h0]
      · omega
  done

@[state_simp_rules]
theorem write_mem_bytes_of_write_mem_bytes_commute
  (h1 : n1 <= 2^64) (h2 : n2 <= 2^64)
  (h3 : mem_separate addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))) addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1)))) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n1 addr1 val1 (write_mem_bytes n2 addr2 val2 s) := by
  by_cases h_n1 : n1 = 0
  case pos => -- (n1 = 0)
    subst n1; simp only [write_mem_bytes]
  case neg => -- (n1 ≠ 0)
    induction n2 generalizing n1 addr1 addr2 val1 s
    case zero => simp only [write_mem_bytes]
    case succ =>
      rename_i n n_ih
      by_cases hn0 : n = 0
      case pos => -- (n = 0)
        subst n; simp only [write_mem_bytes]
        rw [write_mem_of_write_mem_bytes_commute h1]
        simp only [Nat.reduceSucc, Nat.succ_sub_succ_eq_sub,
                   Nat.sub_self, BitVec.add_zero] at h3
        exact h3
      case neg => -- (n ≠ 0)
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h3
        conv in write_mem_bytes (n + 1) => simp only [write_mem_bytes]
        rw [write_mem_of_write_mem_bytes_commute h1]
        · rw [n_ih h1]
          · conv in write_mem_bytes (n + 1) => simp only [write_mem_bytes]
          · omega
          · rw [mem_separate_for_subset1 h3]
            have := @mem_subset_same_region_lemma n addr2
            apply this; omega; omega
          · assumption
        · apply mem_separate_first_address_separate h3
    done

----------------------------------------------------------------------
-- Key theorems: write_mem_bytes_of_write_mem_bytes_shadow_same_region
-- and write_mem_bytes_of_write_mem_bytes_shadow_general

@[state_simp_rules]
theorem write_mem_bytes_of_write_mem_bytes_shadow_same_region
  (h : n <= 2^64) :
  write_mem_bytes n addr val2 (write_mem_bytes n addr val1 s) =
  write_mem_bytes n addr val2 s := by
  induction n generalizing addr s
  case zero => simp only [write_mem_bytes]
  case succ =>
    rename_i n' n_ih
    simp only [write_mem_bytes]
    rw [@write_mem_of_write_mem_bytes_commute n' addr]
    · rw [write_mem_of_write_mem_shadow]
      rw [n_ih]; omega
    · omega
    · rw [mem_separate_contiguous_regions_one_address _ h]
  done

theorem write_mem_bytes_of_write_mem_bytes_shadow_same_first_address
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 <= 2^64)
  (h3 : mem_subset addr (addr + (BitVec.ofNat 64 (n1 - 1))) addr (addr + (BitVec.ofNat 64 (n2 - 1)))) :
  write_mem_bytes n2 addr val2 (write_mem_bytes n1 addr val1 s) =
  write_mem_bytes n2 addr val2 s := by
  by_cases h : n1 = 0
  case pos =>
    subst n1; simp only [write_mem_bytes]
  case neg => -- n1 ≠ 0
    induction n2, h2l using Nat.le_induction generalizing n1 addr val1 s
    case base => -- (n1 ≠ 0) and (n2 = 1)
      -- n1 must also be 1, given h3. So this case reduces to shadowing
      -- of exactly one write.
      simp only [Nat.reduceSucc, Nat.succ_sub_succ_eq_sub,
                 Nat.sub_self, BitVec.add_zero] at h3
      have h1u' : n1 - 1 < 2^64 := by omega
      have h0 := @mem_subset_one_addr_region_lemma_alt (n1 - 1) addr addr h1u'
      simp only [h3, and_true, forall_const] at h0
      have : n1 = 1 := by omega
      subst_vars
      simp only [write_mem_bytes, write_mem_of_write_mem_shadow]
    case succ =>
      rename_i n hnl' n_ih
      conv in write_mem_bytes (n + 1) =>
        simp only [write_mem_bytes, Nat.add_eq, Nat.add_zero]
      conv in write_mem_bytes n1 addr .. =>
        unfold write_mem_bytes
      split
      · contradiction
      · simp only
        rename_i m val' n' val
        rw [write_mem_of_write_mem_bytes_commute (by exact Nat.le_of_lt h1u)]
        · rw [write_mem_of_write_mem_shadow]
          by_cases hn' : n' = 0
          case pos =>
            subst_vars
            simp only [write_mem_bytes, Nat.add_eq, Nat.add_zero]
          case neg => -- n' ≠ 0
            rw [n_ih (by omega) (by omega) _ hn']
            · conv in write_mem_bytes (n + 1) .. =>
                   simp only [write_mem_bytes, Nat.add_eq, Nat.add_zero]
            · simp only [Nat.succ_eq_add_one, Nat.succ_sub_succ_eq_sub,
                         Nat.sub_zero] at h3
              rw [addr_add_one_add_m_sub_one n' addr (by omega) h1u]
              rw [addr_add_one_add_m_sub_one n addr (by omega) h2u]
              rw [first_addresses_add_one_preserves_subset_same_addr
                      (by omega) h1u hnl' h2u h3]
        · rw [mem_separate_contiguous_regions_one_address addr h1u]
  done


-- set_option auto.smt.savepath "/tmp/mem_subset_neq_first_addr_small_second_region.smt2" in
private theorem mem_subset_neq_first_addr_small_second_region
  (n1 n' : Nat) (addr1 addr2 : BitVec 64)
  (h1 : n' < 2 ^ 64 - 1)
  (h2 : mem_subset addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))) addr2 (addr2 + (BitVec.ofNat 64 n')))
  (h_addr : ¬addr1 = addr2) :
  mem_subset addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))) (addr2 + 1#64) (addr2 + (BitVec.ofNat 64 n')) := by
  have : 2^64 - 1 = 18446744073709551615 := by decide
  simp_all only [mem_subset, Bool.decide_eq_true, Bool.or_eq_true,
                 decide_eq_true_eq, Bool.and_eq_true]
  cases h2
  · rename_i h
    simp [BitVec.add_sub_self_left_64] at h
    have l1 : n' = 18446744073709551615 := by
      rw [BitVec.toNat_eq (BitVec.ofNat 64 n') 18446744073709551615#64] at h
      simp only [toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
      omega
    simp [l1] at h1
  · rename_i h
    bv_omega
    done

private theorem write_mem_bytes_of_write_mem_bytes_shadow_general_n2_lt
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 < 2^64)
  (h3 : mem_subset addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))) addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1)))) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n2 addr2 val2 s := by
  by_cases h : n1 = 0
  case pos =>
    subst n1; simp only [write_mem_bytes]
  case neg => -- n1 ≠ 0
    induction n2, h2l using Nat.le_induction generalizing addr1 addr2 val1 s
    case base =>
      have h1u' : n1 - 1 < 2^64 := by omega
      simp_all only [Nat.one_lt_two_pow_iff, ne_eq, Nat.succ_ne_zero,
                     not_false_eq_true, Nat.succ_sub_succ_eq_sub,
  Nat.sub_self, BitVec.add_zero, write_mem_bytes]
      have h0 := @mem_subset_one_addr_region_lemma_alt (n1 - 1) addr1 addr2 h1u'
      simp only [h3, forall_const] at h0
      have ⟨h₀, h₁⟩ := h0
      have : n1 = 1 := by omega
      subst_vars
      simp only [write_mem_bytes, write_mem_of_write_mem_shadow]
    case succ =>
      rename_i n' hn' ihn'
      have h_sep : mem_separate addr2 addr2 (addr2 + 1#64) (addr2 + 1#64 + (BitVec.ofNat 64 (n' - 1))) := by
          have :=  mem_separate_contiguous_regions addr2 0#64 (BitVec.ofNat 64 (n' - 1))
          simp only [Nat.reducePow, Nat.succ_sub_succ_eq_sub,
                     Nat.sub_zero, BitVec.sub_zero, ofNat_lt_ofNat,
                     Nat.reduceMod, BitVec.add_zero] at this
          rw [this]
          exact n_minus_1_lt_2_64_1 n' hn' (by omega)
          done
      by_cases h_addr : addr1 = addr2
      case pos =>
        subst addr2
        rw [write_mem_bytes_of_write_mem_bytes_shadow_same_first_address]
        · omega
        · omega
        · omega
        · exact h3
      case neg => -- addr1 ≠ addr2
       repeat (conv =>
                pattern write_mem_bytes (n' + 1) ..
                simp only [write_mem_bytes, Nat.add_eq, Nat.add_zero])
       rw [←write_mem_of_write_mem_bytes_commute (by omega)]
       · rw [ihn' (by omega)]
         · rw [write_mem_of_write_mem_bytes_commute (by omega)]
           assumption
         · rw [Nat.add_sub_cancel] at h3
           rw [addr_add_one_add_m_sub_one n' addr2 hn' (by omega)]
           rw [mem_subset_neq_first_addr_small_second_region
                  n1 n' addr1 addr2 (by omega) h3 h_addr]
       · assumption
  done

theorem write_mem_bytes_of_write_mem
  (h0 : 0 < n) (h1 : n <= 2^64)
  (h2 : mem_subset addr1 addr1 addr2 (addr2 + (BitVec.ofNat 64 (n - 1)))) :
  write_mem_bytes n addr2 val2 (write_mem addr1 val1 s) =
  write_mem_bytes n addr2 val2 s := by
  induction n, h0 using Nat.le_induction generalizing addr1 addr2 val1 s
  case base =>
    simp only [write_mem_bytes]
    by_cases h₀ : addr1 = addr2
    case pos => -- (addr1 = addr2)
      subst addr2
      simp only [write_mem_of_write_mem_shadow]
    case neg => -- (addr1 ≠ addr2)
      simp only [Nat.reduceSucc, Nat.succ_sub_succ_eq_sub,
                 Nat.sub_self, BitVec.add_zero] at h2
      simp_all only [mem_subset_eq]
  case succ =>
    rename_i n' hn' n_ih
    simp only [write_mem_bytes, Nat.add_eq, Nat.add_zero]
    by_cases h₀ : addr1 = addr2
    case pos => -- (addr1 = addr2)
      subst addr2
      simp only [write_mem_of_write_mem_shadow]
    case neg =>
      rw [write_mem_of_write_mem_commute]
      · rw [n_ih (by omega)]
        simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h2
        rw [addr_add_one_add_m_sub_one n' addr2 hn' h1]
        rw [mem_subset_one_addr_neq h₀]
        assumption
      · rw [mem_separate_neq.mp]
        exact ne_comm.mp h₀
        done

private theorem write_mem_bytes_of_write_mem_bytes_shadow_general_n2_eq
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 = 2^64)
  (h3 : mem_subset addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))) addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1)))) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n2 addr2 val2 s := by
  by_cases h₀ : n1 = 0
  case pos =>
    subst n1
    simp only [write_mem_bytes]
  case neg => -- ¬(n1 = 0)
    induction n1 generalizing addr1 val2 s
    case zero =>
      conv in write_mem_bytes 0 _ _ => simp only [write_mem_bytes]
    case succ =>
      rename_i n n_ih
      conv in write_mem_bytes (Nat.succ n) .. => simp only [write_mem_bytes]
      have n_ih' := @n_ih (addr1 + 1#64) val2 (zeroExtend (n * 8) (val1 >>> 8))
                   (write_mem addr1 (extractLsb 7 0 val1) s)
                   (by omega)
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h3
      by_cases h₁ : n = 0
      case pos =>
        subst n
        simp only [write_mem_bytes]
        rw [write_mem_bytes_of_write_mem h2l]
        · omega
        · simp only [BitVec.add_zero] at h3; exact h3
      case neg => -- ¬(n = 0)
        rw [n_ih']
        · rw [write_mem_bytes_of_write_mem h2l]
          · omega
          · rw [mem_subset_first_address h3]
        · rw [addr_add_one_add_m_sub_one n addr1]
          · have l0 := @mem_subset_trans
                        (addr1 + 1#64) (addr1 + (BitVec.ofNat 64 n)) addr1 (addr1 + (BitVec.ofNat 64 n))
                        addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1)))
            simp only [h3, forall_const] at l0
            rw [first_addresses_add_one_is_subset_of_region_general] at l0
            simp only [forall_const] at l0
            · assumption
            · omega
            · omega
            · omega
            · simp only [mem_subset_refl]
          · omega
          · omega
        · exact h₁

@[state_simp_rules]
theorem write_mem_bytes_of_write_mem_bytes_shadow_general
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 <= 2^64)
  (h3 : mem_subset addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))) addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1)))) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n2 addr2 val2 s := by
  by_cases h : n2 = 2^64
  case pos =>
    simp_all only [write_mem_bytes_of_write_mem_bytes_shadow_general_n2_eq,
                   Nat.le_refl]
  case neg =>
    have h' : n2 < 2^64 := by omega
    simp_all only [write_mem_bytes_of_write_mem_bytes_shadow_general_n2_lt]
  done

----------------------------------------------------------------------
-- Key theorem: read_mem_bytes_of_write_mem_bytes_subset

theorem read_mem_of_write_mem_bytes_same_first_address
  (h0 : 0 < n) (h1 : n <= 2^64) (h : 7 - 0 + 1 = 8) :
  read_mem addr (write_mem_bytes n addr val s) =
  BitVec.cast h (extractLsb 7 0 val) := by
  unfold write_mem_bytes; simp only [Nat.sub_zero, BitVec.cast_eq]
  split
  · contradiction
  · rw [←write_mem_of_write_mem_bytes_commute (by exact Nat.le_of_lt h1)]
    · simp only [read_mem_of_write_mem_same]
    · rw [mem_separate_contiguous_regions_one_address addr h1]
  done

-- (FIXME) Argh, it's annoying to need this lemma, but using
-- BitVec.cast_eq directly was cumbersome.
theorem cast_of_extract_eq (v : BitVec p)
  (h1 : hi1 = hi2) (h2 : lo1 = lo2)
  (h : hi1 - lo1 + 1 = hi2 - lo2 + 1) :
  BitVec.cast h (extractLsb hi1 lo1 v) = (extractLsb hi2 lo2 v) := by
  subst_vars
  simp only [Nat.sub_zero, BitVec.cast_eq]

theorem read_mem_bytes_of_write_mem_bytes_subset_same_first_address
  (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : 0 < n2) (h3 : n2 <= 2^64)
  (h4 : mem_subset addr (addr + (BitVec.ofNat 64 (n2 - 1))) addr (addr + (BitVec.ofNat 64 (n1 - 1))))
  (h : n2 * 8 - 1 - 0 + 1 = n2 * 8) :
  read_mem_bytes n2 addr (write_mem_bytes n1 addr val s) =
  BitVec.cast h (extractLsb ((n2 * 8) - 1) 0 val) := by
  have rm_lemma := @read_mem_of_write_mem_bytes_same_first_address n1 addr val s h0 h1
  simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.cast_eq, forall_const] at rm_lemma
  induction n2, h2 using Nat.le_induction generalizing n1 addr val s
  case base =>
    simp only [read_mem_bytes, rm_lemma, BitVec.cast_eq, Nat.sub_zero]
    apply BitVec.empty_bitvector_append_left
    decide
  case succ =>
    rename_i n hmn n_ih
    simp only [read_mem_bytes, Nat.add_eq, Nat.add_zero,
               rm_lemma, Nat.sub_zero, BitVec.cast_eq]
    unfold write_mem_bytes; simp only [Nat.add_eq, Nat.add_zero]
    split
    · contradiction
    · rename_i i _ n1_1 v
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h4
      by_cases hn1_1 : n1_1 = 0
      case pos =>
        subst n1_1
        simp only [BitVec.add_zero] at h4
        have := mem_subset_one_addr_region_lemma_alt addr addr h3
        simp only [h4, and_true, forall_const] at this
        subst n
        simp only [Nat.add_eq, Nat.add_zero, read_mem_bytes, BitVec.cast_eq]
        apply BitVec.empty_bitvector_append_left
        simp only [Nat.zero_mul, Nat.zero_add]
        done
      case neg =>
        have hn := mem_subset_same_address_different_sizes h4
        have hn' : n <= n1_1 := by
          rw [BitVec.le_iff_val_le_val] at hn
          simp only [toNat_ofNat, Nat.reducePow] at hn
          -- TODO `erw` should not be needed here after the 2^64 simproc is disabled.
          erw [Nat.mod_eq_of_lt h3] at hn
          erw [Nat.mod_eq_of_lt h1] at hn
          exact hn
        rw [n_ih (by omega) (by omega) (by omega) _ (by omega)]
        · rw [BitVec.extract_lsb_of_zeroExtend (v >>> 8)]
          · have l1 := @BitVec.append_of_extract_general ((n1_1 + 1) * 8) 8 (n*8-1+1) (n*8) v
            simp (config := { decide := true }) only [Nat.zero_lt_succ,
              Nat.mul_pos_iff_of_pos_left, Nat.succ_sub_succ_eq_sub,
              Nat.sub_zero, Nat.reduceAdd, Nat.succ.injEq, forall_const] at l1
            rw [l1 (by omega) (by omega)]
            · simp only [Nat.add_eq, Nat.sub_zero, BitVec.cast_cast]
              apply @cast_of_extract_eq ((n1_1 + 1) * 8) (n * 8 - 1 + 1 + 7) ((n + 1) * 8 - 1) 0 0 <;>
              omega
          · omega
        · have rw_lemma2 := @read_mem_of_write_mem_bytes_same_first_address
                              n1_1 (addr + 1#64)
                              (zeroExtend (n1_1 * 8) (v >>> 8))
                              (write_mem addr (extractLsb 7 0 v) s)
          simp only [Nat.reducePow, Nat.sub_zero, Nat.reduceAdd,
                     BitVec.cast_eq, forall_const] at rw_lemma2
          rw [rw_lemma2 (by omega) (by simp only [Nat.reducePow] at h1; omega)]
        · rw [addr_add_one_add_m_sub_one n addr hmn h3]
          rw [addr_add_one_add_m_sub_one n1_1 addr (by omega) (by omega)]
          rw [first_addresses_add_one_preserves_subset_same_addr hmn h3 _ h1]
          · assumption
          · omega
  done

private theorem read_mem_of_write_mem_bytes_subset_helper_1
  (a i : Nat) (h1 : 0 < a) (h2 : a < 2^64) :
  (8 + ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i)) = (a * 8 + i) := by
  have l1 : a + (2^64 - 1) = a - 1 + 2^64 := by omega
  simp only [l1]
  have l2 : a - 1 < 2 ^ 64 := by omega
  simp only [Nat.add_mod_right, Nat.mod_eq_of_lt l2]
  omega

private theorem read_mem_of_write_mem_bytes_subset_helper_2 (a b : Nat)
  (h1 : a < b * 8) :
  a < (b + 1) * 8 := by omega

private theorem read_mem_of_write_mem_bytes_subset_helper_3 (a : Nat) (h1 : 0 < a) (h2 : a < 2^64) :
 (a + (2 ^ 64 - 1)) % 2 ^ 64 = (a - 1) := by
 have l1 : a + (2^64 - 1) = a - 1 + 2^64 := by omega
 simp only [l1]
 have l2 : a - 1 < 2 ^ 64 := by omega
 simp only [Nat.add_mod_right, Nat.mod_eq_of_lt l2]
 done

private theorem read_mem_of_write_mem_bytes_subset_helper_4
  (v a n' : Nat) (h_v_size : v < 2 ^ ((n' + 1) * 8)) (h_a_base : a ≠ 0) (h_a_size : a < 2 ^ 64) :
  (v >>> 8 % 2 ^ (n' * 8)) >>> ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8) % 2 ^ 8 = v >>> (a * 8) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow]
  by_cases h₀ : i < 8
  case pos => -- i < 8
    simp only [h₀, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
               decide_True, Bool.and_true, Bool.true_and]
    by_cases h₁ : ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i < n' * 8)
    case pos => -- (i < 8) and ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i < n' * 8)
      simp only [h₁, decide_True, Bool.and_true, Bool.true_and]
      rw [read_mem_of_write_mem_bytes_subset_helper_1]
      · exact Nat.pos_of_ne_zero h_a_base
      · exact h_a_size
    case neg => -- (i < 8) and ¬((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i < n' * 8)
      simp only [h₁, decide_False, Bool.false_and]
      rw [read_mem_of_write_mem_bytes_subset_helper_3
          a (Nat.pos_of_ne_zero h_a_base) h_a_size] at h₁
      simp only [Nat.not_lt] at h₁
      have : (n' + 1) * 8 ≤ a * 8 + i := by omega
      rw [Nat.testBit_lt_two_pow]
      exact calc
        _ < 2 ^ ((n' + 1) * 8) := by exact h_v_size
        _ <= 2 ^ (a * 8 + i) := by apply Nat.pow_le_pow_right;
                                   decide; exact this
      done
  case neg => -- ¬(i < 8)
    simp only [h₀, decide_False, Bool.false_and]
  done

theorem read_mem_of_write_mem_bytes_subset_helper_5 (a x y : Nat) :
  (((a + x) % y + 1) * 8 - 1 - (a + x) % y * 8 + 1) = 8 := by
  omega

-- (FIXME) Prove for general bitvectors.
theorem BitVec.to_nat_zero_lt_sub_64 (x y : BitVec 64) (h : ¬x = y) :
  (x - y).toNat ≠ 0 := by
  simp only [BitVec.toNat_sub]
  simp only [toNat_eq] at h
  have := x.isLt
  have := y.isLt
  simp_all only [ne_eq]
  omega

theorem read_mem_of_write_mem_bytes_subset
  (h0 : 0 < n) (h1 : n <= 2^64)
  (h2 : mem_subset addr2 addr2 addr1 (addr1 + (BitVec.ofNat 64 (n - 1))))
  (h : ((BitVec.toNat (addr2 - addr1) + 1) * 8 - 1 -
          BitVec.toNat (addr2 - addr1) * 8 + 1) = 8) :
  read_mem addr2 (write_mem_bytes n addr1 val s) =
  BitVec.cast h
    (extractLsb
      ((BitVec.toNat (addr2 - addr1) + 1) * 8 - 1)
      (BitVec.toNat (addr2 - addr1) * 8)
      val) := by
  induction n generalizing addr1 addr2 s
  case zero => contradiction
  case succ =>
    rename_i n' n_ih
    simp_all only [write_mem_bytes, Nat.succ.injEq, Nat.zero_lt_succ,
                   Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    have cast_lemma := @cast_of_extract_eq
    by_cases h₀ : n' = 0
    case pos =>
      simp_all only [Nat.lt_irrefl, Nat.zero_le, Nat.zero_sub,
                     BitVec.add_zero, mem_subset_eq, forall_const,
                     false_implies, implies_true]
      subst_vars
      simp only [write_mem_bytes, read_mem_of_write_mem_same]
      rw [←cast_lemma] <;> bv_omega
    case neg => -- (n' ≠ 0)
      by_cases h₁ : addr2 = addr1
      case pos => -- (n' ≠ 0) and (addr2 = addr1)
        subst_vars
        rw [read_mem_of_write_mem_bytes_different (by omega)]
        · simp only [read_mem_of_write_mem_same]
          rw [←cast_lemma] <;> bv_omega
        · rw [mem_separate_contiguous_regions_one_address _ (by omega)]
      case neg => -- (addr2 ≠ addr1)
        rw [n_ih]
        · ext
          -- simp only [bv_toNat]
          simp only [toNat_cast, extractLsb, extractLsb', toNat_zeroExtend]
          simp only [toNat_ushiftRight]
          simp_all only [toNat_ofNat, toNat_ofNatLt]
          simp only [BitVec.sub_of_add_is_sub_sub, Nat.succ_sub_succ_eq_sub,
                     Nat.mod_eq_of_lt, Nat.reduceLT, Nat.mod_add_mod,
                     Nat.sub_zero]
          have h_sub := BitVec.toNat_sub (addr2 - addr1) 1#64
          simp only [toNat_ofNat] at h_sub
          simp only [h_sub]
          have h_a_size := (addr2 - addr1).isLt
          have h_v_size := val.isLt
          have h_a_base := BitVec.to_nat_zero_lt_sub_64 addr2 addr1 h₁
          generalize BitVec.toNat val = v at h_v_size
          generalize BitVec.toNat (addr2 - addr1) = a at h_a_size h_a_base
          have mod_lt_conc : (2 ^ 64 - 1 % 2 ^ 64) = 2 ^ 64 - 1 := by decide
          -- (FIXME) We won't need
          -- read_mem_of_write_mem_bytes_subset_helper_5 once we can
          -- disable simproc for 2^64.
          simp only [mod_lt_conc,
                     read_mem_of_write_mem_bytes_subset_helper_5]
          have h_tmp : (2 ^ 64 - 1 + a) = (a + 2 ^ 64 - 1) := by 
            apply Nat.add_comm
          simp only [h_tmp]
          apply read_mem_of_write_mem_bytes_subset_helper_4 v a n' h_v_size h_a_base h_a_size
        · omega
        · omega
        · rw [addr_add_one_add_m_sub_one _ _ (by omega) (by omega)]
          rw [mem_subset_one_addr_neq h₁ h2]
        · omega
    done

theorem read_mem_bytes_of_write_mem_bytes_subset_helper1 (a i : Nat)
  (h1 : a < 2^64 - 1) (h2 : 8 <= i):
  ((a + 1) % 2 ^ 64 * 8 + (i - 8)) = (a * 8 + i) := by
  have h' : (a + 1) < 2^64 := by omega
  rw [Nat.mod_eq_of_lt h']
  omega

theorem read_mem_bytes_of_write_mem_bytes_subset_helper2
  (addr2 addr1 : BitVec 64) (val : BitVec (n1 * 8))
  (_h0 : 0 < n1) (_h1 : n1 <= 2 ^ 64) (h2 : 0 < n)
  (h4 : addr1 ≠ addr2) (h5 : addr2 - addr1 < (BitVec.ofNat 64 (2 ^ 64 - 1))) :
  (BitVec.toNat val >>> ((BitVec.toNat (addr2 - addr1) + 1) % 2 ^ 64 * 8) % 2 ^ (n * 8)) <<< 8 |||
      BitVec.toNat val >>> (BitVec.toNat (addr2 - addr1) * 8) % 2 ^ 8 =
    BitVec.toNat val >>> (BitVec.toNat (addr2 - addr1) * 8) %
      2 ^ ((BitVec.toNat (addr2 - addr1) + (n + 1)) * 8 - 1 - BitVec.toNat (addr2 - addr1) * 8 + 1) := by
  have h_a_size := (addr2 - addr1).isLt
  have h_v_size := val.isLt
  -- (FIXME) whnf timeout?
  -- generalize hv : BitVec.toNat val = v at h_v_size
  -- generalize ha :  BitVec.toNat (addr2 - addr1) = a
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h₀ : (i < (BitVec.toNat (addr2 - addr1) + (n + 1)) * 8 - 1 - BitVec.toNat (addr2 - addr1) * 8 + 1)
  case pos =>
    simp only [h₀, decide_True, Bool.true_and, BitVec.toNat_ofNat,
               BitVec.toNat_append, Nat.testBit_or]
    simp only [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
    by_cases h₁ : (i < 8)
    case pos => -- (i < 8)
      have : ¬(8 <= i) := by omega
      simp only [this, h₁, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
      simp only [decide_False, Bool.false_and, decide_True,
                 Bool.true_and, Bool.false_or]
    case neg => -- ¬(i < 8)
      simp only [h₁, decide_False, Bool.false_and, Bool.or_false]
      simp only [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      simp_all only [ne_eq, Nat.not_lt, ge_iff_le, decide_True, Bool.true_and]
      have l1 : (i - 8 < n * 8) := by omega
      simp_all only [l1, decide_True, Bool.true_and, Nat.add_mod_mod]
      rw [read_mem_bytes_of_write_mem_bytes_subset_helper1] <;> assumption
  case neg =>
    simp only [h₀, BitVec.bitvec_to_nat_of_nat, BitVec.toNat_append, Nat.testBit_or]
    simp only [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    by_cases h₁ : (i < 8)
    case pos => -- (i < 8)
      have h₀' : i - 8 < n * 8 := by omega
      have h₁' : ¬(8 <= i) := by omega
      simp only [Nat.not_lt] at h₀
      simp only [h₀', h₁, h₁', decide_True, decide_False,
                 Bool.false_and, Bool.true_and, Bool.false_or]
      rw [Nat.testBit_lt_two_pow]
      omega
    case neg => -- (8 <= i)
      have :  ¬ (i - 8 < n * 8) := by omega
      simp [h₁, this]
  done


private theorem mem_legal_lemma (h0 : 0 < n) (h1 : n < 2^64)
  (h2 : mem_legal a (a + (BitVec.ofNat 64 n))) :
  mem_legal (a + 1#64) (a + 1#64 + (BitVec.ofNat 64 (n - 1))) := by
  revert h0 h1 h2
  have : 2^64 = 18446744073709551616 := by decide
  simp_all [mem_legal]
  bv_omega

private theorem addr_diff_upper_bound_lemma (h0 : 0 < n1) (h1 : n1 ≤ 2 ^ 64)
  (h2 : 0 < n2) (h3 : n2 < 2^64)
  (h4 : mem_legal addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))))
  (h5 : mem_legal addr2 (addr2 + (BitVec.ofNat 64 n2)))
  (h6 : mem_subset addr2 (addr2 + (BitVec.ofNat 64 n2)) addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1)))) :
  addr2 - addr1 < (BitVec.ofNat 64 (2^64 - 1)) := by
  revert h0 h1 h2 h3 h4 h5 h6
  have _ : 2^64 = 18446744073709551616 := by decide
  have _ : 2^64 - 1 = 18446744073709551615 := by decide
  simp_all [mem_subset, mem_legal]
  bv_omega

private theorem read_mem_bytes_of_write_mem_bytes_subset_n2_lt
  (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : 0 < n2) (h3 : n2 < 2^64)
  (h4 : mem_subset addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))) addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))))
  (h5 : mem_legal addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))))
  (h6 : mem_legal addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))))
  (h : ((BitVec.toNat (addr2 - addr1) + n2) * 8 - 1 - BitVec.toNat (addr2 - addr1) * 8 + 1)
        = n2 * 8) :
  read_mem_bytes n2 addr2 (write_mem_bytes n1 addr1 val s) =
   BitVec.cast h
    (extractLsb ((((addr2 - addr1).toNat + n2) * 8) - 1) ((addr2 - addr1).toNat * 8) val) := by
  induction n2, h2 using Nat.le_induction generalizing addr1 addr2 val s
  case base =>
    simp only [Nat.reduceSucc, Nat.succ_sub_succ_eq_sub,
               Nat.sub_self, BitVec.add_zero] at h4
    simp_all only [read_mem_bytes, BitVec.cast_eq]
    have h' : (BitVec.toNat (addr2 - addr1) + 1) * 8 - 1 - BitVec.toNat (addr2 - addr1) * 8 + 1 = 8 := by
      omega
    rw [read_mem_of_write_mem_bytes_subset h0 h1 h4 h']
    apply BitVec.empty_bitvector_append_left
    decide
  case succ =>
    rename_i n h2' n_ih
    by_cases h_addr : addr1 = addr2
    case pos => -- (addr1 = addr2)
      subst addr2
      have h' : (n + 1) * 8 - 1 - 0 + 1 = (n + 1) * 8 := by omega
      have := @read_mem_bytes_of_write_mem_bytes_subset_same_first_address n1 (n + 1) addr1 val s
               h0 h1 (by omega) (by omega) h4 h'
      rw [this]
      ext
      simp only [Nat.sub_zero, BitVec.cast_eq, extractLsb_toNat,
                 Nat.shiftRight_zero, toNat_cast, BitVec.sub_self,
                 toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
    case neg => -- (addr1 ≠ addr2)
      simp only [read_mem_bytes, Nat.add_eq, Nat.add_zero]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h4
      have h_sub : mem_subset (addr2 + 1#64) (addr2 + 1#64 + (BitVec.ofNat 64 (n - 1))) addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))) := by
        rw [addr_add_one_add_m_sub_one]
        · have l0 := @mem_subset_trans (addr2 + 1#64) (addr2 + (BitVec.ofNat 64 n)) addr2 (addr2 + (BitVec.ofNat 64 n))
                   addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1)))
          simp only [h4] at l0
          rw [first_addresses_add_one_is_subset_of_region_general
              (by omega) (by omega) (by omega)] at l0
          · simp_all only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, forall_const]
          · simp only [mem_subset_refl]
        · omega
        · omega
      have l1 := @read_mem_of_write_mem_bytes_subset n1 addr2 addr1 val s (by omega) (by omega)
      have l2 := @first_address_is_subset_of_region addr2 (BitVec.ofNat 64 n)
      have l3 := mem_subset_trans l2 h4
      simp only [l3, forall_const] at l1
      rw [l1 (by omega)]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h5
      have n_ih' := @n_ih (addr2 + 1#64) addr1 val s (by omega)
      simp only [h_sub, forall_const] at n_ih'
      rw [mem_legal_lemma h2'] at n_ih'
      · simp only [forall_const] at n_ih'
        have h' : (BitVec.toNat (addr2 + 1#64 - addr1) + n) * 8 - 1 -
                  BitVec.toNat (addr2 + 1#64 - addr1) * 8 + 1 =
                  n * 8 := by
             omega
        rw [n_ih' h6 h']
        ext
        simp only [extractLsb, extractLsb', toNat_ofNat, toNat_cast,
                   BitVec.add_of_sub_sub_of_add]
        simp only [toNat_add (addr2 - addr1) 1#64, Nat.add_eq, Nat.add_zero,
                   toNat_ofNat, Nat.add_mod_mod, cast_ofNat, toNat_append]
        have := @addr_diff_upper_bound_lemma n1 n addr1 addr2 h0 h1
                 (by omega) (by omega) h6 h5 h4
        rw [read_mem_bytes_of_write_mem_bytes_subset_helper2] <;> assumption
      · omega
      · assumption
  done

-- (FIXME) I found myself needing to hide "^" inside this irreducible
-- definition because whenever I ran into a large term like 2^64 * 8,
-- Lean would either show a "deep recursion" error or the Lean server
-- would crash with the warning that `Nat.pow` got a very large
-- exponent.
@[irreducible]
def my_pow (base exp : Nat) : Nat := base ^ exp

theorem my_pow_2_gt_zero :
  0 < my_pow 2 n := by
  unfold my_pow; exact Nat.one_le_two_pow

theorem entire_memory_subset_of_only_itself
  (h0 : n <= my_pow 2 64)
  (h1 : mem_subset addr2 (addr2 + (BitVec.ofNat 64 (my_pow 2 64 - 1))) addr1 (addr1 + (BitVec.ofNat 64 (n - 1)))) :
  n = my_pow 2 64 := by
  have : 2^64 = 18446744073709551616 := by decide
  unfold my_pow at *
  simp_all [mem_subset, BitVec.add_sub_self_left_64]
  bv_omega

theorem entire_memory_subset_legal_regions_eq_addr
  (h1 : mem_subset addr2 (addr2 + (BitVec.ofNat 64 (my_pow 2 64 - 1))) addr1 (addr1 + (BitVec.ofNat 64 (my_pow 2 64 - 1))))
  (h2 : mem_legal addr1 (addr1 + (BitVec.ofNat 64 (my_pow 2 64 - 1))))
  (h3 : mem_legal addr2 (addr2 + (BitVec.ofNat 64 (my_pow 2 64 - 1)))) :
  addr1 = addr2 := by
  have : 2^64-1 = 18446744073709551615 := by decide
  unfold my_pow at *
  simp_all [mem_subset, mem_legal]
  bv_omega

private theorem read_mem_bytes_of_write_mem_bytes_subset_n2_eq_alt_helper (val : BitVec (x * 8))
  (h0 : 0 < x)
  (h : (BitVec.toNat (addr2 - addr2) + x) * 8 - 1 -
         BitVec.toNat (addr2 - addr2) * 8 + 1
        =
       x * 8) :
  val =
    BitVec.cast h
      (extractLsb ((BitVec.toNat (addr2 - addr2) + x) * 8 - 1)
        (BitVec.toNat (addr2 - addr2) * 8) val) := by
  ext
  simp only [extractLsb, extractLsb', BitVec.sub_self, toNat_ofNat,
             Nat.zero_mod, Nat.zero_mul, Nat.shiftRight_zero,
             ofNat_toNat, toNat_cast, toNat_truncate, Nat.zero_add,
             Nat.sub_zero]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.sub_add_cancel]
  · exact val.isLt
  · omega
  done

private theorem read_mem_bytes_of_write_mem_bytes_subset_n2_eq_alt
  (h0 : 0 < n1) (h1 : n1 <= my_pow 2 64) (h2 : 0 < n2) (h3 : n2 = my_pow 2 64)
  (h4 : mem_subset addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))) addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))))
  (h5 : mem_legal addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))))
  (h6 : mem_legal addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))))
  (h : ((BitVec.toNat (addr2 - addr1) + n2) * 8 - 1 - BitVec.toNat (addr2 - addr1) * 8 + 1)
        = n2 * 8) :
  read_mem_bytes n2 addr2 (write_mem_bytes n1 addr1 val s) =
   BitVec.cast h
    (extractLsb ((((addr2 - addr1).toNat + n2) * 8) - 1) ((addr2 - addr1).toNat * 8) val) := by
    subst n2
    have l0 := @entire_memory_subset_of_only_itself n1 addr2 addr1 h1 h4
    subst n1
    have l1 := @entire_memory_subset_legal_regions_eq_addr addr2 addr1 h4 h6 h5
    subst addr1
    rw [read_mem_bytes_of_write_mem_bytes_same]
    · apply read_mem_bytes_of_write_mem_bytes_subset_n2_eq_alt_helper
      simp [my_pow_2_gt_zero]
    · unfold my_pow; decide

@[state_simp_rules]
theorem read_mem_bytes_of_write_mem_bytes_subset
  (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : 0 < n2) (h3 : n2 <= 2^64)
  (h4 : mem_subset addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))) addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))))
  (h5 : mem_legal addr2 (addr2 + (BitVec.ofNat 64 (n2 - 1))))
  (h6 : mem_legal addr1 (addr1 + (BitVec.ofNat 64 (n1 - 1))))
  (h : ((BitVec.toNat (addr2 - addr1) + n2) * 8 - 1 -
         BitVec.toNat (addr2 - addr1) * 8 + 1)
        = n2 * 8) :
  read_mem_bytes n2 addr2 (write_mem_bytes n1 addr1 val s) =
   BitVec.cast h
  (extractLsb
    ((((addr2 - addr1).toNat + n2) * 8) - 1)
    ((addr2 - addr1).toNat * 8)
    val) := by
  by_cases h₀ : n2 = 2^64
  case pos =>
    apply read_mem_bytes_of_write_mem_bytes_subset_n2_eq_alt h0
    · unfold my_pow; exact h1
    · exact h2
    · unfold my_pow; exact h₀
    · exact h4
    · exact h5
    · exact h6
  case neg =>
    apply read_mem_bytes_of_write_mem_bytes_subset_n2_lt
      h0 (by omega) h2 (by omega) h4 h5 h6
  done

----------------------------------------------------------------------
-- Key theorem : write_mem_bytes_irrelevant

theorem leftshift_n_or_rightshift_n (n x y : Nat) (h : y < 2^n) :
  (x <<< n ||| y) >>> n = x := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_or]
  have l0 : y < 2^(n + i) :=
    calc
      _ < 2^n := by assumption
      _ <= 2^(n + i) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.testBit_lt_two_pow l0]
  simp only [Nat.testBit_shiftLeft, decide_True, Nat.add_sub_cancel_left,
             Nat.le_add_right, Bool.true_and, Bool.or_false]

private theorem write_mem_bytes_irrelevant_helper (h : n * 8 + 8 = (n + 1) * 8) :
  (zeroExtend (n * 8)
    ((BitVec.cast h (read_mem_bytes n (addr + 1#64) s ++ read_mem addr s)) >>> 8)) =
  read_mem_bytes n (addr + 1#64) s := by
  ext
  simp [ushiftRight, ShiftRight.shiftRight, BitVec.bitvec_to_nat_of_nat]
  have h_x_size := (read_mem_bytes n (addr + 1#64) s).isLt
  have h_y_size := (read_mem addr s).isLt
  generalize h_x : (BitVec.toNat (read_mem_bytes n (addr + 1#64) s)) = x
  generalize h_y : (BitVec.toNat (read_mem addr s)) = y
  simp only [h_x] at h_x_size
  simp only [h_y] at h_y_size
  rw [leftshift_n_or_rightshift_n 8 x y h_y_size]
  rw [Nat.mod_eq_of_lt h_x_size]
  done

private theorem extract_byte_of_read_mem_bytes_succ (n : Nat) :
  extractLsb 7 0 (read_mem_bytes (n + 1) addr s) = read_mem addr s := by
  simp only [read_mem_bytes, Nat.add_eq, Nat.add_zero, toNat_eq, extractLsb_toNat,
             toNat_cast, toNat_append, Nat.shiftRight_zero, Nat.reduceAdd]
  generalize read_mem addr s = y
  generalize (read_mem_bytes n (addr + 1#64) s) = x
  have l0 := @leftshift_n_or_mod_2n x.toNat 8 y.toNat
  rw [l0, Nat.mod_eq_of_lt y.isLt]
  done

@[state_simp_rules]
theorem write_mem_bytes_irrelevant :
  write_mem_bytes n addr (read_mem_bytes n addr s) s = s := by
  induction n generalizing addr s
  case zero => simp only [write_mem_bytes]
  case succ =>
    rename_i n n_ih
    simp only [write_mem_bytes]
    conv =>
      pattern write_mem ..
      arg 2
      simp only [extract_byte_of_read_mem_bytes_succ]
    simp only [write_mem_irrelevant]
    have n_ih' := @n_ih (addr + 1#64) s
    simp only [read_mem_bytes]
    rw [write_mem_bytes_irrelevant_helper]
    exact n_ih'
    done

-- set_option pp.deepTerms false in
-- set_option pp.deepTerms.threshold 1000 in
-- theorem write_mem_bytes_irrelevant :
--   write_mem_bytes n addr (read_mem_bytes n addr s) s = s := by
--   induction n generalizing addr s
--   case zero => simp only [write_mem_bytes]
--   case succ =>
--     rename_i n n_ih
--     simp only [read_mem_bytes, write_mem_bytes]

----------------------------------------------------------------------

end MemoryProofs
