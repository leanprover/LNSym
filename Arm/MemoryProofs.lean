/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.SeparateProofs
import Arm.Util
-- import Auto

-- TODO: move to core
@[elab_as_elim]
theorem Nat.le_induction {m : Nat} {P : ∀ n : Nat, m ≤ n → Prop} (base : P m m.le_refl)
    (succ : ∀ n hmn, P n hmn → P (n + 1) (le_succ_of_le hmn)) : ∀ n hmn, P n hmn := fun n hmn ↦ by
  apply Nat.le.rec
  · exact base
  · intros n hn
    apply succ n hn

-- In this file, we have memory (non-)interference proofs that depend
-- on auto.

-- set_option auto.smt true
-- set_option auto.smt.trust true
-- set_option auto.smt.timeout 20 -- seconds
-- set_option auto.smt.save true
-- -- set_option trace.auto.smt.printCommands true
-- set_option trace.auto.smt.result true -- Print the SMT solver's output
-- set_option trace.auto.smt.model true  -- Print the counterexample, if any
-- set_option trace.auto.smt.proof false -- Do not print the proof.

----------------------------------------------------------------------

section MemoryProofs

open Std.BitVec

----------------------------------------------------------------------
-- Key theorem: read_mem_bytes_of_write_mem_bytes_same

theorem mem_separate_preserved_second_start_addr_add_one
  (h0 : 0 < m) (h1 : m < 2^64)
  (h2 : mem_separate a b c (c + m#64)) :
  mem_separate a b (c + 1#64) (c + m#64) := by
  rw [mem_separate_for_subset2 h2]
  unfold mem_subset; simp
  simp [BitVec.le_of_eq]
  rw [BitVec.add_sub_self_left_64 c m#64]
  rw [BitVec.add_sub_self_left_64 c 1#64]
  apply Or.inr
  apply BitVec.val_nat_le 1 m 64 h0 (_ : 1 < 2^64) h1
  decide

theorem read_mem_of_write_mem_bytes_different (hn1 : n <= 2^64)
  (h : mem_separate addr1 addr1 addr2 (addr2 + (n - 1)#64)) :
  read_mem addr1 (write_mem_bytes n addr2 v s) = read_mem addr1 s := by
  by_cases hn0 : n = 0
  case pos => -- n = 0
    subst n; simp [write_mem_bytes]
  case neg => -- n ≠ 0
    have hn0' : 0 < n := by omega
    induction n, hn0' using Nat.le_induction generalizing addr2 s
    case base =>
      have h' : addr1 ≠ addr2 := by apply mem_separate_starting_addresses_neq h
      simp [write_mem_bytes]
      apply read_mem_of_write_mem_different h'
    case succ =>
      have h' : addr1 ≠ addr2 := by refine mem_separate_starting_addresses_neq h
      rename_i m hn n_ih
      simp_all [write_mem_bytes]
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
  Std.BitVec.cast h (zeroExtend (n * 8) (v >>> 8) ++ extractLsb 7 0 v) = v := by
  apply BitVec.append_of_extract
  · omega
  · omega
  · decide
  · omega
  done

@[simp]
theorem read_mem_bytes_of_write_mem_bytes_same (hn1 : n <= 2^64) :
  read_mem_bytes n addr (write_mem_bytes n addr v s) = v := by
  by_cases hn0 : n = 0
  case pos =>
    subst n
    unfold read_mem_bytes
    simp [BitVec.bitvec_zero_is_unique]
  case neg => -- n ≠ 0
   have hn0' : 0 < n := by omega
   induction n, hn0' using Nat.le_induction generalizing addr s
   case base =>
     simp [read_mem_bytes, write_mem_bytes, read_mem_of_write_mem_same]
     have l1 := BitVec.extractLsb_eq v
     simp at l1
     rw [l1]
     have l2 := BitVec.empty_bitvector_append_left v
     simp at l2
     exact l2
   case succ =>
     rename_i n hn n_ih
     simp [read_mem_bytes, write_mem_bytes]
     rw [n_ih]
     rw [read_mem_of_write_mem_bytes_different]
     · simp [read_mem_of_write_mem_same]
       rw [append_byte_of_extract_rest_same_cast n v hn]
     · omega
     · have := mem_separate_contiguous_regions addr 0#64 (n - 1)#64
       simp [Std.BitVec.add_zero, BitVec.sub_zero] at this
       have aux := n_minus_1_lt_2_64_1 n hn hn1
       simp at aux
       simp [aux] at this
       rw [this]
     · omega
     · omega
  done

----------------------------------------------------------------------
-- Key theorem: read_mem_bytes_of_write_mem_bytes_different

@[simp]
theorem read_mem_bytes_of_write_mem_bytes_different
  (hn1 : n1 <= 2^64) (hn2 : n2 <= 2^64)
  (h : mem_separate addr1 (addr1 + (n1 - 1)#64) addr2 (addr2 + (n2 - 1)#64)) :
  read_mem_bytes n1 addr1 (write_mem_bytes n2 addr2 v s) =
  read_mem_bytes n1 addr1 s := by
  by_cases h1 : n1 = 0
  case pos =>
    subst n1; simp [read_mem_bytes]
  case neg => -- n1 ≠ 0
   have h1' : 0 < n1 := by omega
   induction n1, h1' using Nat.le_induction generalizing addr1 s
   case base =>
     simp [read_mem_bytes]
     rw [read_mem_of_write_mem_bytes_different hn2]
     simp at h; exact h
   case succ =>
     rename_i n1 hn n_ih
     simp [read_mem_bytes]
     simp [Nat.add_sub_cancel] at h
     rw [read_mem_of_write_mem_bytes_different hn2]
     · rw [n_ih]
       · omega
       · rw [mem_separate_for_subset1 h]
         rw [addr_add_one_add_m_sub_one n1 addr1 hn hn1]
         rw [first_address_add_one_is_subset_of_region n1 addr1 hn hn1]
       · omega
     · rw [@mem_separate_for_subset1
           addr1 (addr1 + n1#64) addr2 (addr2 + (n2 - 1)#64) addr1 addr1]
       · assumption
       · rw [first_address_is_subset_of_region]
  done

----------------------------------------------------------------------
-- Key theorem: write_mem_bytes_of_write_mem_bytes_commute

theorem write_mem_of_write_mem_commute
  (h : mem_separate addr2 addr2 addr1 addr1) :
  write_mem addr2 val2 (write_mem addr1 val1 s) =
  write_mem addr1 val1 (write_mem addr2 val2 s) := by
  simp_all [write_mem]
  unfold write_store
  have := @mem_separate_starting_addresses_neq addr2 addr2 addr1 addr1
  simp [h] at this
  funext x
  split <;> simp_all
  done

theorem write_mem_of_write_mem_bytes_commute
  (h0 : n <= 2^64)
  (h1 : mem_separate addr2 addr2 addr1 (addr1 + (n - 1)#64)) :
  write_mem addr2 val2 (write_mem_bytes n addr1 val1 s) =
  write_mem_bytes n addr1 val1 (write_mem addr2 val2 s) := by
  by_cases h : n = 0
  case pos => subst n; simp [write_mem_bytes]
  case neg => -- n ≠ 0
    have h' : 0 < n := by omega
    induction n, h' using Nat.le_induction generalizing addr1 addr2 val2 s
    case base =>
      simp_all [write_mem_bytes]
      rw [write_mem_of_write_mem_commute]; assumption
    case succ =>
      rename_i n' h' n_ih
      simp [Nat.succ_sub_succ_eq_sub] at h1
      simp [write_mem_bytes]
      rw [n_ih]
      · rw [write_mem_of_write_mem_commute]
        rw [mem_separate_for_subset2 h1]
        simp [first_address_is_subset_of_region]
      · omega
      · rw [@mem_separate_for_subset2 addr2 addr2 addr1 (addr1 + n'#64)]
        · assumption
        · rw [addr_add_one_add_m_sub_one _ _ h' h0]
          rw [first_address_add_one_is_subset_of_region n' addr1 h' h0]
      · omega
  done

@[simp]
theorem write_mem_bytes_of_write_mem_bytes_commute
  (h1 : n1 <= 2^64) (h2 : n2 <= 2^64)
  (h3 : mem_separate addr2 (addr2 + (n2 - 1)#64) addr1 (addr1 + (n1 - 1)#64)) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n1 addr1 val1 (write_mem_bytes n2 addr2 val2 s) := by
  by_cases h_n1 : n1 = 0
  case pos => -- (n1 = 0)
    subst n1; simp [write_mem_bytes]
  case neg => -- (n1 ≠ 0)
    induction n2 generalizing n1 addr1 addr2 val1 s
    case zero => simp [write_mem_bytes]
    case succ =>
      rename_i n n_ih
      by_cases hn0 : n = 0
      case pos =>
        subst n; simp [write_mem_bytes]
        rw [write_mem_of_write_mem_bytes_commute h1]
        simp at h3; exact h3
      case neg => -- (n ≠ 0)
        simp at h3
        conv in write_mem_bytes (n + 1) => simp [write_mem_bytes]
        rw [write_mem_of_write_mem_bytes_commute h1]
        · rw [n_ih h1]
          · conv in write_mem_bytes (n + 1) => simp [write_mem_bytes]
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

@[simp]
theorem write_mem_bytes_of_write_mem_bytes_shadow_same_region
  (h : n <= 2^64) :
  write_mem_bytes n addr val2 (write_mem_bytes n addr val1 s) =
  write_mem_bytes n addr val2 s := by
  induction n generalizing addr s
  case zero => simp [write_mem_bytes]
  case succ =>
    rename_i n' n_ih
    simp [write_mem_bytes]
    rw [@write_mem_of_write_mem_bytes_commute n' addr]
    · rw [write_mem_of_write_mem_shadow]
      rw [n_ih]; omega
    · omega
    · rw [mem_separate_contiguous_regions_one_address _ h]
  done

theorem write_mem_bytes_of_write_mem_bytes_shadow_same_first_address
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 <= 2^64)
  (h3 : mem_subset addr (addr + (n1 - 1)#64) addr (addr + (n2 - 1)#64)) :
  write_mem_bytes n2 addr val2 (write_mem_bytes n1 addr val1 s) =
  write_mem_bytes n2 addr val2 s := by
  by_cases h : n1 = 0
  case pos =>
    subst n1; simp [write_mem_bytes]
  case neg => -- n1 ≠ 0
    induction n2, h2l using Nat.le_induction generalizing n1 addr val1 s
    case base => -- (n1 ≠ 0) and (n2 = 1)
      -- n1 must also be 1, given h3. So this case reduces to shadowing
      -- of exactly one write.
      simp at h3
      have h1u' : n1 - 1 < 2^64 := by omega
      have h0 := @mem_subset_one_addr_region_lemma_alt (n1 - 1) addr addr h1u'
      simp [h3] at h0
      have : n1 = 1 := by omega
      subst_vars
      simp [write_mem_bytes, write_mem_of_write_mem_shadow]
    case succ =>
      rename_i n hnl' n_ih
      conv in write_mem_bytes (n + 1) => simp [write_mem_bytes]
      conv in write_mem_bytes n1 addr .. => unfold write_mem_bytes
      split
      · contradiction
      · simp only
        rename_i m val' n' val
        rw [write_mem_of_write_mem_bytes_commute (by exact Nat.le_of_lt h1u)]
        · rw [write_mem_of_write_mem_shadow]
          by_cases hn' : n' = 0
          case pos =>
            subst_vars
            simp [write_mem_bytes]
          case neg => -- n' ≠ 0
            rw [n_ih (by omega) (by omega) _ hn']
            · conv in write_mem_bytes (n + 1) .. => simp [write_mem_bytes]
            · simp [Nat.succ_eq_one_add] at h3
              rw [addr_add_one_add_m_sub_one n' addr (by omega) h1u]
              rw [addr_add_one_add_m_sub_one n addr (by omega) h2u]
              FIXME
                rw [first_addresses_add_one_preserves_subset_same_addr
                      (by omega) h1u hnl' h2u h3]
        · rw [mem_separate_contiguous_regions_one_address addr h1u]
  done


-- set_option auto.smt.savepath "/tmp/mem_subset_neq_first_addr_small_second_region.smt2" in
private theorem mem_subset_neq_first_addr_small_second_region
  (n1 n' : Nat) (addr1 addr2 : BitVec 64)
  (h1 : n' < 2 ^ 64 - 1)
  (h2 : mem_subset addr1 (addr1 + (n1 - 1)#64) addr2 (addr2 + n'#64))
  (h_addr : ¬addr1 = addr2) :
  mem_subset addr1 (addr1 + (n1 - 1)#64) (addr2 + 1#64) (addr2 + n'#64) := by
  have : 2^64 - 1 = 18446744073709551615 := by decide
  simp_all [mem_subset, lt_and_bitvec_lt, le_and_bitvec_le]
  cases h2
  · rename_i h
    simp [BitVec.add_sub_self_left_64] at h
    have l1 : n' = 18446744073709551615 := by
      rw [Std.BitVec.toNat_eq n'#64 18446744073709551615#64] at h
      simp [BitVec.bitvec_to_nat_of_nat] at h
      omega
    simp [l1] at h1
  · rename_i h
    apply Or.inr
    sorry -- auto

private theorem write_mem_bytes_of_write_mem_bytes_shadow_general_n2_lt
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 < 2^64)
  (h3 : mem_subset addr1 (addr1 + (n1 - 1)#64) addr2 (addr2 + (n2 - 1)#64)) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n2 addr2 val2 s := by
  by_cases h : n1 = 0
  case pos =>
    subst n1; simp [write_mem_bytes]
  case neg => -- n1 ≠ 0
    induction n2, h2l using Nat.le_induction generalizing addr1 addr2 val1 s
    case base =>
      simp_all [write_mem_bytes]
      have h1u' : n1 - 1 < 2^64 := by simp; omega
      have h0 := @mem_subset_one_addr_region_lemma_alt (n1 - 1) addr1 addr2 h1u'
      simp [h3] at h0
      have ⟨h₀, h₁⟩ := h0
      have : n1 = 1 := by omega
      subst_vars
      simp [write_mem_bytes, write_mem_of_write_mem_shadow]
    case succ =>
      rename_i n' hn' ihn'
      have h_sep : mem_separate addr2 addr2 (addr2 + 1#64) (addr2 + 1#64 + (n' - 1)#64) := by
          have :=  mem_separate_contiguous_regions addr2 0#64 (n' - 1)#64
          simp [BitVec.sub_zero, Std.BitVec.add_zero] at this
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
                simp [write_mem_bytes])
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
  (h2 : mem_subset addr1 addr1 addr2 (addr2 + (n - 1)#64)) :
  write_mem_bytes n addr2 val2 (write_mem addr1 val1 s) =
  write_mem_bytes n addr2 val2 s := by
  induction n, h0 using Nat.le_induction generalizing addr1 addr2 val1 s
  case base =>
    simp [write_mem_bytes]
    by_cases h₀ : addr1 = addr2
    case pos => -- (addr1 = addr2)
      subst addr2
      simp [write_mem_of_write_mem_shadow]
    case neg => -- (addr1 ≠ addr2)
      simp at h2
      simp_all [mem_subset_eq]
  case succ =>
    rename_i n' hn' n_ih
    simp [write_mem_bytes]
    by_cases h₀ : addr1 = addr2
    case pos => -- (addr1 = addr2)
      subst addr2
      simp [write_mem_of_write_mem_shadow]
    case neg =>
      rw [write_mem_of_write_mem_commute]
      · rw [n_ih (by omega)]
        simp at h2
        rw [addr_add_one_add_m_sub_one n' addr2 hn' h1]
        rw [mem_subset_one_addr_neq h₀]
        assumption
      · rw [mem_separate_neq.mp]
        exact ne_comm.mp h₀
        done

private theorem write_mem_bytes_of_write_mem_bytes_shadow_general_n2_eq
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 = 2^64)
  (h3 : mem_subset addr1 (addr1 + (n1 - 1)#64) addr2 (addr2 + (n2 - 1)#64)) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n2 addr2 val2 s := by
  by_cases h₀ : n1 = 0
  case pos =>
    subst n1
    simp [write_mem_bytes]
  case neg => -- ¬(n1 = 0)
    induction n1 generalizing addr1 val2 s
    case zero =>
      conv in write_mem_bytes 0 _ _ => simp [write_mem_bytes]
    case succ =>
      rename_i n n_ih
      conv in write_mem_bytes (Nat.succ n) .. => simp [write_mem_bytes]
      have n_ih' := @n_ih (addr1 + 1#64) val2 (zeroExtend (n * 8) (val1 >>> 8))
                   (write_mem addr1 (extractLsb 7 0 val1) s)
                   (by omega)
      simp at h3
      by_cases h₁ : n = 0
      case pos =>
        subst n
        simp [write_mem_bytes]
        rw [write_mem_bytes_of_write_mem h2l]
        · omega
        · simp at h3; assumption
      case neg => -- ¬(n = 0)
        rw [n_ih']
        · rw [write_mem_bytes_of_write_mem h2l]
          · omega
          · rw [mem_subset_first_address h3]
        · rw [addr_add_one_add_m_sub_one n addr1]
          · have l0 := @mem_subset_trans
                        (addr1 + 1#64) (addr1 + n#64) addr1 (addr1 + n#64)
                        addr2 (addr2 + (n2 - 1)#64)
            simp [h3] at l0
            rw [first_addresses_add_one_is_subset_of_region_general] at l0
            simp at l0
            · assumption
            · omega
            · omega
            · omega
            · simp [mem_subset_refl]
          · omega
          · omega
        · exact h₁

@[simp]
theorem write_mem_bytes_of_write_mem_bytes_shadow_general
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 <= 2^64)
  (h3 : mem_subset addr1 (addr1 + (n1 - 1)#64) addr2 (addr2 + (n2 - 1)#64)) :
  write_mem_bytes n2 addr2 val2 (write_mem_bytes n1 addr1 val1 s) =
  write_mem_bytes n2 addr2 val2 s := by
  by_cases h : n2 = 2^64
  case pos => simp_all [write_mem_bytes_of_write_mem_bytes_shadow_general_n2_eq]
  case neg =>
    have h' : n2 < 2^64 := by omega
    simp_all [write_mem_bytes_of_write_mem_bytes_shadow_general_n2_lt]
  done

----------------------------------------------------------------------
-- Key theorem: read_mem_bytes_of_write_mem_bytes_subset

theorem read_mem_of_write_mem_bytes_same_first_address
  (h0 : 0 < n) (h1 : n <= 2^64) (h : 7 - 0 + 1 = 8) :
  read_mem addr (write_mem_bytes n addr val s) =
  Std.BitVec.cast h (extractLsb 7 0 val) := by
  unfold write_mem_bytes; simp
  split
  · contradiction
  · rw [←write_mem_of_write_mem_bytes_commute (by exact Nat.le_of_lt h1)]
    · simp [read_mem_of_write_mem_same]
    · rw [mem_separate_contiguous_regions_one_address addr h1]
  done

-- (FIXME) Argh, it's annoying to need this lemma, but using
-- Std.BitVec.cast_eq directly was cumbersome.
theorem cast_of_extract_eq (v : BitVec p)
  (h1 : hi1 = hi2) (h2 : lo1 = lo2)
  (h : hi1 - lo1 + 1 = hi2 - lo2 + 1) :
  Std.BitVec.cast h (extractLsb hi1 lo1 v) = (extractLsb hi2 lo2 v) := by
  subst_vars
  simp only [Nat.sub_zero, Std.BitVec.cast_eq]

theorem read_mem_bytes_of_write_mem_bytes_subset_same_first_address
  (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : 0 < n2) (h3 : n2 <= 2^64)
  (h4 : mem_subset addr (addr + (n2 - 1)#64) addr (addr + (n1 - 1)#64))
  (h : n2 * 8 - 1 - 0 + 1 = n2 * 8) :
  read_mem_bytes n2 addr (write_mem_bytes n1 addr val s) =
  Std.BitVec.cast h (extractLsb ((n2 * 8) - 1) 0 val) := by
  have rm_lemma := @read_mem_of_write_mem_bytes_same_first_address n1 addr val s h0 h1
  simp at rm_lemma
  induction n2, h2 using Nat.le_induction generalizing n1 addr val s
  case base =>
    simp [read_mem_bytes, rm_lemma]
    apply BitVec.empty_bitvector_append_left
    decide
  case succ =>
    rename_i n hmn n_ih
    simp [read_mem_bytes, rm_lemma]
    unfold write_mem_bytes; simp
    split
    · contradiction
    · rename_i i _ n1_1 v
      simp at h4
      by_cases hn1_1 : n1_1 = 0
      case pos =>
        subst n1_1
        simp at h4
        have := mem_subset_one_addr_region_lemma_alt addr addr h3
        simp [h4] at this
        subst n
        simp [write_mem_bytes, read_mem_bytes, read_mem_of_write_mem_same]
        apply BitVec.empty_bitvector_append_left; simp
        done
      case neg =>
        have hn := mem_subset_same_address_different_sizes h4
        have hn' : n <= n1_1 := by
          rw [BitVec.le_iff_val_le_val] at hn
          simp only [BitVec.bitvec_to_nat_of_nat] at hn
          rw [Nat.mod_eq_of_lt h3] at hn
          rw [Nat.mod_eq_of_lt h1] at hn
          exact hn
        rw [n_ih (by omega) (by omega) (by omega) _ (by omega)]
        · rw [BitVec.extract_lsb_of_zeroExtend (v >>> 8)]
          · have l1 := @BitVec.append_of_extract_general ((n1_1 + 1) * 8) 8 (n*8-1+1) (n*8) v
            simp (config := {decide := true}) at l1
            rw [l1 (by omega) (by omega)]
            · simp only [Nat.add_eq, Nat.add_one_sub_one, Nat.sub_zero, Std.BitVec.cast_cast]
              apply @cast_of_extract_eq ((n1_1 + 1) * 8) (n * 8 - 1 + 1 + 7) ((n + 1) * 8 - 1) 0 0 <;>
              omega
          · omega
        · have rw_lemma2 := @read_mem_of_write_mem_bytes_same_first_address
                              n1_1 (addr + 1#64)
                              (zeroExtend (n1_1 * 8) (v >>> 8))
                              (write_mem addr (extractLsb 7 0 v) s)
          simp at rw_lemma2
          rw [rw_lemma2 (by omega) (by simp at h1; omega)]
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
  set_option simprocs false in simp [Nat.mod_eq_of_lt l2]
  omega

private theorem read_mem_of_write_mem_bytes_subset_helper_2 (a b : Nat)
  (h1 : a < b * 8) :
  a < (b + 1) * 8 := by omega

private theorem read_mem_of_write_mem_bytes_subset_helper_3 (a : Nat) (h1 : 0 < a) (h2 : a < 2^64) :
 (a + (2 ^ 64 - 1)) % 2 ^ 64 = (a - 1) := by
 have l1 : a + (2^64 - 1) = a - 1 + 2^64 := by omega
 simp only [l1]
 have l2 : a - 1 < 2 ^ 64 := by omega
 simp at l2
 simp [Nat.mod_eq_of_lt l2]

private theorem read_mem_of_write_mem_bytes_subset_helper_4
  (v a : Nat) (h_v_size : v < 2 ^ ((n' + 1) * 8)) (h_a_base : a ≠ 0) (h_a_size : a < 2 ^ 64) :
  (v >>> 8 % 2 ^ ((n' + 1) * 8) % 2 ^ (n' * 8)) >>> ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8) % 2 ^ 8 = v >>> (a * 8) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow]
  by_cases h₂ : i < 8
  case pos => -- (i < 8)
    simp only [h₂, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
    by_cases h₃ : ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i < n' * 8)
    case pos => -- (i < 8) and ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i < n' * 8)
      simp only [h₃]
      rw [read_mem_of_write_mem_bytes_subset_helper_1]
      · have := read_mem_of_write_mem_bytes_subset_helper_2
                 ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i) n' h₃
        simp at this
        simp [this]
      · exact Nat.pos_of_ne_zero h_a_base
      · exact h_a_size
    case neg => -- (i < 8) and (not ((a + (2 ^ 64 - 1)) % 2 ^ 64 * 8 + i < n' * 8))
      FIXME
      simp [h₃]
      rw [read_mem_of_write_mem_bytes_subset_helper_3 a (Nat.pos_of_ne_zero h_a_base) h_a_size] at h₃
      simp at h₃
      have : (n' + 1) * 8 ≤ a * 8 + i := by omega
      rw [Nat.testBit_lt_two]
      exact calc
        _ < 2 ^ ((n' + 1) * 8) := by exact h_v_size
        _ <= 2 ^ (a * 8 + i) := by apply Nat.pow_le_pow_right; decide; exact this
      done
  case neg => simp [h₂]
  done

-- (FIXME) Prove without auto and for general bitvectors.
--  set_option auto.smt.savepath "/tmp/BitVec.to_nat_zero_lt_sub_64.smt2" in
theorem BitVec.to_nat_zero_lt_sub_64 (x y : BitVec 64) (_h : ¬x = y) :
  (x - y).toNat ≠ 0 := by
  simp [lt_and_bitvec_lt]
  sorry -- auto

theorem read_mem_of_write_mem_bytes_subset
  (h0 : 0 < n) (h1 : n <= 2^64)
  (h2 : mem_subset addr2 addr2 addr1 (addr1 + (n - 1)#64))
  (h : ((Std.BitVec.toNat (addr2 - addr1) + 1) * 8 - 1 -
          Std.BitVec.toNat (addr2 - addr1) * 8 + 1) = 8) :
  read_mem addr2 (write_mem_bytes n addr1 val s) =
  Std.BitVec.cast h
    (extractLsb
      ((Std.BitVec.toNat (addr2 - addr1) + 1) * 8 - 1)
      (Std.BitVec.toNat (addr2 - addr1) * 8)
      val) := by
  induction n generalizing addr1 addr2 s
  case zero => contradiction
  case succ =>
  FIXME
    rename_i n' n_ih
    simp_all [write_mem_bytes]
    have cast_lemma := @cast_of_extract_eq
    by_cases h₀ : n' = 0
    case pos =>
      simp_all [mem_subset_eq]
      subst_vars
      simp [write_mem_bytes, read_mem_of_write_mem_same]
      rw [←cast_lemma] <;> simp
    case neg => -- (n' ≠ 0)
      by_cases h₁ : addr2 = addr1
      case pos => -- (n' ≠ 0) and (addr2 = addr1)
        subst_vars
        rw [read_mem_of_write_mem_bytes_different (by omega)]
        · simp [read_mem_of_write_mem_same]
          rw [←cast_lemma] <;> simp
        · rw [mem_separate_contiguous_regions_one_address _ (by omega)]
      case neg => -- (addr2 ≠ addr1)
        rw [n_ih]
        · ext
          simp [toNat_cast, extractLsb, extractLsb']
          simp [BitVec.bitvec_to_nat_of_nat, toNat_zeroExtend]
          simp [HShiftRight.hShiftRight, ushiftRight, ShiftRight.shiftRight,
                BitVec.bitvec_to_nat_of_nat]
          simp [BitVec.sub_of_add_is_sub_sub]
          have h_sub := BitVec.nat_bitvec_sub (addr2 - addr1) 1#64
          simp [BitVec.bitvec_to_nat_of_nat, Nat.mod_eq_of_lt] at h_sub
          simp [h_sub]
          have h_a_size := (addr2 - addr1).isLt
          have h_v_size := val.isLt
          have h_a_base := BitVec.to_nat_zero_lt_sub_64 addr2 addr1 h₁
          generalize Std.BitVec.toNat val = v at h_v_size
          generalize Std.BitVec.toNat (addr2 - addr1) = a at h_a_size h_a_base
          rw [read_mem_of_write_mem_bytes_subset_helper_4]
          exact h_v_size
          exact h_a_base
          exact h_a_size
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
  (h0 : 0 < n1) (h1 : n1 <= 2 ^ 64) (h2 : 0 < n)
  (h4 : addr1 ≠ addr2) (h5 : addr2 - addr1 < (2 ^ 64 - 1)#64) :
  Std.BitVec.toNat
    ((Std.BitVec.toNat val >>>
      ((Std.BitVec.toNat (addr2 - addr1) + Std.BitVec.toNat 1#64) % 2 ^ 64 * 8))#(n * 8)
     ++
     (Std.BitVec.toNat val >>> (Std.BitVec.toNat (addr2 - addr1) * 8))#8) =
  Std.BitVec.toNat val >>>
    (Std.BitVec.toNat (addr2 - addr1) * 8) %
      2 ^ ((Std.BitVec.toNat (addr2 - addr1) + (n + 1)) * 8 - 1
        - Std.BitVec.toNat (addr2 - addr1) * 8 + 1) := by
  have h_a_size := (addr2 - addr1).isLt
  have h_v_size := val.isLt
  -- (FIXME) whnf timeout?
  -- generalize hv : Std.BitVec.toNat val = v at h_v_size
  -- generalize ha :  Std.BitVec.toNat (addr2 - addr1) = a
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h₀ : (i < (Std.BitVec.toNat (addr2 - addr1) + (n + 1))
                       * 8 - 1 - Std.BitVec.toNat (addr2 - addr1) * 8 + 1)
  case pos =>
    FIXME
    simp [h₀, BitVec.bitvec_to_nat_of_nat, Std.BitVec.toNat_append, Nat.testBit_or]
    simp [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
    by_cases h₁ : (i < 8)
    case pos => -- (i < 8)
      simp [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
      have : ¬(8 <= i) := by simp_all
      simp [h₁, this]
    case neg => -- ¬(i < 8)
      simp [h₁]
      simp [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
      simp_all
      have l1 : (i - 8 < n * 8) := by omega
      simp [l1]
      simp [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
      rw [read_mem_bytes_of_write_mem_bytes_subset_helper1] <;> assumption
  case neg => -- ¬(i < (n + 1) * 8)
    FIXME
    simp [h₀, BitVec.bitvec_to_nat_of_nat, Std.BitVec.toNat_append, Nat.testBit_or]
    simp [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    by_cases h₁ : (i < 8)
    case pos =>
      simp at h₀
      simp [h₁]
      have h₁' : ¬(8 <= i) := by omega
      simp [h₀, h₁']
      have h₀' : (n + 1) * 8 ≤ i := by omega
      rw [Nat.testBit_lt_two]
      omega
    case neg => -- (8 <= i)
      simp at h₀ h₁
      simp [h₀, h₁]
      have :  n * 8 ≤ i - 8 := by omega
      simp [this]
  done

-- set_option auto.smt.savepath "/tmp/mem_legal_lemma.smt2" in
private theorem mem_legal_lemma (h0 : 0 < n) (h1 : n < 2^64)
  (h2 : mem_legal a (a + n#64)) :
  mem_legal (a + 1#64) (a + 1#64 + (n - 1)#64) := by
  revert h0 h1 h2
  have : 2^64 = 18446744073709551616 := by decide
  simp_all [mem_legal, le_and_bitvec_le, lt_and_bitvec_lt]
  sorry -- auto

-- set_option auto.smt.savepath "/tmp/addr_diff_upper_bound_lemma.smt2" in
private theorem addr_diff_upper_bound_lemma (h0 : 0 < n1) (h1 : n1 ≤ 2 ^ 64)
  (h2 : 0 < n2) (h3 : n2 < 2^64)
  (h4 : mem_legal addr1 (addr1 + (n1 - 1)#64))
  (h5 : mem_legal addr2 (addr2 + n2#64))
  (h6 : mem_subset addr2 (addr2 + n2#64) addr1 (addr1 + (n1 - 1)#64)) :
  addr2 - addr1 < (2^64 - 1)#64 := by
  revert h0 h1 h2 h3 h4 h5 h6
  have _ : 2^64 = 18446744073709551616 := by decide
  have _ : 2^64 - 1 = 18446744073709551615 := by decide
  simp_all [mem_subset_and_mem_subset_for_auto, mem_legal]
  sorry -- auto d[mem_subset_for_auto]

private theorem read_mem_bytes_of_write_mem_bytes_subset_n2_lt
  (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : 0 < n2) (h3 : n2 < 2^64)
  (h4 : mem_subset addr2 (addr2 + (n2 - 1)#64) addr1 (addr1 + (n1 - 1)#64))
  (h5 : mem_legal addr2 (addr2 + (n2 - 1)#64))
  (h6 : mem_legal addr1 (addr1 + (n1 - 1)#64))
  (h : ((Std.BitVec.toNat (addr2 - addr1) + n2) * 8 - 1 - Std.BitVec.toNat (addr2 - addr1) * 8 + 1)
        = n2 * 8) :
  read_mem_bytes n2 addr2 (write_mem_bytes n1 addr1 val s) =
   Std.BitVec.cast h
    (extractLsb ((((addr2 - addr1).toNat + n2) * 8) - 1) ((addr2 - addr1).toNat * 8) val) := by
  FIXME
  induction n2, h2 using Nat.le_induction generalizing addr1 addr2 val s
  case base =>
    simp_all [read_mem_bytes]
    have h' : (Std.BitVec.toNat (addr2 - addr1) + 1) * 8 - 1 - Std.BitVec.toNat (addr2 - addr1) * 8 + 1 = 8 := by
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
      ext; simp
      -- (FIXME) painful!
      conv =>
        rhs
        rw [BitVec.sub_self]
        simp [BitVec.bitvec_to_nat_of_nat]
      rw [Nat.zero_add]
    case neg => -- (addr1 ≠ addr2)
      simp [read_mem_bytes]
      simp at h4
      have h_sub : mem_subset (addr2 + 1#64) (addr2 + 1#64 + (n - 1)#64) addr1 (addr1 + (n1 - 1)#64) := by
        rw [addr_add_one_add_m_sub_one]
        · have l0 := @mem_subset_trans (addr2 + 1#64) (addr2 + n#64) addr2 (addr2 + n#64)
                   addr1 (addr1 + (n1 - 1)#64)
          simp [h4] at l0
          rw [first_addresses_add_one_is_subset_of_region_general (by omega) (by omega) (by omega)] at l0
          · simp_all
          · simp [mem_subset_refl]
        · omega
        · omega
      have l1 := @read_mem_of_write_mem_bytes_subset n1 addr2 addr1 val s (by omega) (by omega)
      have l2 := @first_address_is_subset_of_region addr2 n#64
      have l3 := mem_subset_trans l2 h4
      simp [l3] at l1
      rw [l1]
      · simp at h5
        have n_ih' := @n_ih (addr2 + 1#64) addr1 val s (by omega)
        simp [h_sub] at n_ih'
        rw [mem_legal_lemma h2'] at n_ih'
        · simp at n_ih'
          have h' : (Std.BitVec.toNat (addr2 + 1#64 - addr1) + n) * 8 - 1 - Std.BitVec.toNat (addr2 + 1#64 - addr1) * 8 + 1 = n * 8 := by omega
          FIXME
          have n_ih'' := n_ih' h6 h'
          rw [n_ih'']
          · ext; simp
            simp [toNat_cast, extractLsb, extractLsb']
            simp [BitVec.bitvec_to_nat_of_nat, toNat_zeroExtend, BitVec.add_of_sub_sub_of_add]
            simp [BitVec.nat_bitvec_add (addr2 - addr1) 1#64]
            have := @addr_diff_upper_bound_lemma
                      n1 n addr1 addr2 h0 h1 (by omega) (by omega) h6 h5 h4
            rw [read_mem_bytes_of_write_mem_bytes_subset_helper2]
            · omega
            · omega
            · omega
            · exact h_addr
            · assumption
          · omega
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
  unfold my_pow;
  FIXME exact Nat.one_le_two_pow n

-- set_option auto.smt.savepath "/tmp/entire_memory_subset_of_only_itself.smt2" in
theorem entire_memory_subset_of_only_itself
  (h0 : n <= my_pow 2 64)
  (h1 : mem_subset addr2 (addr2 + (my_pow 2 64 - 1)#64) addr1 (addr1 + (n - 1)#64)) :
  n = my_pow 2 64 := by
  have : 2^64 = 18446744073709551616 := by decide
  unfold my_pow at *
  simp_all [mem_subset, BitVec.add_sub_self_left_64, lt_and_bitvec_lt, le_and_bitvec_le]
  sorry -- auto

-- set_option auto.smt.savepath "/tmp/entire_memory_subset_legal_regions_eq_addr.smt2" in
theorem entire_memory_subset_legal_regions_eq_addr
  (h1 : mem_subset addr2 (addr2 + (my_pow 2 64 - 1)#64) addr1 (addr1 + (my_pow 2 64 - 1)#64))
  (h2 : mem_legal addr1 (addr1 + (my_pow 2 64 - 1)#64))
  (h3 : mem_legal addr2 (addr2 + (my_pow 2 64 - 1)#64)) :
  addr1 = addr2 := by
  have : 2^64-1 = 18446744073709551615 := by decide
  unfold my_pow at *
  simp_all [mem_subset, mem_legal, lt_and_bitvec_lt, le_and_bitvec_le]
  sorry -- auto

private theorem read_mem_bytes_of_write_mem_bytes_subset_n2_eq_alt_helper (val : BitVec (x * 8))
  (h0 : 0 < x)
  (h : (Std.BitVec.toNat (addr2 - addr2) + x) * 8 - 1 -
         Std.BitVec.toNat (addr2 - addr2) * 8 + 1
        =
       x * 8) :
  val =
    Std.BitVec.cast h
      (extractLsb ((Std.BitVec.toNat (addr2 - addr2) + x) * 8 - 1)
        (Std.BitVec.toNat (addr2 - addr2) * 8) val) := by
  FIXME
  ext; simp
  simp [toNat_cast, extractLsb, extractLsb']
  rw [Nat.mod_eq_of_lt]
  rw [Nat.sub_add_cancel]
  · exact val.isLt
  · omega
  done

private theorem read_mem_bytes_of_write_mem_bytes_subset_n2_eq_alt
  (h0 : 0 < n1) (h1 : n1 <= my_pow 2 64) (h2 : 0 < n2) (h3 : n2 = my_pow 2 64)
  (h4 : mem_subset addr2 (addr2 + (n2 - 1)#64) addr1 (addr1 + (n1 - 1)#64))
  (h5 : mem_legal addr2 (addr2 + (n2 - 1)#64))
  (h6 : mem_legal addr1 (addr1 + (n1 - 1)#64))
  (h : ((Std.BitVec.toNat (addr2 - addr1) + n2) * 8 - 1 - Std.BitVec.toNat (addr2 - addr1) * 8 + 1)
        = n2 * 8) :
  read_mem_bytes n2 addr2 (write_mem_bytes n1 addr1 val s) =
   Std.BitVec.cast h
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

@[simp]
theorem read_mem_bytes_of_write_mem_bytes_subset
  (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : 0 < n2) (h3 : n2 <= 2^64)
  (h4 : mem_subset addr2 (addr2 + (n2 - 1)#64) addr1 (addr1 + (n1 - 1)#64))
  (h5 : mem_legal addr2 (addr2 + (n2 - 1)#64))
  (h6 : mem_legal addr1 (addr1 + (n1 - 1)#64))
  (h : ((Std.BitVec.toNat (addr2 - addr1) + n2) * 8 - 1 -
         Std.BitVec.toNat (addr2 - addr1) * 8 + 1)
        = n2 * 8) :
  read_mem_bytes n2 addr2 (write_mem_bytes n1 addr1 val s) =
   Std.BitVec.cast h
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

theorem leftshift_n_or_rightshift_n (x y : Nat) (h : y < 2^n) :
  (x <<< n ||| y) >>> n = x := by
  FIXME
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_shiftRight, Nat.testBit_or]
  have l0 : y < 2^(n + i) :=
    calc
      _ < 2^n := by assumption
      _ <= 2^(n + i) := by simp [Nat.pow_le_pow_right]
  rw [Nat.testBit_lt_two l0]
  simp [Nat.testBit_shiftLeft]

private theorem write_mem_bytes_irrelevant_helper (h : n * 8 + 8 = (n + 1) * 8) :
  (zeroExtend (n * 8)
    ((Std.BitVec.cast h (read_mem_bytes n (addr + 1#64) s ++ read_mem addr s)) >>> 8)) =
  read_mem_bytes n (addr + 1#64) s := by
  ext
  simp [zeroExtend]
  simp [HShiftRight.hShiftRight, ushiftRight, ShiftRight.shiftRight,
                BitVec.bitvec_to_nat_of_nat]
  FIXME
  simp [Std.BitVec.toNat_append]
  have h_x_size := (read_mem_bytes n (addr + 1#64) s).isLt
  have h_y_size := (read_mem addr s).isLt
  generalize h_x : (Std.BitVec.toNat (read_mem_bytes n (addr + 1#64) s)) = x
  generalize h_y : (Std.BitVec.toNat (read_mem addr s)) = y
  simp [h_x] at h_x_size
  simp [h_y] at h_y_size
  rw [leftshift_n_or_rightshift_n _ _ h_y_size]
  have l0 : 1 < 2 := by decide
  have l1 : n * 8 < (n + 1) * 8 := by omega
  have l2 := pow_lt_pow_right l0 l1
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mod_eq_of_lt]
    omega
  · rw [Nat.mod_eq_of_lt]
    · exact h_x_size
    · omega
  done

@[simp]
theorem write_mem_bytes_irrelevant :
  write_mem_bytes n addr (read_mem_bytes n addr s) s = s := by
  FIXME
  induction n generalizing addr s
  case zero => simp [write_mem_bytes]
  case succ =>
    rename_i n n_ih
    simp [write_mem_bytes, read_mem_bytes]
    conv =>
      pattern write_mem ..
      arg 2
      simp [toNat_cast, extractLsb, extractLsb']
      simp [BitVec.bitvec_to_nat_of_nat, toNat_zeroExtend]
      simp [BitVec.truncate_to_lsb_of_append]
    simp [write_mem_irrelevant]
    have n_ih' := @n_ih (addr + 1#64) s
    rw [write_mem_bytes_irrelevant_helper]
    exact n_ih'
    done

----------------------------------------------------------------------

end MemoryProofs
