/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.SeparateProofs
import Auto

-- In this file, we have memory (non-)interference proofs that depend
-- on auto.

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
-- Key theorem: read_mem_bytes_of_write_mem_bytes_same

theorem read_mem_of_write_mem_bytes_different (hn1 : n <= 2^64)
  (h : mem_separate addr1 addr1 addr2 (addr2 + (n - 1)#64)) :
  read_mem addr1 (write_mem_bytes n addr2 v s) = read_mem addr1 s := by
  by_cases hn0 : n = 0
  case pos =>
    subst n; unfold write_mem_bytes; rfl
  case neg => -- n ≠ 0
    have hn0' : 0 < n := by exact Nat.pos_of_ne_zero hn0
    induction n, hn0' using Nat.le_induction generalizing addr2 s
    case base =>
      have h' : addr1 ≠ addr2 := by refine mem_separate_starting_addresses_neq h
      simp [write_mem_bytes]
      refine read_mem_of_write_mem_different h'
    case succ =>
      have h' : addr1 ≠ addr2 := by refine mem_separate_starting_addresses_neq h
      rename_i m hn n_ih
      simp_all [write_mem_bytes]
      rw [n_ih]
      · refine read_mem_of_write_mem_different h'
      · omega
      · rw [addr_add_one_add_m_sub_one m addr2 hn hn1]
        rw [mem_separate_for_subset2 h]
        unfold mem_subset; simp
        simp [BitVec.le_of_eq]
        rw [BitVec.add_sub_self_left_64 addr2 m#64]
        rw [BitVec.add_sub_self_left_64 addr2 1#64]
        apply BitVec.val_nat_le 1 m 64 hn (_ : 1 < 2^64) hn1
        decide
      · omega
  done

theorem append_byte_of_extract_rest_same_cast (n : Nat) (v : BitVec ((n + 1) * 8))
  (hn0 : Nat.succ 0 ≤ n)
  (h : (n * 8 + (7 - 0 + 1)) = (n + 1) * 8) :
  Std.BitVec.cast h (zeroExtend (n * 8) (v >>> 8) ++ BitVec.extract v 7 0) = v := by
  apply BitVec.append_of_extract
  · omega
  · exact eq_tsub_of_add_eq h
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
     have l1 := BitVec.extract_eq v
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
       simp_rw [n_minus_1_lt_2_64_1 n hn hn1] at this
       simp_rw [this]
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
      simp [Nat.succ_sub_succ_eq_sub, tsub_zero] at h1
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
        · rw [separate_regions_first_address_separate
               n#64 addr2 addr1 (addr1 + (n1 - 1)#64)]
          assumption
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
              rw [first_addresses_add_one_preserves_subset_same_addr
                    (by omega) h1u hnl' h2u h3]
        · rw [mem_separate_contiguous_regions_one_address addr h1u]
  done

set_option auto.smt.savepath "/tmp/mem_subset_neq_first_addr_small_second_region.smt2" in
theorem mem_subset_neq_first_addr_small_second_region (n1 n' : ℕ) (addr1 addr2 : BitVec 64)
  (h3 : mem_subset addr1 (addr1 + (n1 - 1)#64) addr2 (addr2 + n'#64))
  (h_addr : ¬addr1 = addr2) :
  mem_subset addr1 (addr1 + (n1 - 1)#64) (addr2 + 1#64) (addr2 + n'#64) := by
  simp_all [mem_subset, lt_and_bitvec_lt, le_and_bitvec_le]
  auto


@[simp]
theorem write_mem_bytes_of_write_mem_bytes_shadow_general
  (h1u : n1 <= 2^64) (h2l : 0 < n2) (h2u : n2 <= 2^64)
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
      have h1u' : n1 - 1 < 2^64 := by omega
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
          exact n_minus_1_lt_2_64_1 n' hn' h2u
          done
      by_cases h_addr : addr1 = addr2
      case pos =>
        subst addr2
        rw [write_mem_bytes_of_write_mem_bytes_shadow_same_first_address h1u _ h2u h3]
        omega
      case neg => -- addr1 ≠ addr2
       repeat (conv =>
                pattern write_mem_bytes (n' + 1) ..
                simp [write_mem_bytes])
       rw [←write_mem_of_write_mem_bytes_commute (by omega)]
       · rw [ihn' (by omega)]
         · rw [write_mem_of_write_mem_bytes_commute (by omega)]
           assumption
         · rw [Nat.add_sub_cancel] at h3
           rw [addr_add_one_add_m_sub_one n' addr2 hn' h2u]
           rw [mem_subset_neq_first_addr_small_second_region n1 n' addr1 addr2 h3 h_addr]
       · assumption
  done

----------------------------------------------------------------------
-- Key theorem: read_mem_bytes_of_write_mem_bytes_subset

theorem read_mem_of_write_mem_bytes_same_first_address
  (h0 : 0 < n) (h1 : n <= 2^64) (h : 7 - 0 + 1 = 8) :
  read_mem addr (write_mem_bytes n addr val s) =
  Std.BitVec.cast h (BitVec.extract val 7 0) := by
  unfold write_mem_bytes; simp
  split
  · contradiction
  · rw [←write_mem_of_write_mem_bytes_commute (by exact Nat.le_of_lt h1)]
    · simp [read_mem_of_write_mem_same]
    · rw [mem_separate_contiguous_regions_one_address addr h1]
  done

-- (FIXME) Argh, it's annoying to need this lemma.
theorem cast_of_extract_eq (v : BitVec p) (h1 : n - 0 + 1 = m + 1) (h2 : m - 0 + 1 = m + 1) :
  Std.BitVec.cast h1 (BitVec.extract v n 0) = Std.BitVec.cast h2 (BitVec.extract v m 0) := by
  have l1 : n = m := by exact Nat.succ_inj.mp h1
  subst_vars
  simp only [Nat.sub_zero, Std.BitVec.cast_eq]

theorem read_mem_bytes_of_write_mem_bytes_subset_same_first_address
  (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : 0 < n2) (h3 : n2 <= 2^64)
  (h4 : mem_subset addr (addr + (n2 - 1)#64) addr (addr + (n1 - 1)#64))
  (h : n2 * 8 - 1 - 0 + 1 = n2 * 8) :
  read_mem_bytes n2 addr (write_mem_bytes n1 addr val s) =
  Std.BitVec.cast h (BitVec.extract val ((n2 * 8) - 1) 0) := by
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
          simp [BitVec.bitvec_to_nat_of_nat] at hn
          rw [Nat.mod_eq_of_lt h3] at hn
          rw [Nat.mod_eq_of_lt h1] at hn
          exact hn
        rw [n_ih (by omega) (by omega) (by omega) _ (by omega)]
        · rw [BitVec.extract_lsb_of_zeroExtend (v >>> 8)]
          · have l1 := @BitVec.append_of_extract_general ((n1_1 + 1) * 8) 8 (n*8-1+1) (n*8) v
            simp (config := {decide := true}) at l1
            rw [l1 (by omega) (by omega)]
            · simp only [Nat.add_eq, Nat.add_succ_sub_one, Nat.sub_zero, Std.BitVec.cast_cast]
              apply cast_of_extract_eq
              simp only [Nat.add_eq, Nat.mul_eq, tsub_zero]
          · omega
        · have rw_lemma2 := @read_mem_of_write_mem_bytes_same_first_address
                              n1_1 (addr + 1#64)
                              (zeroExtend (n1_1 * 8) (v >>> 8))
                              (write_mem addr (BitVec.extract v 7 0) s)
          simp at rw_lemma2
          rw [rw_lemma2 (by omega) (by omega)]
        · rw [addr_add_one_add_m_sub_one n addr hmn h3]
          rw [addr_add_one_add_m_sub_one n1_1 addr (by omega) (by omega)]
          rw [first_addresses_add_one_preserves_subset_same_addr hmn h3 _ h1]
          · assumption
          · omega
  done

-- set_option trace.auto.smt.printCommands true in
set_option auto.smt.savepath "/tmp/read_write_mem_subset_extract_width.smt2" in
theorem read_write_mem_subset_check_extract_width (n : Nat) (a1 a2 : BitVec 64)
  (h0 : 0 < n) (h1 : n <= 2^64) :
  ((Std.BitVec.toNat (a2 - a1) + n) * 8 - 1 - Std.BitVec.toNat (a2 - a1) * 8 + 1) = n * 8 := by
  rw [BitVec.nat_bitvec_sub]
  have ha1_lt := a1.isLt
  have ha2_lt := a2.isLt
  revert h0 h1 ha1_lt ha2_lt
  generalize Std.BitVec.toNat a1 = a1'
  generalize Std.BitVec.toNat a2 = a2'
  simp (config := {ground := true})
  auto

-- @[simp]
-- theorem read_mem_bytes_of_write_mem_bytes_subset
--   (h0 : 0 < n1) (h1 : n1 <= 2^64) (h2 : n2 <= 2^64)
--   (h3 : mem_subset addr1 (addr1 + (n1 - 1)#64) addr2 (addr2 + (n2 - 1)#64))
--   (h : ((Std.BitVec.toNat (addr2 - addr1) + n1) * 8 - 1 - Std.BitVec.toNat (addr2 - addr1) * 8 + 1)
--         = n1 * 8) :
--   read_mem_bytes n1 addr1 (write_mem_bytes n2 addr2 val s) =
--    Std.BitVec.cast h
--     (BitVec.extract val ((((addr2 - addr1).toNat + n1) * 8) - 1) ((addr2 - addr1).toNat * 8)) := by
--   unfold BitVec.extract
--   sorry

----------------------------------------------------------------------

-- @[simp]
-- theorem write_mem_bytes_irrelevant :
--   write_mem_bytes n addr (read_mem_bytes n addr s) s = s := by
--   induction n generalizing addr s
--   case zero => simp [write_mem_bytes]
--   case succ =>
--     rename_i n' n_ih
--     simp [write_mem_bytes]
--     sorry

----------------------------------------------------------------------

end MemoryProofs
