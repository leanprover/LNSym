/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer, Shilpi Goel
-/
import Specs.GCMV8
import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.Aggregate
import Tactics.StepThms
import Tactics.CSE
import Tactics.ClearNamed
import Arm.Memory.SeparateAutomation
import Arm.Syntax
import Correctness.ArmSpec

namespace GCMGmultV8Program
open ArmStateNotation

#genStepEqTheorems gcm_gmult_v8_program

/-
theorem vrev128_64_8_in_terms_of_rev_elems (x : BitVec 128) :
DPSFP.vrev128_64_8 x =
rev_elems 128 8 ((BitVec.setWidth 64 x) ++ (BitVec.setWidth 64 (x >>> 64))) _p1 _p2 := by
simp only [DPSFP.vrev128_64_8]
unfold rev_vector
simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
unfold rev_vector
simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
rw [rev_elems_64_8_append_eq_rev_elems_128_8]
done
-/

theorem vrev128_64_8_in_terms_of_rev_elems (x : BitVec 128) :
DPSFP.vrev128_64_8 x =
-- rev_elems 64 8 (BitVec.setWidth 64 (x >>> 64)) _p1 _p2 ++
-- rev_elems 64 8 (BitVec.setWidth 64 x) _p3 _p4  := by
rev_elems 64 8 (BitVec.extractLsb' 64 64 x) _p1 _p2 ++
rev_elems 64 8 (BitVec.extractLsb' 0 64 x) _p3 _p4  := by
simp only [DPSFP.vrev128_64_8]
unfold rev_vector
simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
unfold rev_vector
simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
exact rfl
done

-- (TODO) Should we simply replace one function by the other here?
theorem gcm_polyval_mul_eq_polynomial_mult {x y : BitVec 128} :
  GCMV8.gcm_polyval_mul x y = DPSFP.polynomial_mult x y := by
  sorry

theorem eq_of_rev_elems_eq (x y : BitVec 128) (h : x = y) :
  (rev_elems 128 8 x _p1 _p2 = rev_elems 128 8 y _p1 _p2) := by
  congr

theorem pmull_op_e_0_eize_64_elements_1_size_128_eq (x y : BitVec 64) :
  DPSFP.pmull_op 0 64 1 x y 0#128 =
  DPSFP.polynomial_mult x y := by
  unfold DPSFP.pmull_op
  simp (config := {ground := true}) only [minimal_theory]
  unfold DPSFP.pmull_op
  simp (config := {ground := true}) only [minimal_theory]
  simp only [state_simp_rules, bitvec_rules]
  done

theorem rev_elems_128_8_eq_rev_elems_64_8_extractLsb' (x : BitVec 128) :
  rev_elems 128 8 x _p1 _p2 =
  rev_elems 64 8 (BitVec.extractLsb' 0 64 x) _p3 _p4 ++ rev_elems 64 8 (BitVec.extractLsb' 64 64 x) _p5 _p6 := by
  repeat unfold rev_elems
  simp (config := {decide := true, ground := true}) only [minimal_theory, BitVec.cast_eq]
  bv_check
    "lrat_files/GCMGmultV8Sym.lean-GCMGmultV8Program.rev_elems_128_8_eq_rev_elems_64_8_extractLsb'-51-2.lrat"
  done

theorem rev_elems_64_8_append_eq_rev_elems_128_8 (x y : BitVec 64) :
  rev_elems 64 8 x _p1 _p2 ++ rev_elems 64 8 y _p3 _p4 =
  rev_elems 128 8 (y ++ x) _p5 _p6 := by
  repeat unfold rev_elems
  simp (config := {decide := true, ground := true}) only [minimal_theory, BitVec.cast_eq]
  bv_check
    "lrat_files/GCMGmultV8Sym.lean-GCMGmultV8Program.rev_elems_64_8_append_eq_rev_elems_128_8-60-2.lrat"
  done

private theorem lsb_from_extractLsb'_of_append_self (x : BitVec 128) :
  BitVec.extractLsb' 64 64 (BitVec.extractLsb' 64 128 (x ++ x)) =
  BitVec.extractLsb' 0 64 x := by
  rw [BitVec.extractLsb'_append]
  simp_all (config := {ground := true}) only [bitvec_rules]
  congr

private theorem msb_from_extractLsb'_of_append_self (x : BitVec 128) :
  BitVec.extractLsb' 0 64 (BitVec.extractLsb' 64 128 (x ++ x)) =
  BitVec.extractLsb' 64 64 x := by
  rw [BitVec.extractLsb'_append]
  simp_all (config := {ground := true}) only [bitvec_rules]
  congr

private theorem zeroExtend_allOnes_lsh_64 :
  ~~~(BitVec.zeroExtend 128 (BitVec.allOnes 64) <<< 64)
    = 0x0000000000000000ffffffffffffffff#128 := by
    decide

private theorem zeroExtend_allOnes_lsh_0 :
  ~~~(BitVec.zeroExtend 128 (BitVec.allOnes 64) <<< 0) =
  0xffffffffffffffff0000000000000000#128 := by
  decide

private theorem BitVec.extractLsb'_64_128_of_appends (x y w z : BitVec 64) :
  BitVec.extractLsb' 64 128 (x ++ y ++ (w ++ z)) =
  y ++ w := by
  bv_decide

private theorem BitVec.and_high_to_extractLsb'_concat (x : BitVec 128) :
  x &&& 0xffffffffffffffff0000000000000000#128 = (BitVec.extractLsb' 64 64 x) ++ 0#64 := by
  bv_decide

theorem BitVec.extractLsb'_append_eq (x : BitVec (n + n)) :
  BitVec.extractLsb' n n x ++ BitVec.extractLsb' 0 n x = x := by
  have h1 := @BitVec.append_of_extract_general (n + n) n n x
  simp only [Nat.reduceAdd, BitVec.extractLsb'_eq] at h1
  have h3 : BitVec.setWidth n (x >>> n) = BitVec.extractLsb' n n x := by
    apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [BitVec.getLsbD_setWidth, Fin.is_lt, decide_True, BitVec.getLsbD_ushiftRight,
      Bool.true_and, BitVec.getLsbD_extractLsb']
  simp_all only


/-
(TODO) Need a lemma like the following, which breaks up a polynomial
multiplication into four constituent ones, for normalization.
-/
example :
  let p := 0b11#2
  let q := 0b10#2
  let w := 0b01#2
  let z := 0b01#2
  (DPSFP.polynomial_mult
        (p ++ q)
        (w ++ z))
  =
  ((DPSFP.polynomial_mult p w) ++ 0#4) ^^^
  (0#4 ++ (DPSFP.polynomial_mult q z)) ^^^
  (0#2 ++ (DPSFP.polynomial_mult p z) ++ 0#2) ^^^
  (0#2 ++ (DPSFP.polynomial_mult q w) ++ 0#2) := by native_decide


set_option pp.deepTerms false in
set_option pp.deepTerms.threshold 50 in
-- set_option trace.simp_mem.info true in
theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_Xi : Xi = s0[read_gpr 64 0#5 s0, 16])
    (h_HTable : HTable = s0[read_gpr 64 1#5 s0, 32])
    (h_mem_sep : Memory.Region.pairwiseSeparate
                 [(read_gpr 64 0#5 s0, 16),
                  (read_gpr 64 1#5 s0, 32)])
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    -- The final state is error-free.
    read_err sf = .None ∧
    -- The program is unmodified in `sf`.
    sf.program = gcm_gmult_v8_program ∧
    -- The stack pointer is still aligned in `sf`.
    CheckSPAlignment sf ∧
    -- The final state returns to the address in register `x30` in `s0`.
    read_pc sf = r (StateField.GPR 30#5) s0 ∧
    -- (TODO) Delete the following conjunct because it is covered by the
    -- MEM_UNCHANGED_EXCEPT frame condition. We keep it around because it
    -- exposes the issue with `simp_mem` that @bollu will fix.
    -- HTable is unmodified.
    sf[read_gpr 64 1#5 s0, 32] = HTable ∧
    -- Frame conditions.
    -- Note that the following also covers that the Xi address in .GPR 0
    -- is unmodified.
    REGS_UNCHANGED_EXCEPT [.SFP 0, .SFP 1, .SFP 2, .SFP 3,
                           .SFP 17, .SFP 18, .SFP 19, .SFP 20,
                           .SFP 21, .PC]
                          (sf, s0) ∧
    -- Memory frame condition.
    MEM_UNCHANGED_EXCEPT [(r (.GPR 0) s0, 16)] (sf, s0) ∧
    sf[r (.GPR 0) s0, 16] =
    rev_elems 128 8
            (GCMV8.GCMGmultV8_alt
              (HTable.extractLsb' 0 128)
              (rev_elems 128 8 Xi (by decide) (by decide)))
            (by decide) (by decide) := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  simp only [Nat.reduceMul] at Xi HTable
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected

  sym_n 27
  -- Epilogue
  simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  simp only [memory_rules] at *
  sym_aggregate
  -- Split conjunction
  repeat' apply And.intro
  · simp_mem; rfl
  · simp only [List.mem_cons, List.mem_singleton, not_or, and_imp] at *
    sym_aggregate
  · intro n addr h_separate
    simp_mem
    -- Aggregate the memory (non)effects.
    simp only [*]
  · clear_named [h_s, stepi_]
    clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26
    -- Simplifying the LHS
    have h_HTable_low :
      Memory.read_bytes 16 (r (StateField.GPR 1#5) s0) s0.mem = HTable.extractLsb' 0 128 := by
      -- (FIXME @bollu) use `simp_mem` instead of the rw below.
      rw [@Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
           32 (r (StateField.GPR 1#5) s0) HTable (r (StateField.GPR 1#5) s0) 16 _ h_HTable.symm]
      · simp only [Nat.reduceMul, BitVec.extractLsBytes, Nat.sub_self, Nat.zero_mul]
      · mem_omega!
    have h_HTable_high :
      (Memory.read_bytes 16 (r (StateField.GPR 1#5) s0 + 16#64) s0.mem) = HTable.extractLsb' 128 128 := by
      -- (FIXME @bollu) use `simp_mem` instead of the rw below.
      rw [@Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
          32 (r (StateField.GPR 1#5) s0) HTable (r (StateField.GPR 1#5) s0 + 16#64) 16 _ h_HTable.symm]
      repeat sorry
    simp only [h_HTable_high, h_HTable_low, ←h_Xi]
    clear h_mem_sep h_run
    /-
    simp/ground below to reduce
    (BitVec.extractLsb' 0 64
                      (shift_left_common_aux 0
                        { esize := 64, elements := 2, shift := 57, unsigned := true, round := false,
                          accumulate := false }
                        300249147283180997173565830086854304225#128 0#128))
    -/
    simp (config := {ground := true}) only
    simp only [msb_from_extractLsb'_of_append_self,
               lsb_from_extractLsb'_of_append_self,
               BitVec.partInstall]
    -- (FIXME @bollu) cse leaves the goal unchanged here, quietly, likely due to
    -- subexpressions occurring in dep. contexts. Maybe a message here would be helpful.
    generalize h_Xi_rev : DPSFP.vrev128_64_8 Xi = Xi_rev
    rw [@vrev128_64_8_in_terms_of_rev_elems (by decide) (by decide) (by decide) (by decide)] at h_Xi_rev
    generalize h_Xi_upper_rev : rev_elems 64 8 (BitVec.extractLsb' 64 64 Xi) (by decide) (by decide) = Xi_upper_rev
    generalize h_Xi_lower_rev : rev_elems 64 8 (BitVec.extractLsb' 0 64 Xi) (by decide) (by decide) = Xi_lower_rev
    -- Simplifying the RHS
    simp only [GCMV8.GCMGmultV8_alt,
               GCMV8.lo, GCMV8.hi,
               GCMV8.gcm_polyval,
               ←h_HTable, ←h_Xi_rev, h_Xi_lower_rev, h_Xi_upper_rev]
    simp only [pmull_op_e_0_eize_64_elements_1_size_128_eq, gcm_polyval_mul_eq_polynomial_mult]
    simp only [zeroExtend_allOnes_lsh_64, zeroExtend_allOnes_lsh_0]
    rw [BitVec.extractLsb'_64_128_of_appends]
    rw [BitVec.xor_append]
    repeat rw [BitVec.extractLsb'_append_right]
    repeat rw [BitVec.extractLsb'_append_left]
    repeat rw [BitVec.extractLsb'_zero_extractLsb'_of_le (by decide)]
    repeat rw [BitVec.extractLsb'_extractLsb'_zero_of_le (by decide)]
    rw [BitVec.and_high_to_extractLsb'_concat]
    generalize h_HTable_upper : (BitVec.extractLsb' 64 64 HTable) = HTable_upper
    generalize h_HTable_lower : (BitVec.extractLsb' 0 64 HTable) = HTable_lower
    generalize h_term_u0u1 : (DPSFP.polynomial_mult HTable_upper Xi_upper_rev) = u0u1 at *
    generalize h_term_l0l1 : (DPSFP.polynomial_mult HTable_lower Xi_lower_rev) = l0l1 at *
    generalize h_term_1 : (DPSFP.polynomial_mult (BitVec.extractLsb' 128 64 HTable) (Xi_lower_rev ^^^ Xi_upper_rev) ^^^
                        BitVec.extractLsb' 64 128 (l0l1 ++ u0u1) ^^^
                      (u0u1 ^^^ l0l1)) = term_1
    generalize h_term_2 : ((term_1 &&& 0xffffffffffffffff#128 ||| BitVec.zeroExtend 128 (BitVec.setWidth 64 u0u1) <<< 64) ^^^
                  DPSFP.polynomial_mult (BitVec.extractLsb' 0 64 u0u1) 0xc200000000000000#64)
                  = term_2
    generalize h_term_3 : (BitVec.extractLsb' 64 128 (term_2 ++ term_2) ^^^
            (BitVec.extractLsb' 64 64 l0l1 ++ 0x0#64 |||
              BitVec.zeroExtend 128 (BitVec.extractLsb' 64 64 term_1) <<< 0))
              = term_3
    rw [@vrev128_64_8_in_terms_of_rev_elems (by decide) (by decide) (by decide) (by decide)]
    rw [BitVec.extractLsb'_64_128_of_appends]
    rw [@rev_elems_64_8_append_eq_rev_elems_128_8 _ _ (by decide) (by decide) (by decide) (by decide)]
    apply eq_of_rev_elems_eq
    rw [@rev_elems_128_8_eq_rev_elems_64_8_extractLsb' _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [h_Xi_upper_rev, h_Xi_lower_rev]
    rw [BitVec.extractLsb'_append_eq]
    simp [GCMV8.gcm_polyval_red]
    -- have h_reduce : (GCMV8.reduce 0x100000000000000000000000000000087#129 0x1#129) = 1#129 := by native_decide
    -- simp [GCMV8.gcm_polyval_red, GCMV8.irrepoly, GCMV8.pmod, h_reduce]
    -- repeat (unfold GCMV8.pmod.pmodTR; simp)

    sorry
  done

end GCMGmultV8Program
