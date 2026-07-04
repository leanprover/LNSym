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

-- v4.15: the `simp` below exceeded the default heartbeats at `whnf`; bumped.
-- v4.27: PARKED. The `repeat unfold rev_elems; simp (config := {ground := true})`
-- recipe (green ≤ v4.26 at default maxRecDepth) now hits the same v4.27 elaborator
-- recursion/stack regression as `gcm_gmult_v8_program_run_27` below: at the default
-- `maxRecDepth` the `unfold`/`simp` overflows the recursion limit, and raising
-- maxRecDepth makes `simp (ground)` ground-evaluate the fully-unfolded `rev_elems`
-- into a giant literal that OOMs (~34 GB, exit 137) / stack-overflows the kernel.
-- These two bridging lemmas are used ONLY by the (now-parked) functional GCMGmult
-- proof, so parking them loses no live content. Full recipe preserved at tag
-- `port-v4.26.0`; re-enable when the sym_n/rev_elems term-size regression is fixed
-- (see memory notes `v431-symn-oom-widespread`, `gcm-gmult-symn-oom-v431`).
set_option maxHeartbeats 1000000 in
theorem rev_elems_128_8_eq_rev_elems_64_8_extractLsb' (x : BitVec 128) :
  rev_elems 128 8 x _p1 _p2 =
  rev_elems 64 8 (BitVec.extractLsb' 0 64 x) _p3 _p4 ++ rev_elems 64 8 (BitVec.extractLsb' 64 64 x) _p5 _p6 := by
  sorry

-- v4.27: PARKED — same v4.27 rev_elems recursion/term-size regression (see above).
set_option maxHeartbeats 1000000 in
theorem rev_elems_64_8_append_eq_rev_elems_128_8 (x y : BitVec 64) :
  rev_elems 64 8 x _p1 _p2 ++ rev_elems 64 8 y _p3 _p4 =
  rev_elems 128 8 (y ++ x) _p5 _p6 := by
  sorry

-- v4.29: the old `rw [extractLsb'_append]; simp_all (ground) [bitvec_rules]; congr`
-- recipe broke — v4.29's `congr` over-decomposes and leaves impossible residual
-- goals (`64 = 0`). These are concrete BitVec identities, so close them directly
-- with `bv_decide`. (Only consumed by the parked `gcm_gmult_v8_program_run_27`.)
private theorem lsb_from_extractLsb'_of_append_self (x : BitVec 128) :
  BitVec.extractLsb' 64 64 (BitVec.extractLsb' 64 128 (x ++ x)) =
  BitVec.extractLsb' 0 64 x := by
  bv_decide

private theorem msb_from_extractLsb'_of_append_self (x : BitVec 128) :
  BitVec.extractLsb' 0 64 (BitVec.extractLsb' 64 128 (x ++ x)) =
  BitVec.extractLsb' 64 64 x := by
  bv_decide

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
    -- v4.16: ext lemma gives Nat index + bound `hi`; introduce both, drop `Fin.is_lt`.
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, hi, decide_true, BitVec.getLsbD_ushiftRight,
      Bool.true_and, BitVec.getLsbD_extractLsb']
  simp_all only


/-
(TODO) Need a lemma like the following, which breaks up a polynomial
multiplication into four constituent ones, for normalization.
-/
example :
  let p := 0b11#2
  let q := 0b10#2
  let x := 0b01#2
  let y := 0b01#2
  (DPSFP.polynomial_mult
        (p ++ q)
        (x ++ y))
  =
  ((DPSFP.polynomial_mult p x) ++ 0#4) ^^^
  (0#4 ++ (DPSFP.polynomial_mult q y)) ^^^
  (0#2 ++ (DPSFP.polynomial_mult p y) ++ 0#2) ^^^
  (0#2 ++ (DPSFP.polynomial_mult q x) ++ 0#2) := by native_decide

def pmult_test_1 : IO Bool := do
  let p ← BitVec.rand 64
  let q ← BitVec.rand 64
  let x ← BitVec.rand 64
  let y ← BitVec.rand 64
  pure
    (DPSFP.polynomial_mult (p ++ q) (x ++ y) ==
     ((DPSFP.polynomial_mult p x) ++ 0#128) ^^^
     (0#128 ++ (DPSFP.polynomial_mult q y)) ^^^
     (0#64 ++ (DPSFP.polynomial_mult p y) ++ 0#64) ^^^
     (0#64 ++ (DPSFP.polynomial_mult q x) ++ 0#64))

/--
info: true
-/
#guard_msgs in
#eval pmult_test_1

theorem DPSFP.polynomial_mult_append {p q x y : BitVec 64} :
  DPSFP.polynomial_mult (p ++ q) (x ++ y) =
  ((DPSFP.polynomial_mult p x) ++ 0#128) ^^^
   (0#128 ++ (DPSFP.polynomial_mult q y)) ^^^
   (0#64 ++ (DPSFP.polynomial_mult p y) ++ 0#64) ^^^
   (0#64 ++ (DPSFP.polynomial_mult q x) ++ 0#64) := by
  sorry

/-
Source: Function `GCMInitV8` in `Specs/GCMV8.lean`:
Note that `H0` is the 128-bit HTable input to `gcm_gmult_v8`.

let H2 := GCMV8.gcm_polyval H0 H0
let H1 := ((hi H2) ^^^ (lo H2)) ++ ((hi H0) ^^^ (lo H0))
-/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 500000 in
set_option pp.deepTerms false in
set_option pp.deepTerms.threshold 50 in
-- set_option trace.simp_mem.info true in
#time theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    {H1_hi H1_lo H0_hi H0_lo : BitVec 64}
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_Xi : Xi = s0[read_gpr 64 0#5 s0, 16])
    (h_HTable_lo : H0_hi ++ H0_lo = s0[read_gpr 64 1#5 s0, 16])
    (h_HTable_hi : H1_hi ++ H1_lo = s0[read_gpr 64 1#5 s0 + 16#64, 16])
    -- (h_HTable : HTable = s0[read_gpr 64 1#5 s0, 32])
    -- (h_HTable_alt : HTable = H1_hi ++ H1_lo ++ H0_hi ++ H0_lo)
    (h_H1_low_64 : H1_lo = H0_hi ^^^ H0_lo)
    -- (h_H1 : HTable.extractLsb' 128 128 =
    --         let H0 := HTable.extractLsb' 0 128
    --         let H2 := GCMV8.gcm_polyval H0 H0
    --         let H0_hi := H0.extractLsb' 64 64
    --         let H0_lo := H0.extractLsb' 0 64
    --         let H2_hi := H2.extractLsb' 64 64
    --         let H2_lo := H2.extractLsb' 0 64
    --         ((H2_hi) ^^^ (H2_lo)) ++ ((H0_hi) ^^^ (H0_lo)))
    (h_mem_sep : Memory.Region.pairwiseSeparate
                 [(read_gpr 64 0#5 s0, 16),
                  (read_gpr 64 1#5 s0, 16),
                  (read_gpr 64 1#5 s0 + 16#64, 16)])
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    -- The final state is error-free.
    read_err sf = .None ∧
    -- The program is unmodified in `sf`.
    sf.program = gcm_gmult_v8_program ∧
    -- The stack pointer is still aligned in `sf`.
    CheckSPAlignment sf ∧
    -- The final state returns to the address in register `x30` in `s0`.
    read_pc sf = r (StateField.GPR 30#5) s0 ∧
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
              (H0_hi ++ H0_lo)
              (rev_elems 128 8 Xi (by decide) (by decide)))
            (by decide) (by decide) := by
  -- v4.27: PARKED. `sym_n 27` OOM-kills during elaboration on v4.27.0 (exit 137,
  -- peak ~34 GB and climbing past the 40 GB cap). This is the **sym_n memory
  -- blowup regression landing at v4.27** — the term-size the reference branch
  -- diagnosed at v4.31 (super-linear ~3×/step; un-reduced `ite`-width SIMD
  -- element sizes defeat AxEffects subterm-sharing so the effect DAG expands as
  -- a tree). BISECTION RESULT: this proof built green in 37s (part of the 9.6 GB
  -- whole-Proofs build) on v4.26.0 and OOMs at v4.27.0 — byte-identical body, so
  -- it is a pure toolchain regression at v4.27.
  --
  -- The proof was already `sorry`-terminated below (never fully closed — the RHS
  -- gcm_polyval reduction was a TODO), so parking the whole body loses no proven
  -- content. Full prior body preserved at tag `port-v4.26.0`. The real fix is
  -- restructuring the sym_n/AxEffects value-sharing (see memory notes
  -- `v431-symn-oom-widespread`, `gcm-gmult-symn-oom-v431`); re-enable when that lands.
  sorry
  done

end GCMGmultV8Program
