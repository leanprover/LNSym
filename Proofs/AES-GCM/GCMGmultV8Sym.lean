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
  -- (v4.31) re-indented the flush-left tactic body under `:= by`.
  simp only [DPSFP.vrev128_64_8]
  unfold rev_vector
  simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
  unfold rev_vector
  simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
  exact rfl
  done

/-- XOR parity of `f 0`, `f 1`, ..., `f (n - 1)`, used to express each bit of a
carryless GF(2)[x] product as a convolution over input bit indices. -/
private def parityRange : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, f => parityRange n f ^^ f n

private theorem lsb_eq_one_iff {w : Nat} (x : BitVec w) (i : Nat) :
    BitVec.lsb x i = 1 ↔ x.getLsbD i = true := by
  constructor
  · intro h
    have hb := congrArg (fun b : BitVec 1 => b.getLsbD 0) h
    simpa [BitVec.lsb] using hb
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa [BitVec.lsb] using h

private theorem polynomial_mult_aux_bit (x : BitVec m) (y : BitVec (m+n)) (k : Nat)
    (hk : k < m+n) (i : Nat) (hi : i ≤ m) (acc : BitVec (m+n))
    (hacc : acc.getLsbD k = parityRange i
      (fun j => x.getLsbD j && (decide (j ≤ k) && y.getLsbD (k-j)))) :
    (DPSFP.polynomial_mult_aux i acc x y).getLsbD k =
      parityRange m (fun j => x.getLsbD j && (decide (j ≤ k) && y.getLsbD (k-j))) := by
  rw [DPSFP.polynomial_mult_aux]
  split
  · rename_i h
    exact (Nat.le_antisymm hi h) ▸ hacc
  · rename_i h
    apply polynomial_mult_aux_bit x y k hk (i+1) (by omega)
    rw [parityRange, ← hacc]
    by_cases hbit : x.getLsbD i = true
    · rw [ite_eq_left ((lsb_eq_one_iff x i).2 hbit), BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft]
      by_cases hki : i ≤ k
      · simp [hk, hbit, hki, show ¬ k < i by omega]
      · simp [hk, hbit, hki, show k < i by omega]
    · rw [ite_eq_right (fun h => hbit ((lsb_eq_one_iff x i).1 h))]
      simp [hbit]
termination_by m-i

private theorem polynomial_mult_bit (x : BitVec m) (y : BitVec n) (k : Nat) (hk : k < m+n) :
    (DPSFP.polynomial_mult x y).getLsbD k =
      parityRange m (fun i => x.getLsbD i && (decide (i ≤ k) && y.getLsbD (k-i))) := by
  unfold DPSFP.polynomial_mult
  have h := polynomial_mult_aux_bit x (y.zeroExtend (m+n)) k hk 0
    (Nat.zero_le _) 0 (by simp [parityRange])
  simpa [BitVec.zeroExtend, show ∀ i : Nat, k-i < m+n from fun i => by omega] using h

-- The coefficient at bit k is the parity of the products of input bits
-- whose indices sum to k. The two multiplication loops traverse opposite inputs.
private theorem pmultTR_bit (x y : BitVec 128) (i k : Nat) (hi : i ≤ 128) (hk : k < 255)
    (acc : BitVec 255) :
    (GCMV8.pmult.pmultTR (m := 127) (n := 127) x y i acc).getLsbD k =
      ((decide (i ≤ k) && acc.getLsbD (k-i)) ^^
        parityRange i (fun j => y.getLsbD j && (decide (j ≤ k) && x.getLsbD (k-j)))) := by
  induction i generalizing acc with
  | zero => simp [GCMV8.pmult.pmultTR, parityRange]
  | succ i ih =>
    have hyidx : y.getMsbD (128 - (i+1)) = y.getLsbD i := by
      rw [BitVec.getMsbD_eq_getLsbD]
      rw [show 128-1-(128-(i+1)) = i by omega,
        decide_eq_true (by omega : 128-(i+1) < 128), Bool.true_and]
    rw [GCMV8.pmult.pmultTR, ih (by omega), parityRange]
    simp only [hyidx]
    have hki : k-i < 255 := by omega
    by_cases h : i ≤ k
    · by_cases h' : i + 1 ≤ k
      · have hbit : ¬ k - i < 1 := by omega
        have hoff : k-i-1 = k-(i+1) := by omega
        have hidx : k - (i + 1) < 255 := by omega
        cases y.getLsbD i
        · simp [h, h', hki, hbit, hoff, BitVec.getLsbD_eq_getElem hidx]
        · simp [h, h', hki, hbit, hoff, BitVec.partInstall, BitVec.getLsbD_eq_getElem hidx,
            Bool.xor_left_comm, Bool.xor_comm]
      · have hz : k-i = 0 := by omega
        cases y.getLsbD i <;>
          simp [h, h', hz, BitVec.partInstall, Bool.xor_comm]
    · have h' : ¬ i+1 ≤ k := by omega
      simp [h,h']

private theorem polyval_bit_lt (x y : BitVec 128) (k : Nat) (hk : k < 255) :
    (GCMV8.gcm_polyval_mul x y).getLsbD k =
      parityRange 128 (fun j => y.getLsbD j && (decide (j ≤ k) && x.getLsbD (k-j))) := by
  change (0#1 ++ (GCMV8.pmult.pmultTR (m := 127) (n := 127) x y 128 0 : BitVec 255)).getLsbD k = _
  rw [BitVec.getLsbD_append, ite_eq_left hk]
  simpa using pmultTR_bit x y 128 k (by decide) hk 0

private theorem parity_head (n : Nat) (f : Nat → Bool) :
    parityRange (n + 1) f = (f 0 ^^ parityRange n (fun j => f (j + 1))) := by
  induction n with
  | zero => simp [parityRange]
  | succ n ih =>
    change (parityRange (n + 1) f ^^ f (n + 1)) = _
    rw [ih]
    exact Bool.xor_assoc _ _ _

private theorem parity_rev (n : Nat) (f : Nat → Bool) :
    parityRange n f = parityRange n (fun i => f (n - 1 - i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parity_head n (fun i => f (n + 1 - 1 - i))]
    change (parityRange n f ^^ f n) = _
    rw [ih, Bool.xor_comm]
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    congr 2
    funext i
    congr 1
    omega

private theorem parity_trim {a b : Nat} (f : Nat → Bool) (hab : a ≤ b)
    (hz : ∀ i, a ≤ i → f i = false) : parityRange b f = parityRange a f := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    rw [ha]
  | succ b ih =>
    by_cases he : a = b + 1
    · rw [he]
    · have h : a ≤ b := by omega
      change (parityRange b f ^^ f b) = _
      rw [hz _ h, Bool.xor_false, ih h]

private theorem parity_prefix_eq {n : Nat} (f g : Nat → Bool)
    (h : ∀ i, i < n → f i = g i) : parityRange n f = parityRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (parityRange n f ^^ f n) = (parityRange n g ^^ g n)
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem convolution_sym {w : Nat} (x y : BitVec w) (k : Nat) :
    parityRange w (fun i => x.getLsbD i && (decide (i ≤ k) && y.getLsbD (k-i))) =
    parityRange w (fun i => y.getLsbD i && (decide (i ≤ k) && x.getLsbD (k-i))) := by
  let term (v z : BitVec w) (i : Nat) := v.getLsbD i && (decide (i ≤ k) && z.getLsbD (k-i))
  have resize (v z : BitVec w) : parityRange w (term v z) = parityRange (k+1) (term v z) := by
    by_cases h : w ≤ k + 1
    · symm
      exact parity_trim _ h (fun i hi => by simp [term, BitVec.getLsbD_of_ge _ _ hi])
    · apply parity_trim _ (by omega)
      intro i hi
      have hn : ¬ i ≤ k := by omega
      simp [term, hn]
  change parityRange w (term x y) = parityRange w (term y x)
  rw [resize x y, resize y x, parity_rev _ (term x y)]
  apply parity_prefix_eq
  intro i hi
  have h₁ : i ≤ k := by omega
  have h₂ : k - i ≤ k := by omega
  have h₃ : k - (k - i) = i := by omega
  simp [term, h₁, h₂, h₃, Bool.and_comm]

private theorem polyval_bit (x y : BitVec 128) (k : Nat) (hk : k < 256) :
    (GCMV8.gcm_polyval_mul x y).getLsbD k =
      parityRange 128 (fun j => y.getLsbD j && (decide (j ≤ k) && x.getLsbD (k-j))) := by
  by_cases h : k < 255
  · exact polyval_bit_lt x y k h
  · have e : k = 255 := by omega
    subst k
    have hz (j : Nat) : (y.getLsbD j && (decide (j ≤ 255) && x.getLsbD (255-j))) = false := by
      by_cases hj : j < 128
      · simp [BitVec.getLsbD_of_ge x _ (by omega : 128 ≤ 255-j)]
      · simp [BitVec.getLsbD_of_ge y _ (by omega : 128 ≤ j)]
    rw [parity_trim (a := 0) _ (by decide) (fun j _ => hz j)]
    change ((0#1 ++ (GCMV8.pmult x y : BitVec 255)).getLsbD 255) = false
    rw [BitVec.getLsbD_append]
    rfl

-- (TODO) Should we simply replace one function by the other here?
theorem gcm_polyval_mul_eq_polynomial_mult {x y : BitVec 128} :
  GCMV8.gcm_polyval_mul x y = DPSFP.polynomial_mult x y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [polyval_bit x y k hk, polynomial_mult_bit x y k hk]
  exact convolution_sym y x k

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
  -- (v4.35) unfold `rev_elems` one step at a time instead of `repeat unfold` +
  -- ground `simp`, which overflows the recursion limit since v4.27.
  simp (disch := decide) only [rev_elems_step, rev_elems_base, Nat.reduceSub]
  bv_decide

theorem rev_elems_64_8_append_eq_rev_elems_128_8 (x y : BitVec 64) :
  rev_elems 64 8 x _p1 _p2 ++ rev_elems 64 8 y _p3 _p4 =
  rev_elems 128 8 (y ++ x) _p5 _p6 := by
  -- (v4.35) unfold `rev_elems` one step at a time instead of `repeat unfold` +
  -- ground `simp`, which overflows the recursion limit since v4.27.
  simp (disch := decide) only [rev_elems_step, rev_elems_base, Nat.reduceSub]
  bv_decide

-- v4.29: the old `rw [extractLsb'_append]; simp_all (ground) [bitvec_rules]; congr`
-- recipe broke — v4.29's `congr` over-decomposes and leaves impossible residual
-- goals (`64 = 0`). These are concrete BitVec identities, so close them directly
-- with `bv_decide`. (Only consumed by `gcm_gmult_v8_program_run_27`.)
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

-- Bit-level parity-splitting helpers for decomposing 128-bit `DPSFP.polynomial_mult`
-- into four shifted 64-bit schoolbook products.
private theorem appendParity_false (n : Nat) (f : Nat → Bool)
    (h : ∀ i < n, f i = false) : parityRange n f = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [parityRange, ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem appendParity_xor (n : Nat) (f g : Nat → Bool) :
    (parityRange n f ^^ parityRange n g) = parityRange n (fun i => f i ^^ g i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [parityRange, ← ih]
    cases parityRange n f <;> cases parityRange n g <;> cases f n <;> cases g n <;> decide

private theorem appendParity_split (a b : Nat) (f : Nat → Bool) :
    parityRange (a+b) f = (parityRange a f ^^ parityRange b (fun i => f (a+i))) := by
  induction b with
  | zero => simp [parityRange]
  | succ b ih =>
    change (parityRange (a+b) f ^^ f (a+b)) =
      (parityRange a f ^^ (parityRange b (fun i => f (a+i)) ^^ f (a+b)))
    rw [ih, Bool.xor_assoc]

private def splitTerm (u v : BitVec 64) (off k i : Nat) : Bool :=
  if off+i ≤ k ∧ k < off+i+64 then u.getLsbD i && v.getLsbD (k-(off+i)) else false

private theorem shifted_polynomial_bit (u v : BitVec 64) (off k : Nat) :
    (decide (off ≤ k) && (DPSFP.polynomial_mult u v).getLsbD (k-off)) =
      parityRange 64 (splitTerm u v off k) := by
  by_cases h : off ≤ k
  · simp only [h, decide_true, Bool.true_and]
    by_cases hb : k - off < 128
    · rw [polynomial_mult_bit u v (k-off) hb]
      apply parity_prefix_eq
      intro i hi
      by_cases hlo : off+i ≤ k
      · have hil : i ≤ k-off := by omega
        have eqn : k-off-i = k-(off+i) := by omega
        by_cases hhi : k < off+i+64
        · simp [splitTerm, hlo, hhi, hil, eqn]
        · have hg : 64 ≤ k-(off+i) := by omega
          simp [splitTerm, hlo, hhi, hil, eqn, BitVec.getLsbD_of_ge _ _ hg]
      · simp [splitTerm, hlo, show ¬ i ≤ k-off by omega]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      symm
      apply appendParity_false
      intro i hi
      simp [splitTerm, show ¬ k < off+i+64 by omega]
  · simp only [h, decide_false, Bool.false_and]
    symm
    apply appendParity_false
    intro i hi
    simp [splitTerm, show ¬ off+i ≤ k by omega]

private theorem splitTerm_append (u x y : BitVec 64) (off k i : Nat) :
    (u.getLsbD i && (decide (off+i ≤ k) && (x ++ y).getLsbD (k-(off+i)))) =
      (splitTerm u y off k i ^^ splitTerm u x (off+64) k i) := by
  rw [BitVec.getLsbD_append]
  have off' : off+64+i = off+i+64 := by omega
  by_cases h₀ : off+i ≤ k
  · by_cases h₁ : k < off+i+64
    · simp [splitTerm, h₀, h₁, off', show k-(off+i) < 64 by omega,
        show ¬ off+i+64 ≤ k by omega]
    · have h₁' : off+i+64 ≤ k := by omega
      have e : k-(off+i)-64 = k-(off+i+64) := by omega
      by_cases h₂ : k < off+i+64+64
      · simp [splitTerm, h₀, h₁, h₁', h₂, off', e, show ¬ k-(off+i) < 64 by omega]
      · have hg : 64 ≤ k-(off+i+64) := by omega
        simp [splitTerm, h₀, h₁, h₁', h₂, off', e, show ¬ k-(off+i) < 64 by omega,
          BitVec.getLsbD_of_ge _ _ hg]
  · simp [splitTerm, h₀, off', show ¬ off+i+64 ≤ k by omega]

private theorem append_high_bit (z : BitVec 128) (k : Nat) :
    (z ++ 0#128).getLsbD k = (decide (128 ≤ k) && z.getLsbD (k-128)) := by
  rw [BitVec.getLsbD_append]
  by_cases h : k < 128
  · simp [h, show ¬ 128 ≤ k by omega]
  · simp [h, show 128 ≤ k by omega]

private theorem append_low_bit (z : BitVec 128) (k : Nat) :
    (0#128 ++ z).getLsbD k = (decide (0 ≤ k) && z.getLsbD (k-0)) := by
  rw [BitVec.getLsbD_append]
  by_cases h : k < 128
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge z k (by omega)]

private theorem append_mid_bit (z : BitVec 128) (k : Nat) :
    (0#64 ++ z ++ 0#64).getLsbD k = (decide (64 ≤ k) && z.getLsbD (k-64)) := by
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]
  by_cases h : k < 64
  · simp [h, show ¬ 64 ≤ k by omega]
  · simp only [h, ↓reduceIte, show 64 ≤ k by omega, decide_true, Bool.true_and]
    by_cases h' : k-64 < 128
    · simp [h']
    · simp [h', BitVec.getLsbD_of_ge z (k-64) (by omega)]

theorem DPSFP.polynomial_mult_append {p q x y : BitVec 64} :
  DPSFP.polynomial_mult (p ++ q) (x ++ y) =
  ((DPSFP.polynomial_mult p x) ++ 0#128) ^^^
   (0#128 ++ (DPSFP.polynomial_mult q y)) ^^^
   (0#64 ++ (DPSFP.polynomial_mult p y) ++ 0#64) ^^^
   (0#64 ++ (DPSFP.polynomial_mult q x) ++ 0#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_xor]
  rw [append_high_bit (_root_.DPSFP.polynomial_mult p x) k,
    append_low_bit (_root_.DPSFP.polynomial_mult q y) k,
    append_mid_bit (_root_.DPSFP.polynomial_mult p y) k,
    append_mid_bit (_root_.DPSFP.polynomial_mult q x) k,
    shifted_polynomial_bit p x 128 k, shifted_polynomial_bit q y 0 k,
    shifted_polynomial_bit p y 64 k, shifted_polynomial_bit q x 64 k]
  rw [polynomial_mult_bit _ _ k hk, appendParity_split 64 64]
  simp only [appendParity_xor]
  apply parity_prefix_eq
  intro i hi
  have hi' : ¬64 + i < 64 := by omega
  rw [BitVec.getLsbD_append (x := p) (y := q) (i := i), ite_eq_left hi,
    BitVec.getLsbD_append (x := p) (y := q) (i := 64+i), ite_eq_right hi',
    show 64+i-64 = i by omega]
  have low := splitTerm_append q x y 0 k i
  simp only [Nat.zero_add] at low
  rw [low, splitTerm_append p x y 64 k i]
  change (splitTerm q y 0 k i ^^ splitTerm q x 64 k i ^^
    (splitTerm p y 64 k i ^^ splitTerm p x 128 k i)) = _
  cases splitTerm q y 0 k i <;> cases splitTerm q x 64 k i <;>
    cases splitTerm p y 64 k i <;> cases splitTerm p x 128 k i <;> decide

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
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- simp only [Nat.reduceMul] at Xi HTable
  simp only [Nat.reduceMul] at Xi
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 27
  -- Epilogue
  -- simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  simp only [memory_rules] at *
  sym_aggregate
  -- Split conjunction
  repeat' apply And.intro
  -- · simp_mem; rfl
  · simp only [List.mem_cons, List.mem_singleton, not_or, and_imp] at *
    sym_aggregate
  · intro n addr h_separate
    conv =>
      lhs
      simp_mem sep with [h_separate]
  · clear_named [h_s, stepi_]
    clear s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26

    -- Simplifying the LHS
    simp only [←h_Xi]
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

    simp only [GCMV8.GCMGmultV8_alt,
               GCMV8.lo, GCMV8.hi,
               GCMV8.gcm_polyval,
               ←h_HTable_lo, ←h_HTable_hi,
               ←h_Xi_rev, h_Xi_lower_rev, h_Xi_upper_rev]
    simp only [pmull_op_e_0_eize_64_elements_1_size_128_eq, gcm_polyval_mul_eq_polynomial_mult]
    simp only [zeroExtend_allOnes_lsh_64, zeroExtend_allOnes_lsh_0]
    rw [BitVec.extractLsb'_64_128_of_appends]
    rw [BitVec.xor_append]
    repeat rw [BitVec.extractLsb'_append_right]
    repeat rw [BitVec.extractLsb'_append_left]
    repeat rw [BitVec.extractLsb'_zero_extractLsb'_of_le (by decide)]
    repeat rw [BitVec.extractLsb'_extractLsb'_zero_of_le (by decide)]
    rw [BitVec.and_high_to_extractLsb'_concat]

    rw [@vrev128_64_8_in_terms_of_rev_elems (by decide) (by decide) (by decide) (by decide)]
    rw [BitVec.extractLsb'_64_128_of_appends]
    rw [@rev_elems_64_8_append_eq_rev_elems_128_8 _ _ (by decide) (by decide) (by decide) (by decide)]
    apply eq_of_rev_elems_eq
    rw [@rev_elems_128_8_eq_rev_elems_64_8_extractLsb' _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [h_Xi_upper_rev, h_Xi_lower_rev]
    rw [BitVec.extractLsb'_append_eq]
    simp only [BitVec.truncate_eq_setWidth, Nat.reduceAdd, BitVec.shiftLeft_zero]

    simp [DPSFP.polynomial_mult_append]
    simp [GCMV8.gcm_polyval_red, GCMV8.irrepoly]

    generalize h_term_1 : DPSFP.polynomial_mult H0_lo Xi_lower_rev = term1
    generalize h_term_2 : DPSFP.polynomial_mult H0_hi Xi_upper_rev = term2

    -- (TODO) Can we remove `reverse` from `pmod` in the RHS?

    -- have h_reduce : (GCMV8.reduce 0x100000000000000000000000000000087#129 0x1#129) = 1#129 := by native_decide
    --
    -- simp only [GCMV8.gcm_polyval_red, GCMV8.irrepoly,
    --            GCMV8.pmod, GCMV8.pmod.pmodTR,
    --            GCMV8.reduce, GCMV8.degree, GCMV8.degree.degreeTR]
    -- simp only [Nat.reduceAdd, BitVec.ushiftRight_eq, BitVec.reduceExtracLsb',
    --   BitVec.reduceHShiftLeft, BitVec.reduceAppend, BitVec.reduceHShiftRight, BitVec.ofNat_eq_ofNat,
    --   BitVec.reduceEq, ↓reduceIte, Nat.sub_self, BitVec.ushiftRight_zero_eq, BitVec.reduceAnd,
    --   BitVec.toNat_ofNat, Nat.pow_one, Nat.reduceMod, Nat.mul_zero, Nat.add_zero, Nat.zero_mod,
    --   Nat.zero_add, Nat.sub_zero, Nat.mul_one, Nat.zero_mul, Nat.one_mul, Nat.reduceSub,
    --   BitVec.and_self, BitVec.zero_and, BitVec.reduceMul, BitVec.xor_zero, BitVec.mul_one,
    --   BitVec.zero_xor, Nat.add_one_sub_one, BitVec.one_mul, BitVec.reduceXOr]
    sorry
  done

end GCMGmultV8Program
