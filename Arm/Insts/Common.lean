/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng, Nathan Wetzler
-/

import Std.Tactic.BVDecide
import Arm.BitVec
import Arm.State
import Arm.Insts.CosimM

section Common

open BitVec

----------------------------------------------------------------------

/--
`GPRIndex.rand` picks a safe GPR index for Arm-based Apple platforms
i.e., one not reserved on them. Use this function instead of
`BitVec.rand` to pick an appropriate random index for a source and
destination GPR during cosimulations.

See "NOTE: Considerations for running cosimulations on Arm-based Apple
platforms" in Arm/Cosim.lean for details.
-/
partial def GPRIndex.rand (lo := 0) (hi := 31) :
  Cosim.CosimM (BitVec 5) := do
  if ← Cosim.darwin? then
    go lo hi
  else
    -- On non-Darwin machines, fall through to `BitVec.rand`.
    BitVec.rand 5 lo hi
  where go (lo hi : Nat) : IO (BitVec 5) := do
    let ans ← BitVec.rand 5 lo hi
    -- GPRs 18 and 29 are reserved on Apple Arm platforms.
    if ans ∈ [18#5, 29#5] then
      go lo hi
    else
      pure ans

----------------------------------------------------------------------

/--
Integer addition with carry input, returning result and NZCV flags.

Ref.:
https://developer.arm.com/documentation/ddi0602/2024-06/Shared-Pseudocode/shared-functions-integer?lang=en#impl-shared.AddWithCarry.3
-/
def AddWithCarry (x : BitVec n) (y : BitVec n) (carry_in : BitVec 1) :
  (BitVec n × PState) :=
  let carry_in_ext := zeroExtend (n + 1) carry_in
  let unsigned_sum :=
    (zeroExtend (n + 1) x) + (zeroExtend (n + 1) y) + carry_in_ext
  let signed_sum :=
    (signExtend (n + 1) x) + (signExtend (n + 1) y) + carry_in_ext
  let result := zeroExtend n unsigned_sum
  let N := lsb result (n - 1)
  let Z := if result = (BitVec.zero n) then 1#1 else 0#1
  let C := if zeroExtend (n + 1) result = unsigned_sum then 0#1 else 1#1
  let V := if signExtend (n + 1) result = signed_sum then 0#1 else 1#1
  (result, (make_pstate N Z C V))

/-- When the carry bit is `0`, `AddWithCarry x y 0 = x + y` -/
@[bitvec_rules, state_simp_rules]
theorem fst_AddWithCarry_eq_add (x : BitVec n) (y : BitVec n) :
  (AddWithCarry x y 0#1).fst = x + y := by
  simp  [AddWithCarry, setWidth_eq, setWidth_zero, setWidth_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_setWidth, toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]
  have : 2^n < 2^(n + 1) := by
    refine Nat.pow_lt_pow_of_lt (by omega) (by omega)
  have : x.toNat + y.toNat < 2^(n + 1) := by omega
  rw [Nat.mod_eq_of_lt this]

/-- When the carry bit is `1`, `AddWithCarry x y 1 = x - ~~~y` -/
@[bitvec_rules, state_simp_rules]
theorem fst_AddWithCarry_eq_sub_neg (x : BitVec n) (y : BitVec n) :
  (AddWithCarry x y 1#1).fst = x - ~~~y := by
  simp  [AddWithCarry, setWidth_eq, setWidth_zero, setWidth_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_setWidth, toNat_add, Nat.add_mod_mod, Nat.mod_add_mod, toNat_ofNat, Nat.pow_one,
    Nat.reduceMod, toNat_sub, toNat_not]
  simp only [show 2 ^ n - (2 ^ n - 1 - y.toNat) = 1 + y.toNat by omega]
  have : 2^n < 2^(n + 1) := by
    refine Nat.pow_lt_pow_of_lt (by omega) (by omega)
  have : x.toNat + y.toNat + 1 < 2^(n + 1) := by omega
  rw [Nat.mod_eq_of_lt this]
  congr 1
  omega

-- TODO: Is this rule helpful at all?
@[bitvec_rules]
theorem setWidth_eq_of_AddWithCarry :
  setWidth n (AddWithCarry x y carry_in).fst =
  (AddWithCarry x y carry_in).fst := by
  simp only [setWidth_eq]

/--
Return `true` iff `cond` currently holds

Ref.:
https://developer.arm.com/documentation/ddi0602/2024-06/Shared-Pseudocode/shared-functions-system?lang=en#impl-shared.ConditionHolds.1
-/
@[state_simp_rules]
def ConditionHolds (cond : BitVec 4) (s : ArmState) : Bool :=
  open PFlag in
  let N := read_flag N s
  let Z := read_flag Z s
  let C := read_flag C s
  let V := read_flag V s
  let result :=
    match (extractLsb' 1 3 cond) with
      | 0b000#3 => Z = 1#1           -- EQ or NE
      | 0b001#3 => C = 1#1           -- CS or CC
      | 0b010#3 => N = 1#1           -- MI or PL
      | 0b011#3 => V = 1#1           -- VS or VC
      | 0b100#3 => C = 1#1 ∧ Z = 0#1 -- HI or LS
      | 0b101#3 => N = V             -- GE or LT
      | 0b110#3 => N = V ∧ Z = 0#1   -- GT or LE
      | 0b111#3 => true              -- AL
  -- Condition flag values in the set 111x indicate always true
  -- Otherwise, invert condition if necessary.
  if (lsb cond 0) = 1#1 ∧ cond ≠ 0b1111#4 then
    not result
  else
    result

/-- `x > y` iff `(N = V) ∧ Z = 0` . -/
theorem sgt_iff_n_eq_v_and_z_eq_0_64 (x y : BitVec 64) :
  (((AddWithCarry x (~~~y) 1#1).snd.n = (AddWithCarry x (~~~y) 1#1).snd.v) ∧
   (AddWithCarry x (~~~y) 1#1).snd.z = 0#1) ↔ BitVec.slt y x := by
  simp [AddWithCarry, make_pstate, lsb]
  split
  · bv_decide
  · bv_decide

/-- `x > y` iff `(N = V) ∧ Z = 0` . -/
theorem sgt_iff_n_eq_v_and_z_eq_0_32 (x y : BitVec 32) :
  (((AddWithCarry x (~~~y) 1#1).snd.n = (AddWithCarry x (~~~y) 1#1).snd.v) ∧
   (AddWithCarry x (~~~y) 1#1).snd.z = 0#1) ↔ BitVec.slt y x := by
  simp [AddWithCarry, make_pstate, lsb]
  split
  · bv_decide
  · bv_decide

/-- `x ≤ y` iff `¬ ((N = V) ∧ (Z = 0))`. -/
theorem sle_iff_not_n_eq_v_and_z_eq_0_64 (x y : BitVec 64) :
  (¬(((AddWithCarry x (~~~y) 1#1).snd.n = (AddWithCarry x (~~~y) 1#1).snd.v) ∧
   (AddWithCarry x (~~~y) 1#1).snd.z = 0#1)) ↔ BitVec.sle x y := by
  simp [AddWithCarry, make_pstate, lsb]
  split
  · bv_decide
  · bv_decide

/-- `x ≤ y` iff `¬ ((N = V) ∧ (Z = 0))`. -/
theorem sle_iff_not_n_eq_v_and_z_eq_0_32 (x y : BitVec 32) :
  (¬(((AddWithCarry x (~~~y) 1#1).snd.n = (AddWithCarry x (~~~y) 1#1).snd.v) ∧
   (AddWithCarry x (~~~y) 1#1).snd.z = 0#1)) ↔ BitVec.sle x y := by
  simp [AddWithCarry, make_pstate, lsb]
  split
  · bv_decide
  · bv_decide

/--
`x = 0` iff `Z = 0`.
This is implemented by testing whether `x + (-1) + 1 = 0`
-/
theorem zero_iff_z_eq_one (x : BitVec 64) :
  ((AddWithCarry x 0xffffffffffffffff#64 0x1#1).snd.z = 1#1) ↔
  (x = 0#64) := by
  simp only [AddWithCarry, bitvec_rules, state_simp_rules]
  repeat split
  · bv_decide
  · bv_decide
  done


/-- `Aligned x a` witnesses that the bitvector `x` is `a`-bit aligned. -/
def Aligned (x : BitVec n) (a : Nat) : Prop :=
  extractLsb' 0 a x = BitVec.zero _

/-- We need to prove why the Aligned predicate is Decidable. -/
instance : Decidable (Aligned x a) := by
  cases a <;> simp only [Aligned] <;> infer_instance

theorem Aligned_BitVecSub_64_4 {x : BitVec 64} {y : BitVec 64}
  (x_aligned : Aligned x 4)
  (y_aligned : Aligned y 4)
  : Aligned (x - y) 4 := by
  simp_all only [Aligned, Nat.sub_zero, zero_eq]
  bv_decide

theorem Aligned_BitVecAdd_64_4 {x : BitVec 64} {y : BitVec 64}
  (x_aligned : Aligned x 4)
  (y_aligned : Aligned y 4)
  : Aligned (x + y) 4 := by
  simp_all only [Aligned, Nat.sub_zero, zero_eq]
  bv_decide

theorem Aligned_AddWithCarry_64_4 (x : BitVec 64) (y : BitVec 64) (carry_in : BitVec 1)
  (x_aligned : Aligned x 4)
  (y_carry_in_aligned : Aligned (BitVec.add (extractLsb' 0 4 y) (setWidth 4 carry_in)) 4)
  : Aligned (AddWithCarry x y carry_in).fst 4 := by
  unfold AddWithCarry Aligned at *
  simp_all only [Nat.sub_zero, zero_eq, add_eq]
  bv_decide

/-- Check correct stack pointer (SP) alignment for AArch64 state; returns
true when sp is aligned. -/
def CheckSPAlignment (s : ArmState) : Prop :=
  -- (FIXME) Incomplete specification: should also check PSTATE.EL
  -- after we model that.
  let sp := read_gpr 64 31#5 s
  -- If the low 4 bits of SP are 0, then it is divisible by 16 and
  -- 16-aligned.
  (Aligned sp 4)

/-- We need to prove why the CheckSPAlignment predicate is Decidable. -/
instance : Decidable (CheckSPAlignment s) := by unfold CheckSPAlignment; infer_instance

@[state_simp_rules]
theorem CheckSPAlignment_w_different_eq (h : StateField.GPR 31#5 ≠ fld) :
  CheckSPAlignment (w fld v s) = CheckSPAlignment s := by
  simp_all only [CheckSPAlignment, state_simp_rules, minimal_theory, bitvec_rules]

/-- A rewording of `CheckSPAlignment_w_different_eq` as an implication,
to be used by proof automation in `AxEffects` -/
theorem CheckSPAlignment_w_of_ne_sp_of (h : StateField.GPR 31#5 ≠ fld) :
    CheckSPAlignment s → CheckSPAlignment (w fld v s) := by
  simp only [CheckSPAlignment_w_different_eq h, imp_self]

@[state_simp_rules]
theorem CheckSPAlignment_of_w_sp :
  CheckSPAlignment (w (StateField.GPR 31#5) v s) = (Aligned v 4) := by
  simp_all only [CheckSPAlignment, state_simp_rules, minimal_theory, bitvec_rules]

/-- A rewording of `CheckSPAlignment_of_w_sp` as an implication,
to be used by proof automation in `AxEffects` -/
theorem CheckSPAlignment_w_sp_of (h : Aligned v 4) :
    CheckSPAlignment (w (StateField.GPR 31#5) v s) := by
  simpa only [CheckSPAlignment_of_w_sp] using h

@[state_simp_rules]
theorem CheckSPAlignment_write_mem_bytes_eq :
  CheckSPAlignment (write_mem_bytes n addr v s) = CheckSPAlignment s := by
  simp_all only [CheckSPAlignment, state_simp_rules, minimal_theory, bitvec_rules]

theorem CheckSPAlignment_write_mem_bytes_of :
  CheckSPAlignment s → CheckSPAlignment (write_mem_bytes n addr v s) := by
  simp only [CheckSPAlignment_write_mem_bytes_eq, imp_self]

@[state_simp_rules]
theorem CheckSPAlignment_AddWithCarry_64_4 (st : ArmState) (y : BitVec 64) (carry_in : BitVec 1)
  (x_aligned : CheckSPAlignment st)
  (y_carry_in_aligned : Aligned (BitVec.add (extractLsb' 0 4 y) (setWidth 4 carry_in)) 4)
  : Aligned (AddWithCarry (r (StateField.GPR 31#5) st) y carry_in).fst 4 := by
  simp_all only [CheckSPAlignment, read_gpr, setWidth_eq, Nat.sub_zero, add_eq,
    Aligned_AddWithCarry_64_4]

@[state_simp_rules]
theorem CheckSPAlignment_of_r_sp_eq {s s' : ArmState}
    (h_eq : r (StateField.GPR 31#5) s' = r (StateField.GPR 31#5) s)
    (h_sp : CheckSPAlignment s) :
    CheckSPAlignment s' := by
  simpa only [CheckSPAlignment, read_gpr, h_eq] using h_sp

@[state_simp_rules]
theorem CheckSPAlignment_of_r_sp_aligned {s : ArmState} {value}
    (h_eq : r (StateField.GPR 31#5) s = value)
    (h_aligned : Aligned value 4) :
    CheckSPAlignment s := by
  simp only [CheckSPAlignment, read_gpr, h_eq, setWidth_eq, h_aligned]

----------------------------------------------------------------------

inductive ShiftType where
  | LSL : ShiftType
  | LSR : ShiftType
  | ASR : ShiftType
  | ROR : ShiftType
deriving DecidableEq, Repr

instance : ToString ShiftType where toString a := toString (repr a)

@[state_simp_rules]
def decode_shift (shift : BitVec 2) : ShiftType :=
  match shift with
  | 0b00 => ShiftType.LSL
  | 0b01 => ShiftType.LSR
  | 0b10 => ShiftType.ASR
  | 0b11 => ShiftType.ROR

@[state_simp_rules]
def shift_reg (bv : BitVec n) (st : ShiftType) (sa : BitVec 6)
  : BitVec n :=
  match st with
  | ShiftType.LSL => bv <<< sa.toNat -- BitVec.shiftLeft operation
  | ShiftType.LSR => ushiftRight bv sa.toNat
  | ShiftType.ASR => sshiftRight bv sa.toNat
  | ShiftType.ROR => rotateRight bv sa.toNat

inductive LogicalShiftedRegType where
  | AND  : LogicalShiftedRegType
  | BIC  : LogicalShiftedRegType
  | ORR  : LogicalShiftedRegType
  | ORN  : LogicalShiftedRegType
  | EOR  : LogicalShiftedRegType
  | EON  : LogicalShiftedRegType
  | ANDS : LogicalShiftedRegType
  | BICS : LogicalShiftedRegType
deriving DecidableEq, Repr

instance : ToString LogicalShiftedRegType where toString a := toString (repr a)

def zero_flag_spec (bv : BitVec n) : BitVec 1 :=
  if bv = BitVec.zero n then 1#1 else 0#1

----------------------------------------------------------------------

inductive LogicalImmType where
  | AND : LogicalImmType
  | ORR : LogicalImmType
  | EOR : LogicalImmType
  | ANDS : LogicalImmType
deriving DecidableEq, Repr

instance : ToString LogicalImmType where toString a := toString (repr a)

/- Find the index of the most significant set bit, if any, in `bv`.
This function differs from the Arm's HighestSetBit
(https://developer.arm.com/documentation/ddi0602/2022-03/Shared-Pseudocode/Shared-Functions?lang=en#impl-shared.HighestSetBit.1)
because it returns `n` when no set bit is found, instead of returning `-1`.
-/
def highest_set_bit (bv : BitVec n) : Nat :=
  go (n - 1) bv where
  go (i : Nat) (bv : BitVec n) :=
    if lsb bv i = 1#1 then
      i
    else
      if i = 0 then
        n
      else
        go (i - 1) bv

/- Find the index of the least significant set bit, if any, in `bv`.
This function matches Arm's LowestSetBit
(https://developer.arm.com/documentation/ddi0602/2022-03/Shared-Pseudocode/Shared-Functions?lang=en#impl-shared.LowestSetBit.1)
-- it returns `n` when no set bit is found.
-/
def lowest_set_bit (bv : BitVec n) : Nat :=
  go 0 bv where
  go (i : Nat) (bv : BitVec n) :=
    if i >= n then
      n
    else
      if lsb bv i = 1#1 then
        i
      else
        go (i + 1) bv
  termination_by (n - i)

open Lean Meta Simp in
@[inline] def reduceFindSetBit (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → Nat) (e : Expr) : Lean.Meta.Simp.SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op v.value)

dsimproc [state_simp_rules] reduce_highest_set_bit (highest_set_bit _) :=
  reduceFindSetBit ``highest_set_bit 2 highest_set_bit

dsimproc [state_simp_rules] reduce_lowest_set_bit (lowest_set_bit _) :=
  reduceFindSetBit ``lowest_set_bit 2 lowest_set_bit

def invalid_bit_masks (immN : BitVec 1) (imms : BitVec 6) (immediate : Bool)
  (M : Nat) : Bool :=
  let inp := immN ++ ~~~imms
  let len := highest_set_bit inp
  if len = inp.width then
    -- If no set bit is found in `inp`, then `highest_set_bit` returns the width
    -- of `inp`.
    true
  else if len < 1 ∧ M < (1 <<< len) then
   true
  else
    let levels := setWidth 6 (allOnes len)
    if immediate ∧ (imms &&& levels = levels) then
      true
    else
      let esize := 1 <<< len
      if esize * (M / esize) ≠ M then true else false

open Lean Meta Simp in
dsimproc [state_simp_rules] reduceInvalidBitMasks (invalid_bit_masks _ _ _ _) := fun e => do
  let_expr invalid_bit_masks immN imms imm M ← e | return .continue
  let immN ← simp immN
  let imms ← simp imms
  let imm ← simp imm
  let M ← simp M
  let some ⟨immN_width, immN⟩ ← getBitVecValue? immN.expr | return .continue
  let some ⟨imms_width, imms⟩ ← getBitVecValue? imms.expr | return .continue
  if h : immN_width = 1 ∧ imms_width = 6 then
    let some M ← Nat.fromExpr? M.expr | return .continue
    return .done <|
        toExpr (invalid_bit_masks
                    (BitVec.cast (by simp_all only) immN)
                    (BitVec.cast (by simp_all only) imms)
                    imm.expr.isTrue
                    M)
  else return .continue

theorem M_divisible_by_esize_of_valid_bit_masks (immN : BitVec 1) (imms : BitVec 6)
  (immediate : Bool) (M : Nat):
  ¬ invalid_bit_masks immN imms immediate M →
  let len := highest_set_bit $ immN ++ ~~~imms
  let esize := 1 <<< len
  esize * (M / esize) = M := by
    unfold invalid_bit_masks
    simp only [Nat.lt_one_iff, ite_not, Bool.not_eq_true]
    split
    · simp only [Nat.reduceAdd, false_implies, Bool.true_eq_false]
    . simp_all only [Bool.ite_eq_false_distrib, ite_eq_left_iff, imp_false]
      split
      . simp only [Bool.true_eq_false, Nat.reduceAdd, false_implies]
      . split
        . simp only [Bool.true_eq_false, Nat.reduceAdd, false_implies]
        . simp only [Nat.reduceAdd, Bool.true_eq_false, imp_false,
            Decidable.not_not, imp_self]
    done

-- Resources on Arm bitmask immediate:
--   https://developer.arm.com/documentation/dui0802/b/A64-General-Instructions/MOV--bitmask-immediate-
--   https://kddnewton.com/2022/08/11/aarch64-bitmask-immediates.html
-- Arm Implementation:
--   https://developer.arm.com/documentation/ddi0602/2023-12/Shared-Pseudocode/aarch64-functions-bitmasks?lang=en#impl-aarch64.DecodeBitMasks.5
def decode_bit_masks (immN : BitVec 1) (imms immr : BitVec 6)
                     (immediate : Bool) (M : Nat) :
                     Option (BitVec M × BitVec M) :=
  if h0 : invalid_bit_masks immN imms immediate M then none
  else
    let len := Option.get! $ highest_set_bit $ immN ++ ~~~imms
    let levels := setWidth 6 (allOnes len)
    let s := imms &&& levels
    let r := immr &&& levels
    let diff := s - r
    let esize := 1 <<< len
    let d := extractLsb' 0 len diff
    let welem := setWidth esize (allOnes (s.toNat + 1))
    let telem := setWidth esize (allOnes (d.toNat + 1))
    let wmask := replicate (M/esize) $ rotateRight welem r.toNat
    let tmask := replicate (M/esize) telem
    have h : esize * (M / esize) = M := by
      apply M_divisible_by_esize_of_valid_bit_masks immN imms immediate M
      simp_all
    some (BitVec.cast h wmask, BitVec.cast h tmask)

open Lean Meta Simp in
dsimproc [state_simp_rules] reduceDecodeBitMasks (decode_bit_masks _ _ _ _ _) :=
  fun e => do
  let_expr decode_bit_masks immN imms immr imm M ← e | return .continue
  let immN ← simp immN
  let imms ← simp imms
  let immr ← simp immr
  let imm ← simp imm
  let M ← simp M
  let some ⟨immN_width, immN⟩ ← getBitVecValue? immN.expr | return .continue
  let some ⟨imms_width, imms⟩ ← getBitVecValue? imms.expr | return .continue
  let some ⟨immr_width, immr⟩ ← getBitVecValue? immr.expr | return .continue
  if h : immN_width = 1 ∧ imms_width = 6 ∧ immr_width = 6 then
    let some M ← Nat.fromExpr? M.expr | return .continue
    return .done <|
        toExpr (decode_bit_masks
                    (BitVec.cast (by simp_all only) immN)
                    (BitVec.cast (by simp_all only) imms)
                    (BitVec.cast (by simp_all only) immr)
                    imm.expr.isTrue
                    M)
  else return .continue

----------------------------------------------------------------------

inductive SIMDThreeSameLogicalType where
  | AND  : SIMDThreeSameLogicalType
  | BIC  : SIMDThreeSameLogicalType
  | ORR  : SIMDThreeSameLogicalType
  | ORN  : SIMDThreeSameLogicalType
  | EOR  : SIMDThreeSameLogicalType
  | BSL  : SIMDThreeSameLogicalType
  | BIT : SIMDThreeSameLogicalType
  | BIF : SIMDThreeSameLogicalType
deriving DecidableEq, Repr

instance : ToString SIMDThreeSameLogicalType where toString a := toString (repr a)

----------------------------------------------------------------------

@[state_simp_rules]
def Vpart_read (n : BitVec 5) (part width : Nat) (s : ArmState)
  : BitVec width :=
  -- assert n >= 0 && n <= 31;
  -- assert part IN {0, 1};
  if part = 0 then
    -- assert width < 128;
    extractLsb' 0 width $ read_sfp 128 n s
  else
    -- assert width IN {32,64};
    extractLsb' width width $ read_sfp 128 n s


@[state_simp_rules]
def Vpart_write (n : BitVec 5) (part width : Nat) (val : BitVec width) (s : ArmState)
  : ArmState :=
  -- assert n >= 0 && n <= 31;
  -- assert part IN {0, 1};
  if part = 0 then
    -- assert width < 128
    write_sfp width n val s
  else
    -- assert width == 64
    let res := (extractLsb' 0 64 val) ++ (read_sfp 64 n s)
    write_sfp 128 n res s

----------------------------------------------------------------------

@[state_simp_rules]
def ldst_read (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
  if SIMD? then read_sfp width idx s else read_gpr width idx s

@[state_simp_rules]
def ldst_write (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (val : BitVec width) (s : ArmState)
  : ArmState :=
  if SIMD? then write_sfp width idx val s else write_gpr width idx val s

----------------------------------------------------------------------

theorem zero_lt_shift_left_pos {x n : Nat} (h : 0 < x) :
  0 < x <<< n := by
  simp_all only [Nat.shiftLeft_eq, gt_iff_lt, Nat.zero_lt_succ,
  Nat.zero_lt_two, Nat.pow_pos, Nat.mul_pos_iff_of_pos_left]
  done

----------------------------------------------------------------------
----------------------------------------------------------------------

-- Floating-point convert/move instruction types
inductive FPConvOp where
  | FPConvOp_CVT_FtoI : FPConvOp
  | FPConvOp_CVT_ItoF : FPConvOp
  | FPConvOp_MOV_FtoI : FPConvOp
  | FPConvOp_MOV_ItoF : FPConvOp
  | FPConvOp_CVT_FtoI_JS : FPConvOp
deriving DecidableEq, Repr

----------------------------------------------------------------------

/-- Reverse the order of `esize`-bit elements in `x`.-/
def rev_elems (n esize : Nat) (x : BitVec n) (h₀ : esize ∣ n) (h₁ : 0 < esize) : BitVec n :=
  if h0 : n <= esize then
    x
  else
    let element := BitVec.setWidth esize x
    let rest_x := BitVec.setWidth (n - esize) (x >>> esize)
    have h1 : esize <= n := by
      simp at h0; exact Nat.le_of_lt h0; done
    have h2 : esize ∣ (n - esize) := by
      refine Nat.dvd_sub ?H h₀ ?h₂
      · exact h1
      · simp only [Nat.dvd_refl]
      done
    have ?term_lemma : n - esize < n := by exact Nat.sub_lt_self h₁ h1
    let rest_ans := rev_elems (n - esize) esize rest_x h2 h₁
    have h3 : (esize + (n - esize)) = n := by
      simp_all only [ge_iff_le, Nat.add_sub_cancel', h1]
    BitVec.cast h3 (element ++ rest_ans)
   termination_by n

example : rev_elems 4 4 0xA#4 (by decide) (by decide) = 0xA#4 := by
  native_decide
example : rev_elems 8 4 0xAB#8 (by decide) (by decide) = 0xBA#8 := by native_decide
example : rev_elems 8 4 (rev_elems 8 4 0xAB#8 (by decide) (by decide))
          (by decide) (by decide) = 0xAB#8 := by native_decide

theorem rev_elems_base :
  rev_elems esize esize x h₀ h₁ = x := by
  unfold rev_elems; simp only [Nat.le_refl, ↓reduceDIte]; done

/-- Divide a bv of width `datasize` into containers, each of size
`container_size`, and within a container, reverse the order of `esize`-bit
elements. -/
def rev_vector (datasize container_size esize : Nat) (x : BitVec datasize)
  (h₀ : 0 < esize) (h₁ : esize <= container_size) (h₂ : container_size <= datasize)
  (h₃ : esize ∣ container_size) (h₄ : container_size ∣ datasize) :
  BitVec datasize :=
  if h0 : container_size = datasize then
    BitVec.cast h0 (rev_elems container_size esize (BitVec.cast h0.symm x) h₃ h₀)
  else
    let container := BitVec.setWidth container_size x
    let new_container := rev_elems container_size esize container h₃ h₀
    let new_datasize := datasize - container_size
    let rest_x := BitVec.setWidth new_datasize (x >>> container_size)
    have h₄' : container_size ∣ new_datasize := by
      have h : container_size ∣ container_size := Nat.dvd_refl _
      exact Nat.dvd_sub h₂ h₄ h
    have h₂' : container_size <= new_datasize := by
      refine Nat.le_of_dvd ?h h₄'
      omega
    have h1 : 0 < container_size := by exact Nat.lt_of_lt_of_le h₀ h₁
    have ?term_lemma : new_datasize < datasize := by exact Nat.sub_lt_self h1 h₂
    let rest_ans := rev_vector new_datasize container_size esize rest_x h₀ h₁ h₂' h₃ h₄'
    have h2 : new_datasize + container_size = datasize := by
        rw [Nat.sub_add_cancel h₂]
    BitVec.cast h2 (rest_ans ++ new_container)
  termination_by datasize

example : rev_vector 32 16 8 0xaabbccdd#32 (by decide)
          (by decide) (by decide) (by decide) (by decide) =
          0xbbaaddcc#32 := by
          native_decide

----------------------------------------------------------------------

/-- Divide bv `vector` into elements, each of size `size`. This function gets
the `e`'th element from the `vector`. -/
@[state_simp_rules]
def elem_get (vector : BitVec n) (e : Nat) (size : Nat) : BitVec size :=
  -- assert (e+1)*size <= n
  let lo := e * size
  extractLsb' lo size vector

/-- Divide bv `vector` into elements, each of size `size`. This function sets
the `e`'th element in the `vector`. -/
@[state_simp_rules]
def elem_set (vector : BitVec n) (e : Nat) (size : Nat)
  (value : BitVec size) : BitVec n :=
  -- assert (e+1)*size <= n
  let lo := e * size
  BitVec.partInstall lo size value vector

----------------------------------------------------------------------

-- Field unsigned, round and accumulate are not used in left shifts
structure ShiftInfo where
  esize : Nat
  elements : Nat
  shift : Nat
  unsigned := true
  round := false
  accumulate := false
deriving DecidableEq, Repr

export ShiftInfo (esize elements shift unsigned round accumulate)

@[state_simp_rules]
def RShr (unsigned : Bool) (value : Int) (shift : Nat) (round : Bool)
  : BitVec n :=
  -- assert shift > 0
  let fn := if unsigned then ushiftRight else sshiftRight
  let rounded_bv :=
    if round then
      let rounded := value + (1 <<< (shift - 1))
      BitVec.ofInt (n + 1) rounded
    else
      BitVec.ofInt (n + 1) value
  extractLsb' 0 n (fn rounded_bv shift)

@[state_simp_rules]
def Int_with_unsigned (unsigned : Bool) (value : BitVec n) : Int :=
  if unsigned then Int.ofNat value.toNat else value.toInt

def shift_right_common_aux
  (e : Nat) (info : ShiftInfo) (operand : BitVec datasize)
  (operand2 : BitVec datasize) (result : BitVec datasize) : BitVec datasize :=
  if h : info.elements ≤ e then
    result
  else
    let elem := Int_with_unsigned info.unsigned $ elem_get operand e info.esize
    let shift_elem := RShr info.unsigned elem info.shift info.round
    let acc_elem := elem_get operand2 e info.esize + shift_elem
    let result := elem_set result e info.esize acc_elem
    have _ : info.elements - (e + 1) < info.elements - e := by omega
    shift_right_common_aux (e + 1) info operand operand2 result
  termination_by (info.elements - e)

-- FIXME: should this be upstreamed?
theorem shift_le (x : Nat) (shift :Nat) :
  x >>> shift ≤ x := by
  simp only [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self x (2 ^ shift)

set_option bv.ac_nf false

@[state_simp_rules]
theorem shift_right_common_aux_64_2_tff (operand : BitVec 128)
  (shift : Nat) (result : BitVec 128):
  shift_right_common_aux 0
    {esize := 64, elements := 2, shift := shift,
     unsigned := true, round := false, accumulate := false}
    operand 0#128 result =
  (ushiftRight (extractLsb' 64 64 operand) shift)
    ++ (ushiftRight (extractLsb' 0 64 operand) shift) := by
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  simp only [state_simp_rules,
             minimal_theory,
             -- FIXME: simply using bitvec_rules will expand out setWidth
             -- bitvec_rules,
             BitVec.cast_eq,
             Nat.shiftRight_zero,
             Nat.zero_shiftRight,
             Nat.reduceMul,
             Nat.reduceAdd,
             Nat.add_one_sub_one,
             Nat.sub_zero,
             reduceAllOnes,
             reduceZeroExtend,
             Nat.zero_mul,
             shiftLeft_zero_eq,
             reduceNot,
             BitVec.extractLsb_ofNat,
             Nat.reducePow,
             Nat.zero_mod,
             Int.ofNat_emod,
             Int.Nat.cast_ofNat_Int,
             BitVec.zero_add,
             Nat.reduceSub,
             Nat.one_mul,
             reduceHShiftLeft,
             -- FIXME: should partInstall be state_simp_rules?
             partInstall,
             -- Eliminating casting functions
             Int.ofNat_eq_coe, ofInt_natCast, ofNat_toNat
    ]
  generalize (extractLsb' 64 64 operand) = x
  generalize (extractLsb' 0 64 operand) = y
  have h0 : ∀ (z : BitVec 64), extractLsb' 0 64 ((zeroExtend 65 z).ushiftRight shift)
    = z.ushiftRight shift := by
    intro z
    simp only [ushiftRight, toNat_setWidth]
    have h1: z.toNat % 2 ^ 65 = z.toNat := by omega
    simp only [h1]
    simp only [Std.Tactic.BVDecide.Normalize.BitVec.ofNatLt_reduce]
    simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.extractLsb'_ofNat, Nat.shiftRight_zero]
    have h2 : z.toNat >>> shift % 2 ^ 65 = z.toNat >>> shift := by
      refine Nat.mod_eq_of_lt ?h3
      have h4 : z.toNat >>> shift ≤ z.toNat := by exact shift_le z.toNat shift
      omega
    simp only [h2]
  simp only [h0]
  clear h0
  generalize x.ushiftRight shift = p
  generalize y.ushiftRight shift = q
  -- FIXME: This proof can be simplified once bv_decide supports shift
  -- operations with variable offsets
  bv_decide

-- FIXME: where to put this?
theorem ofInt_eq_signExtend (x : BitVec 32) :
  BitVec.ofInt 33 x.toInt = signExtend 33 x := by
  exact rfl

-- FIXME: where to put this?
theorem msb_signExtend (x : BitVec n) (hw: n < n'):
      (signExtend n' x).msb = x.msb := by
  rcases n' with rfl | n'
  · simp only [show n = 0 by omega,
               msb_eq_getLsbD_last, Nat.zero_sub, Nat.le_refl,
               getLsbD_ge]
  · simp only [msb_eq_getLsbD_last, Nat.add_one_sub_one,
               getLsbD_signExtend, Nat.lt_add_one,
               decide_True, Bool.true_and, ite_eq_right_iff]
    by_cases h : n' < n
    · rcases n with rfl | n
      · simp
      · simp only [h, Nat.add_one_sub_one, true_implies]
        omega
    · simp [h]

theorem shift_right_common_aux_32_4_fff (operand : BitVec 128)
  (shift : Nat) (result : BitVec 128):
  shift_right_common_aux 0
    { esize := 32, elements := 4, shift := shift,
      unsigned := false, round := false, accumulate := false}
      operand 0#128 result =
  (sshiftRight (extractLsb' 96 32 operand) shift)
    ++ (sshiftRight (extractLsb' 64 32 operand) shift)
    ++ (sshiftRight (extractLsb' 32 32 operand) shift)
    ++ (sshiftRight (extractLsb' 0 32 operand) shift) := by
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_right_common_aux
  simp only [minimal_theory, bitvec_rules]
  simp only [state_simp_rules,
             minimal_theory,
             -- FIXME: simply using bitvec_rules will expand out setWidth
             -- bitvec_rules,
             BitVec.cast_eq,
             Nat.shiftRight_zero,
             Nat.zero_shiftRight,
             Nat.reduceMul,
             Nat.reduceAdd,
             Nat.add_one_sub_one,
             Nat.sub_zero,
             reduceAllOnes,
             reduceZeroExtend,
             Nat.zero_mul,
             shiftLeft_zero_eq,
             reduceNot,
             BitVec.extractLsb_ofNat,
             Nat.reducePow,
             Nat.zero_mod,
             Int.ofNat_emod,
             Int.Nat.cast_ofNat_Int,
             BitVec.zero_add,
             Nat.reduceSub,
             Nat.one_mul,
             reduceHShiftLeft,
             partInstall,
             -- Eliminating casting functions
             ofInt_eq_signExtend
    ]
  generalize extractLsb' 0 32 operand = a
  generalize extractLsb' 32 32 operand = b
  generalize extractLsb' 64 32 operand = c
  generalize extractLsb' 96 32 operand = d
  have h : ∀ (x : BitVec 32),
    extractLsb' 0 32 ((signExtend 33 x).sshiftRight shift)
    = x.sshiftRight shift := by
    intros x
    apply eq_of_getLsbD_eq; intros i; simp at i
    simp only [getLsbD_sshiftRight]
    simp only [Nat.sub_zero, Nat.reduceAdd, getLsbD_extractLsb', Nat.zero_add,
               getLsbD_sshiftRight, getLsbD_signExtend]
    simp only [show (i : Nat) < 32 by omega,
               decide_True, Bool.true_and]
    simp only [show ¬33 ≤ (i : Nat) by omega,
               decide_False, Bool.not_false, Bool.true_and]
    simp only [show ¬32 ≤ (i : Nat) by omega,
               decide_False, Bool.not_false, Bool.true_and]
    by_cases h : shift + (i : Nat) < 32
    · simp only [h, reduceIte]
      simp only [show shift + (i : Nat) < 33 by omega,
                 ↓reduceIte, decide_True, Bool.true_and]
    · simp only [h, reduceIte]
      have icases : shift + (i : Nat) = 32 ∨ 32 < shift + (i : Nat) := by omega
      rcases icases with (h' | h')
      · simp only [h', Nat.lt_add_one, ↓reduceIte, decide_True, Bool.true_and]
      · simp only [show ¬(shift + (i : Nat) < 33) by omega, ↓reduceIte]
        apply msb_signExtend; trivial
  simp only [h]
  clear h
  generalize a.sshiftRight shift = a
  generalize b.sshiftRight shift = b
  generalize c.sshiftRight shift = c
  generalize d.sshiftRight shift = d
  -- FIXME: This proof can be simplified once bv_decide supports shift
  -- operations with variable offsets
  bv_decide

@[state_simp_rules]
def shift_right_common
  (info : ShiftInfo) (datasize : Nat) (Rn : BitVec 5) (Rd : BitVec 5)
  (s : ArmState) : BitVec datasize :=
  let operand := read_sfp datasize Rn s
  let operand2 := if info.accumulate then read_sfp datasize Rd s else BitVec.zero datasize
  let result := BitVec.zero datasize
  shift_right_common_aux 0 info operand operand2 result

def shift_left_common_aux
  (e : Nat) (info : ShiftInfo) (operand : BitVec datasize)
  (result : BitVec datasize) : BitVec datasize :=
  if h : info.elements ≤ e then
    result
  else
    let elem := elem_get operand e info.esize
    let shift_elem := elem <<< info.shift
    let result := elem_set result e info.esize shift_elem
    have _ : info.elements - (e + 1) < info.elements - e := by omega
    shift_left_common_aux (e + 1) info operand result
  termination_by (info.elements - e)

theorem shift_left_common_aux_64_2 (operand : BitVec 128)
  (shift : Nat) (unsigned: Bool) (round : Bool) (accumulate : Bool)
  (result : BitVec 128):
  shift_left_common_aux 0
    {esize := 64, elements := 2, shift := shift,
     unsigned := unsigned, round := round, accumulate := accumulate}
    operand result =
  (extractLsb' 64 64 operand <<< shift)
    ++ (extractLsb' 0 64 operand <<< shift) := by
  unfold shift_left_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_left_common_aux
  simp only [minimal_theory, bitvec_rules]
  unfold shift_left_common_aux
  simp only [minimal_theory, bitvec_rules]
  simp only [state_simp_rules, minimal_theory, bitvec_rules, partInstall]
  bv_decide

@[state_simp_rules]
def shift_left_common
  (info : ShiftInfo) (datasize : Nat) (Rn : BitVec 5) (s : ArmState)
  : BitVec datasize :=
  let operand := read_sfp datasize Rn s
  let result := BitVec.zero datasize
  shift_left_common_aux 0 info operand result

----------------------------------------------------------------------

-- MemOp: Memory access instruction types
inductive MemOp where
  | MemOp_LOAD : MemOp
  | MemOp_STORE : MemOp
  | MemOp_PREFETCH : MemOp
deriving DecidableEq, Repr

----------------------------------------------------------------------

end Common
