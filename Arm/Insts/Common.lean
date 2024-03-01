/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
import Arm.BitVec
import Arm.Memory

section Common

open Std.BitVec

----------------------------------------------------------------------

def AddWithCarry (x : BitVec n) (y : BitVec n) (carry_in : BitVec 1) : (BitVec n × PState) :=
  let carry_in_nat := Std.BitVec.toNat carry_in
  let unsigned_sum := Std.BitVec.toNat x + Std.BitVec.toNat y + carry_in_nat
  let signed_sum := Std.BitVec.toInt x + Std.BitVec.toInt y + carry_in_nat
  let result := (Std.BitVec.ofNat n unsigned_sum)
  have h: n - 1 - (n - 1) + 1 = 1 := by simp
  let N := h ▸ (extractLsb (n - 1) (n - 1) result)
  let Z := if result = (Std.BitVec.zero n) then 1#1 else 0#1
  let C := if Std.BitVec.toNat result = unsigned_sum then 0#1 else 1#1
  let V := if Std.BitVec.toInt result = signed_sum then 0#1 else 1#1
  (result, (make_pstate N Z C V))

def ConditionHolds (cond : BitVec 4) (pstate : PState) : Bool :=
  open PFlag in
  let result :=
    match (extractLsb 3 1 cond) with
      | 0b000#3 => pstate Z == 1#1
      | 0b001#3 => pstate C == 1#1
      | 0b010#3 => pstate N == 1#1
      | 0b011#3 => pstate V == 1#1
      | 0b100#3 => pstate C == 1#1 && pstate Z == 0#1
      | 0b101#3 => pstate N == pstate V
      | 0b110#3 => pstate N == pstate V && pstate Z == 0#1
      | 0b111#3 => true
  if (extractLsb 0 0 cond) = 1#1 && cond ≠ 0b1111#4 then
    not result
  else
    result

/-- Check correct stack pointer (SP) alignment for AArch64 state; returns
true when sp is aligned. -/
def CheckSPAlignment (s : ArmState) : Bool :=
  -- (FIXME) Incomplete specification: should also check PSTATE.EL
  -- after we model that.
  let sp := read_gpr 64 31#5 s
  -- If the low 4 bits of SP are 0, then it is divisible by 16 and
  -- 16-aligned.
  (extractLsb 3 0 sp) &&& 0xF#4 == 0#4

----------------------------------------------------------------------

inductive ShiftType where
  | LSL : ShiftType
  | LSR : ShiftType
  | ASR : ShiftType
  | ROR : ShiftType
deriving DecidableEq, Repr

instance : ToString ShiftType where toString a := toString (repr a)

def decode_shift (shift : BitVec 2) : ShiftType :=
  match shift with
  | 0b00 => ShiftType.LSL
  | 0b01 => ShiftType.LSR
  | 0b10 => ShiftType.ASR
  | 0b11 => ShiftType.ROR

def shift_reg (bv : BitVec n) (st : ShiftType) (sa : BitVec 6)
  : BitVec n :=
  match st with
  | ShiftType.LSL => Std.BitVec.shiftLeft bv sa.toNat
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
  if bv = Std.BitVec.zero n then 1#1 else 0#1

----------------------------------------------------------------------

inductive LogicalImmType where
  | AND : LogicalImmType
  | ORR : LogicalImmType
  | EOR : LogicalImmType
  | ANDS : LogicalImmType
deriving DecidableEq, Repr

instance : ToString LogicalImmType where toString a := toString (repr a)

def highest_set_bit (bv : BitVec n) : Option Nat := Id.run do
  let mut acc := none
  for i in List.reverse $ List.range n do
    if extractLsb i i bv = 1
    then acc := some i
         break
  return acc

def lowest_set_bit (bv : BitVec n) : Nat := Id.run do
  let mut acc := n
  for i in List.range n do
    if extractLsb i i bv == 1
    then acc := i
         break
  return acc

def invalid_bit_masks (immN : BitVec 1) (imms : BitVec 6) (immediate : Bool)
  (M : Nat) : Bool :=
  let len := highest_set_bit $ immN ++ ~~~imms
  match len with
  | none => true
  | some len =>
    if len < 1 ∧ M < (1 <<< len) then true
    else
      let levels := zeroExtend 6 (allOnes len)
      if immediate ∧ (imms &&& levels = levels) then true
      else
        let esize := 1 <<< len
        if esize * (M / esize) ≠ M then true else false

theorem option_get_bang_of_some [Inhabited α] (v : α) :
  Option.get! (some v) = v := by rfl

theorem M_divisible_by_esize_of_valid_bit_masks (immN : BitVec 1) (imms : BitVec 6)
  (immediate : Bool) (M : Nat):
  ¬ invalid_bit_masks immN imms immediate M →
  let len := highest_set_bit $ immN ++ ~~~imms
  let esize := 1 <<< len.get!
  esize * (M / esize) = M := by
    unfold invalid_bit_masks
    simp
    split
    . simp
    . simp_all; rw [option_get_bang_of_some]; split
      . simp
      . split
        . simp
        . simp
    done

-- Resources on Arm bitmask immediate:
--   https://developer.arm.com/documentation/dui0802/b/A64-General-Instructions/MOV--bitmask-immediate-
--   https://kddnewton.com/2022/08/11/aarch64-bitmask-immediates.html
-- Arm Implementation:
--   https://tiny.amazon.com/c57v7i1u/devearmdocuddi02023Sharaarc
def decode_bit_masks (immN : BitVec 1) (imms : BitVec 6) (immr : BitVec 6)
  (immediate : Bool) (M : Nat) : Option (BitVec M × BitVec M) :=
  if h0 : invalid_bit_masks immN imms immediate M then none
  else
    let len := Option.get! $ highest_set_bit $ immN ++ ~~~imms
    let levels := zeroExtend 6 (allOnes len)
    let s := imms &&& levels
    let r := immr &&& levels
    let diff := s - r
    let esize := 1 <<< len
    let d := extractLsb (len - 1) 0 diff
    let welem := zeroExtend esize (allOnes (s.toNat + 1))
    let telem := zeroExtend esize (allOnes (d.toNat + 1))
    let wmask := replicate (M/esize) $ rotateRight welem r.toNat
    let tmask := replicate (M/esize) telem
    have h : esize * (M / esize) = M := by
      apply M_divisible_by_esize_of_valid_bit_masks immN imms immediate M
      simp_all
    some (h ▸ wmask, h ▸ tmask)

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

@[simp]
def Vpart_read (n : BitVec 5) (part width : Nat) (s : ArmState) (H : width > 0)
  : BitVec width :=
  -- assert n >= 0 && n <= 31;
  -- assert part IN {0, 1};
  have h1: width - 1 + 1 = width := by omega
  have h2: (width * 2 - 1 - width + 1) = width := by omega
  if part == 0 then
    -- assert width < 128;
    h1 ▸ extractLsb (width-1) 0 $ read_sfp 128 n s
  else
    -- assert width IN {32,64};
    h2 ▸ extractLsb (width*2-1) width $ read_sfp 128 n s


@[simp]
def Vpart_write (n : BitVec 5) (part width : Nat) (val : BitVec width) (s : ArmState)
  : ArmState :=
  -- assert n >= 0 && n <= 31;
  -- assert part IN {0, 1};
  if part == 0 then
    -- assert width < 128
    write_sfp width n val s
  else
    -- assert width == 64
    let res := (extractLsb 63 0 val) ++ (read_sfp 64 n s)
    write_sfp 128 n res s

----------------------------------------------------------------------

@[simp]
def ldst_read (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
  if SIMD? then read_sfp width idx s else read_gpr width idx s

@[simp]
def ldst_write (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (val : BitVec width) (s : ArmState)
  : ArmState :=
  if SIMD? then write_sfp width idx val s else write_gpr width idx val s

----------------------------------------------------------------------

theorem hi_lo_diff_equal_esize (esize : Nat) (lo : Nat) (hi : Nat) 
  (h₀ : esize > 0) (h₁ : hi = lo + esize - 1):
  hi - lo + 1 = esize := by omega

theorem esize_gt_zero (size : Nat):
  8 <<< size > 0 := by
  simp_all only [ Nat.shiftLeft_eq, gt_iff_lt, Nat.zero_lt_succ
                , mul_pos_iff_of_pos_left, zero_lt_two, pow_pos]

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
    let element := Std.BitVec.zeroExtend esize x
    let rest_x := Std.BitVec.zeroExtend (n - esize) (x >>> esize)
    have h1 : esize <= n := by 
      simp at h0; exact Nat.le_of_lt h0; done
    have h2 : esize ∣ (n - esize) := by
      refine Nat.dvd_sub ?H h₀ ?h₂
      · exact h1
      · simp only [dvd_refl]
      done
    have ?term_lemma : n - esize < n := by exact Nat.sub_lt_self h₁ h1
    let rest_ans := rev_elems (n - esize) esize rest_x h2 h₁
    have h3 : (esize + (n - esize)) = n := by
      simp_all only [ge_iff_le, add_tsub_cancel_of_le, h1]
    h3 ▸ (element ++ rest_ans)
   termination_by rev_elems n esize x h₀ h₁ => n

example : rev_elems 4 4 0xA#4 (by decide) (by decide) = 0xA#4 := rfl
example : rev_elems 8 4 0xAB#8 (by decide) (by decide) = 0xBA#8 := rfl
example : rev_elems 8 4 (rev_elems 8 4 0xAB#8 (by decide) (by decide))
          (by decide) (by decide) = 0xAB#8 := by native_decide 

theorem rev_elems_base :
  rev_elems esize esize x h₀ h₁ = x := by
  unfold rev_elems; simp; done
 
/-- Divide a bv of width `datasize` into containers, each of size
`container_size`, and within a container, reverse the order of `esize`-bit
elements. -/
def rev_vector (datasize container_size esize : Nat) (x : BitVec datasize)
  (h₀ : 0 < esize) (h₁ : esize <= container_size) (h₂ : container_size <= datasize)
  (h₃ : esize ∣ container_size) (h₄ : container_size ∣ datasize) :
  BitVec datasize :=
  if h0 : datasize = container_size then
    h0 ▸ (rev_elems container_size esize (h0 ▸ x) h₃ h₀)
  else
    let container := Std.BitVec.zeroExtend container_size x
    let new_container := rev_elems container_size esize container h₃ h₀
    let new_datasize := datasize - container_size
    let rest_x := Std.BitVec.zeroExtend new_datasize (x >>> container_size)
    have h₄' : container_size ∣ new_datasize := by
      have h : container_size ∣ container_size := by simp
      exact Nat.dvd_sub h₂ h₄ h
    have h₂' : container_size <= new_datasize := by
      refine Nat.le_of_dvd ?h h₄'
      simp_all!; exact Ne.lt_of_le' h0 h₂
    have h1 : 0 < container_size := by exact Nat.lt_of_lt_of_le h₀ h₁
    have ?term_lemma : new_datasize < datasize := by exact Nat.sub_lt_self h1 h₂
    let rest_ans := rev_vector new_datasize container_size esize rest_x h₀ h₁ h₂' h₃ h₄'
    have h2 : new_datasize + container_size = datasize := by
        rw [Nat.sub_add_cancel h₂]
    h2 ▸ (rest_ans ++ new_container)
  termination_by rev_vector datasize container_size esize x _ _ _ _ _ => datasize

example : rev_vector 32 16 8 0xaabbccdd#32 (by decide)
          (by decide) (by decide) (by decide) (by decide) =
          0xbbaaddcc#32 := by
          native_decide

end Common
