/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
def ldst_read (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
  if SIMD? then read_sfp width idx s else read_gpr width idx s

@[simp]
def ldst_write (SIMD? : Bool) (width : Nat) (idx : BitVec 5) (val : BitVec width) (s : ArmState)
  : ArmState :=
  if SIMD? then write_sfp width idx val s else write_gpr width idx val s

end Common
