/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
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
  let N := h ▸ (BitVec.extract result (n - 1) (n - 1))
  let Z := if result = (Std.BitVec.zero n) then 1#1 else 0#1
  let C := if Std.BitVec.toNat result = unsigned_sum then 0#1 else 1#1
  let V := if Std.BitVec.toInt result = signed_sum then 0#1 else 1#1
  (result, (make_pstate N Z C V))

def ConditionHolds (cond : BitVec 4) (pstate : PState) : Bool :=
  open PFlag in
  let result :=
    match (BitVec.extract cond 3 1) with
      | 0b000#3 => pstate Z == 1#1
      | 0b001#3 => pstate C == 1#1
      | 0b010#3 => pstate N == 1#1
      | 0b011#3 => pstate V == 1#1
      | 0b100#3 => pstate C == 1#1 && pstate Z == 0#1
      | 0b101#3 => pstate N == pstate V
      | 0b110#3 => pstate N == pstate V && pstate Z == 0#1
      | 0b111#3 => true
  if (BitVec.extract cond 0 0) = 1#1 && cond ≠ 0b1111#4 then
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
  (BitVec.extract sp 3 0) &&& 0xF#4 == 0#4

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


end Common
