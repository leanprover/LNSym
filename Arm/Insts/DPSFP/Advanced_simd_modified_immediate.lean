/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- MOVI, MVNI, ORR, BIC (Immediate, vector), and FMOV (vector, immediate) - Single/double-precision
-- Missing: FMOV (vector, immediate) - Half-precision

import Arm.Decode
import Arm.Insts.Common
import Arm.BitVec

----------------------------------------------------------------------

namespace DPSFP

open BitVec

inductive ImmediateOp where
  | MOVI : ImmediateOp
  | MVNI : ImmediateOp
  | ORR : ImmediateOp
  | BIC : ImmediateOp
deriving DecidableEq, Repr

instance : ToString ImmediateOp where toString a := toString (repr a)

def decode_immediate_op (cmode : BitVec 4) (op : BitVec 1) : ImmediateOp :=
  match_bv cmode ++ op with
  | [0, _xx:2, 00] => ImmediateOp.MOVI
  | [0, _xx:2, 01] => ImmediateOp.MVNI
  | [0, _xx:2, 10] => ImmediateOp.ORR
  | [0, _xx:2, 11] => ImmediateOp.BIC
  | [10, _x:1, 00] => ImmediateOp.MOVI
  | [10, _x:1, 01] => ImmediateOp.MVNI
  | [10, _x:1, 10] => ImmediateOp.ORR
  | [10, _x:1, 11] => ImmediateOp.BIC
  | [110, _x:1, 0] => ImmediateOp.MOVI
  | [110, _x:1, 1] => ImmediateOp.MVNI
  | [1110, _x:1] => ImmediateOp.MOVI
  | [11110] => ImmediateOp.MOVI
  -- | case [11111]
  | _ => ImmediateOp.MOVI

def AdvSIMDExpandImm (op : BitVec 1) (cmode : BitVec 4) (imm8 : BitVec 8) : BitVec 64 :=
  let cmode_high3 := extractLsb 3 1 cmode
  let cmode_low1 := lsb cmode 0
  match cmode_high3 with
  | 0b000#3 => replicate 2 $ BitVec.zero 24 ++ imm8
  | 0b001#3 => replicate 2 $ BitVec.zero 16 ++ imm8 ++ BitVec.zero 8
  | 0b010#3 => replicate 2 $ BitVec.zero 8 ++ imm8 ++ BitVec.zero 16
  | 0b011#3 => replicate 2 $ imm8 ++ BitVec.zero 24
  | 0b100#3 => replicate 4 $ BitVec.zero 8 ++ imm8
  | 0b101#3 => replicate 4 $ imm8 ++ BitVec.zero 8
  | 0b110#3 =>
    if cmode_low1 == 0 then
      replicate 2 $ BitVec.zero 16 ++ imm8 ++ allOnes 8
    else
      replicate 2 $ BitVec.zero 8 ++ imm8 ++ allOnes 16
  | _ =>
    if cmode_low1 == 0 && op == 0 then
      replicate 8 imm8
    else if cmode_low1 == 0 && op == 1 then
      let imm8a := replicate 8 $ lsb imm8 7
      let imm8b := replicate 8 $ lsb imm8 6
      let imm8c := replicate 8 $ lsb imm8 5
      let imm8d := replicate 8 $ lsb imm8 4
      let imm8e := replicate 8 $ lsb imm8 3
      let imm8f := replicate 8 $ lsb imm8 2
      let imm8g := replicate 8 $ lsb imm8 1
      let imm8h := replicate 8 $ lsb imm8 0
      imm8a ++ imm8b ++ imm8c ++ imm8d ++ imm8e ++ imm8f ++ imm8g ++ imm8h
    else if cmode_low1 == 1 && op == 0 then
      let imm32 := lsb imm8 7 ++ ~~~(lsb imm8 6) ++
                   (replicate 5 $ lsb imm8 6) ++
                   extractLsb 5 0 imm8 ++ BitVec.zero 19
      replicate 2 imm32
    else
      -- Assume not UsingAArch32()
      -- if UsingAArch32() then ReservedEncoding();
      lsb imm8 7 ++ ~~~(lsb imm8 6) ++
        (replicate 8 $ lsb imm8 6) ++ extractLsb 5 0 imm8 ++ BitVec.zero 48


private theorem mul_div_norm_form_lemma  (n m : Nat) (_h1 : 0 < m) (h2 : n ∣ m) :
  (n * (m / n)) = n * m / n := by
  rw [Nat.mul_div_assoc]
  simp only [h2]

@[state_simp_rules]
-- Assumes CheckFPAdvSIMDEnabled64();
def exec_advanced_simd_modified_immediate
  (inst : Advanced_simd_modified_immediate_cls) (s : ArmState) : ArmState :=
  if inst.cmode == 0b1111#4 && inst.op == 0b0#1 && inst.o2 == 0b1#1 then
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  else if inst.cmode == 0b1111#4 && inst.op == 0b1#1 && inst.Q == 0b0#1 || inst.o2 == 0b1#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 64 <<< inst.Q.toNat
    let operation := decode_immediate_op inst.cmode inst.op
    let imm8 := inst.a ++ inst.b ++ inst.c ++ inst.d ++ inst.e ++ inst.f ++ inst.g ++ inst.h
    let imm64 := AdvSIMDExpandImm inst.op inst.cmode imm8
    let imm := replicate (datasize/64) imm64
    have h₀ : 0 < datasize := by 
      simp [datasize]
      apply zero_lt_shift_left_pos (by decide)
    have h₁ : 64 ∣ datasize := by
      simp only [datasize, Nat.shiftLeft_eq, Nat.dvd_mul_right]
    have h : (64 * (datasize / 64)) = datasize := by 
      rw [mul_div_norm_form_lemma 64 datasize h₀ h₁]
      refine Nat.mul_div_cancel_left datasize ?H; decide
    let result := match operation with
                  | ImmediateOp.MOVI => (h ▸ imm)
                  | ImmediateOp.MVNI => ~~~(h ▸ imm)
                  | ImmediateOp.ORR =>
                    let operand := read_sfp datasize inst.Rd s
                    operand ||| (h ▸ imm)
                  | _ =>
                    let operand := read_sfp datasize inst.Rd s
                    operand &&& ~~~(h ▸ imm)
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp datasize inst.Rd result s
    s

----------------------------------------------------------------------

partial def Advanced_simd_modified_immediate_cls.nonfp.rand : IO (Option (BitVec 32)) := do
  let cmode := ← BitVec.rand 4
  let op := ← BitVec.rand 1
  let Q := ← BitVec.rand 1
  if cmode == 0b1111#4 && op == 0b1#1 && Q = 0b0#1 then
    Advanced_simd_modified_immediate_cls.nonfp.rand
  else
    let (inst : Advanced_simd_modified_immediate_cls) :=
      { Q     := Q,
        op    := op,
        a     := ← BitVec.rand 1,
        b     := ← BitVec.rand 1,
        c     := ← BitVec.rand 1,
        cmode := cmode,
        o2    := 0b0#1,
        d     := ← BitVec.rand 1,
        e     := ← BitVec.rand 1,
        f     := ← BitVec.rand 1,
        g     := ← BitVec.rand 1,
        h     := ← BitVec.rand 1,
        Rd    := ← BitVec.rand 5
      }
    pure (some inst.toBitVec32)

/-- Generate random instructions of Advanced_simd_modified_immediate class. -/
def Advanced_simd_modified_immediate_cls.rand : List (IO (Option (BitVec 32))) :=
  [ Advanced_simd_modified_immediate_cls.nonfp.rand ]

----------------------------------------------------------------------

end DPSFP
