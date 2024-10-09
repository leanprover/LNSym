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
import Arm.Insts.CosimM

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

@[state_simp_rules]
def decode_immediate_op (inst : Advanced_simd_modified_immediate_cls)
  (s : ArmState) : (Option ImmediateOp) × ArmState :=
  -- All UNALLOCATED cases when inst.o2 = 1
  if inst.o2 = 0b1#1 ∧ inst.cmode ++ inst.op ≠ 0b11110#5 then
    (none, write_err (StateError.Illegal s!"Illegal {inst} encountered!") s)
  else
    match_bv inst.cmode ++ inst.op with
    | [0, _xx:2, 00] => (some ImmediateOp.MOVI, s)
    | [0, _xx:2, 01] => (some ImmediateOp.MVNI, s)
    | [0, _xx:2, 10] => (some ImmediateOp.ORR, s)
    | [0, _xx:2, 11] => (some ImmediateOp.BIC, s)
    | [10, _x:1, 00] => (some ImmediateOp.MOVI, s)
    | [10, _x:1, 01] => (some ImmediateOp.MVNI, s)
    | [10, _x:1, 10] => (some ImmediateOp.ORR, s)
    | [10, _x:1, 11] => (some ImmediateOp.BIC, s)
    | [110, _x:1, 0] => (some ImmediateOp.MOVI, s)
    | [110, _x:1, 1] => (some ImmediateOp.MVNI, s)
    | [1110, _x:1] => (some ImmediateOp.MOVI, s)
    | [11110] => (some ImmediateOp.MOVI, s)
    -- | case [11111]
    | _ => if inst.Q = 0#1
           then (none, write_err (StateError.Illegal s!"Illegal {inst} encountered!") s)
           else (some ImmediateOp.MOVI, s)

def AdvSIMDExpandImm (op : BitVec 1) (cmode : BitVec 4) (imm8 : BitVec 8) : BitVec 64 :=
  let cmode_high3 := extractLsb' 1 3 cmode
  let cmode_low1 := lsb cmode 0
  match cmode_high3 with
  | 0b000#3 => replicate 2 $ BitVec.zero 24 ++ imm8
  | 0b001#3 => replicate 2 $ BitVec.zero 16 ++ imm8 ++ BitVec.zero 8
  | 0b010#3 => replicate 2 $ BitVec.zero 8 ++ imm8 ++ BitVec.zero 16
  | 0b011#3 => replicate 2 $ imm8 ++ BitVec.zero 24
  | 0b100#3 => replicate 4 $ BitVec.zero 8 ++ imm8
  | 0b101#3 => replicate 4 $ imm8 ++ BitVec.zero 8
  | 0b110#3 =>
    if cmode_low1 = 0 then
      replicate 2 $ BitVec.zero 16 ++ imm8 ++ allOnes 8
    else
      replicate 2 $ BitVec.zero 8 ++ imm8 ++ allOnes 16
  | _ =>
    if cmode_low1 = 0 ∧ op = 0 then
      replicate 8 imm8
    else if cmode_low1 = 0 ∧ op = 1 then
      let imm8a := replicate 8 $ lsb imm8 7
      let imm8b := replicate 8 $ lsb imm8 6
      let imm8c := replicate 8 $ lsb imm8 5
      let imm8d := replicate 8 $ lsb imm8 4
      let imm8e := replicate 8 $ lsb imm8 3
      let imm8f := replicate 8 $ lsb imm8 2
      let imm8g := replicate 8 $ lsb imm8 1
      let imm8h := replicate 8 $ lsb imm8 0
      imm8a ++ imm8b ++ imm8c ++ imm8d ++ imm8e ++ imm8f ++ imm8g ++ imm8h
    else if cmode_low1 = 1 ∧ op = 0 then
      let imm32 := lsb imm8 7 ++ ~~~(lsb imm8 6) ++
                   (replicate 5 $ lsb imm8 6) ++
                   extractLsb' 0 6 imm8 ++ BitVec.zero 19
      replicate 2 imm32
    else
      -- Assume not UsingAArch32()
      -- if UsingAArch32() then ReservedEncoding();
      lsb imm8 7 ++ ~~~(lsb imm8 6) ++
        (replicate 8 $ lsb imm8 6) ++ extractLsb' 0 6 imm8 ++ BitVec.zero 48

open Lean Meta Simp in
dsimproc [state_simp_rules] reduceAdvSIMDExpandImm (AdvSIMDExpandImm _ _ _) := fun e => do
  let_expr AdvSIMDExpandImm op cmode imm8 ← e | return .continue
  let some ⟨op_n, op⟩ ← getBitVecValue? op | return .continue
  let some ⟨cmode_n, cmode⟩ ← getBitVecValue? cmode | return .continue
  let some ⟨imm8_n, imm8⟩ ← getBitVecValue? imm8 | return .continue
  if h : op_n = 1 ∧ cmode_n = 4 ∧ imm8_n = 8 then
    return .done <| toExpr (AdvSIMDExpandImm
                              (BitVec.cast (by simp_all only) op)
                              (BitVec.cast (by simp_all only) cmode)
                              (BitVec.cast (by simp_all only) imm8))
  else return .continue

private theorem mul_div_norm_form_lemma  (n m : Nat) (_h1 : 0 < m) (h2 : n ∣ m) :
  (n * (m / n)) = n * m / n := by
  rw [Nat.mul_div_assoc]
  simp only [h2]

@[state_simp_rules]
-- Assumes CheckFPAdvSIMDEnabled64();
def exec_advanced_simd_modified_immediate
  (inst : Advanced_simd_modified_immediate_cls) (s : ArmState) : ArmState :=
  let (maybe_operation, s) := decode_immediate_op inst s
  match maybe_operation with
  | none => s
  | some operation =>
    let datasize := 64 <<< inst.Q.toNat
    let imm8 := inst.a ++ inst.b ++ inst.c ++ inst.d ++ inst.e ++ inst.f ++ inst.g ++ inst.h
    let imm16 : BitVec 16 :=
                 extractLsb' 7 1 imm8 ++ ~~~ (extractLsb' 6 1 imm8) ++
                 (replicate 2 $ extractLsb' 6 1 imm8) ++
                 extractLsb' 0 6 imm8 ++ BitVec.zero 6
    let imm64 := AdvSIMDExpandImm inst.op inst.cmode imm8
    have h₁ : 16 * (datasize / 16) = datasize := by omega
    have h₂ : 64 * (datasize / 64) = datasize := by omega
    -- Assumes IsFeatureImplemented(FEAT_FP16)
    let imm : BitVec datasize :=
      if inst.op ++ inst.cmode ++ inst.o2 = 0b011111#6
      then BitVec.cast h₁ $ replicate (datasize/16) imm16
      else BitVec.cast h₂ $ replicate (datasize/64) imm64
    let result := match operation with
                | ImmediateOp.MOVI => imm
                | ImmediateOp.MVNI => ~~~imm
                | ImmediateOp.ORR =>
                  let operand := read_sfp datasize inst.Rd s
                  operand ||| imm
                | _ =>
                  let operand := read_sfp datasize inst.Rd s
                  operand &&& ~~~imm
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp datasize inst.Rd result s
    s

----------------------------------------------------------------------

partial def Advanced_simd_modified_immediate_cls.all.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let cmode := ← BitVec.rand 4
  let op := ← BitVec.rand 1
  let Q := ← BitVec.rand 1
  let o2 := ← BitVec.rand 1
  if (cmode == 0b1111#4 && op == 0b1#1 && Q = 0b0#1) || (o2 == 0b1#1 && cmode ++ op != 0b11110#5) then
    Advanced_simd_modified_immediate_cls.all.rand
  else
    let (inst : Advanced_simd_modified_immediate_cls) :=
      { Q     := Q,
        op    := op,
        a     := ← BitVec.rand 1,
        b     := ← BitVec.rand 1,
        c     := ← BitVec.rand 1,
        cmode := cmode,
        o2    := o2,
        d     := ← BitVec.rand 1,
        e     := ← BitVec.rand 1,
        f     := ← BitVec.rand 1,
        g     := ← BitVec.rand 1,
        h     := ← BitVec.rand 1,
        Rd    := ← BitVec.rand 5
      }
    pure (some inst.toBitVec32)

/-- Generate random instructions of Advanced_simd_modified_immediate class. -/
def Advanced_simd_modified_immediate_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [ Advanced_simd_modified_immediate_cls.all.rand ]

----------------------------------------------------------------------

end DPSFP
