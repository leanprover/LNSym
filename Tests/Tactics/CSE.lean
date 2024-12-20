/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

This file contains tests for the common subexpression elimination pass.
-/
import Arm.Insts.DPSFP.Insts
import Specs.SHA512
import Tactics.CSE


/- ### Test that CSE succeeds and counts subexpressions correctly.

We want to check that it correctly sees that there are:
- `16` occurrences of `y`,
- `8` occurrences of `y + y`,
- `4` occurrences of `(y + y) + (y + y)`.

-/

/--
warning: declaration uses 'sorry'
---
info: x y z x1 x2 : Nat
hx2 : y + y = x2
hx1 : x2 + x2 = x1
⊢ x + x + x1 = x1 + x1 + x1
-/
#guard_msgs in theorem many_subexpr (x y z : Nat) : (x + x) + ((y + y) + (y + y)) =
  (((y + y) + (y + y)) + ((y + y) + (y + y))) + (((y + y) + (y + y))) := by
  cse (config := {minOccsToCSE := 2})
  trace_state
  all_goals sorry


/- ### Test that generalize fails gracefully

In this test case, we try to generalize on `64`, which is a dependent index
of the type `BitVec 64`. Therefore, this should fail to generalize.
-/
/--
warning: declaration uses 'sorry'
---
info: y : Nat
x : BitVec (y + (y + 0))
⊢ BitVec.ofNat (y + y) (y + y) = x
-/
#guard_msgs in theorem generalize_failure (x : BitVec (y + (y + 0))) :
    (BitVec.ofNat (y + y) (y + y)) = x := by
  cse
  trace_state
  all_goals sorry

/- ### Test from SHA -/

open BitVec in
/--
warning: declaration uses 'sorry'
---
info: a b c d : BitVec 64
x1 x2 : BitVec 128
hx1 : x2 <<< 64 = x1
x3 : BitVec 64
hx3 : BitVec.extractLsb' 64 64 c = x3
hx2 : BitVec.zeroExtend 128 x3 = x2
⊢ BitVec.zeroExtend 128 (BitVec.extractLsb' 0 64 x1) ||| BitVec.zeroExtend 128 (BitVec.extractLsb' 64 64 x1) =
    sorryAx (BitVec 128)
-/

#guard_msgs in theorem bitvec_subexpr  (a b c d : BitVec 64) : (zeroExtend 128
              (extractLsb' 0 64
                  (
                    zeroExtend 128 (extractLsb' 64 64 c) <<< 64)) |||
          zeroExtend 128
              (extractLsb' 64 64
                  (zeroExtend 128 (extractLsb' 64 64 c) <<< 64))) = sorry := by
  cse
  trace_state
  all_goals sorry


namespace SHA

open BitVec sha512_helpers DPSFP SHA2 in
/--
warning: declaration uses 'sorry'
---
info: a b c d e : BitVec 128
x1 x2 x3 : BitVec 64
x4 : BitVec 128
hx3 : BitVec.extractLsb' 64 64 x4 = x3
x5 x6 x7 x8 x9 : BitVec 64
hx2 : x9 + x3 = x2
x10 x11 : BitVec 128
hx4 : x11 ||| x10 = x4
x12 : BitVec 128
hx11 : x12 &&& 18446744073709551615#128 = x11
x13 : BitVec 128
hx10 : x13 <<< 64 = x10
x14 : BitVec 64
hx12 : BitVec.zeroExtend 128 x14 = x12
x15 : BitVec 64
hx13 : BitVec.zeroExtend 128 x15 = x13
x16 x17 : BitVec 64
x18 : BitVec 128
hx16 : BitVec.extractLsb' 64 64 x18 = x16
hx17 : BitVec.extractLsb' 0 64 x18 = x17
x19 x20 : BitVec 64
hx8 : x19 + x20 = x8
x21 : BitVec 64
hx9 : x20 + x21 = x9
x22 : BitVec 64
x23 x24 : BitVec 128
hx18 : x24 ||| x23 = x18
x25 : BitVec 128
hx23 : x25 <<< 64 = x23
x26 : BitVec 64
x27 : BitVec 128
hx24 : x27 &&& 18446744073709551615#128 = x24
x28 : BitVec 64
hx20 : x28 ^^^ x26 = x20
x29 : BitVec 64
hx25 : BitVec.zeroExtend 128 x29 = x25
x30 : BitVec 64
hx27 : BitVec.zeroExtend 128 x30 = x27
x31 : BitVec 64
hx21 : x22 ^^^ x31 = x21
x32 x33 x34 : BitVec 64
hx22 : x34 ^^^ x33 = x22
x35 : BitVec 64
hx35 : BitVec.extractLsb' 64 64 a = x35
hx26 : x32 &&& x35 = x26
x36 : BitVec 64
hx36 : BitVec.extractLsb' 64 64 e = x36
hx6 : x7 + x36 = x6
hx15 : x16 + x36 = x15
x37 : BitVec 64
hx37 : BitVec.extractLsb' 0 64 a = x37
x38 : BitVec 64
hx38 : BitVec.extractLsb' 64 64 d = x38
hx7 : x8 + x38 = x7
x39 : BitVec 64
hx39 : BitVec.extractLsb' 0 64 c = x39
x40 : BitVec 64
hx40 : BitVec.extractLsb' 64 64 c = x40
hx19 : x40 + x21 = x19
hx29 : x40 + x38 = x29
x41 : BitVec 64
hx41 : BitVec.extractLsb' 0 64 b = x41
hx1 : x2 + x41 = x1
hx5 : x41 + x6 = x5
x42 : BitVec 64
hx42 : BitVec.extractLsb' 64 64 b = x42
hx31 : x42.rotateRight 41 = x31
hx32 : ~~~x42 = x32
hx33 : x42.rotateRight 18 = x33
hx34 : x42.rotateRight 14 = x34
hx28 : x42 &&& x37 = x28
x43 : BitVec 64
hx43 : BitVec.extractLsb' 0 64 e = x43
hx14 : x17 + x43 = x14
x44 : BitVec 64
hx44 : BitVec.extractLsb' 0 64 d = x44
hx30 : x39 + x44 = x30
⊢ x2 ++
      ((x1 &&& x42 ^^^ ~~~x1 &&& x37) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        BitVec.extractLsb' 0 64 x4) =
    x6 ++
      (x39 + (x5.rotateRight 14 ^^^ x5.rotateRight 18 ^^^ x5.rotateRight 41) + (x5 &&& x42 ^^^ ~~~x5 &&& x37) + x44 +
        x43)
-/
#guard_msgs in theorem sha512h_rule_1 (a b c d e : BitVec 128) :
  let elements := 2
  let esize := 64
  let inner_sum := (binary_vector_op_aux 0 elements esize BitVec.add c d (BitVec.zero 128))
  let outer_sum := (binary_vector_op_aux 0 elements esize BitVec.add inner_sum e (BitVec.zero 128))
  let a0 := extractLsb'  0 64 a
  let a1 := extractLsb' 64 64 a
  let b0 := extractLsb'  0 64 b
  let b1 := extractLsb' 64 64 b
  let c0 := extractLsb'  0 64 c
  let c1 := extractLsb' 64 64 c
  let d0 := extractLsb'  0 64 d
  let d1 := extractLsb' 64 64 d
  let e0 := extractLsb'  0 64 e
  let e1 := extractLsb' 64 64 e
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d1 e1
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d0 e0
  sha512h a b outer_sum = hi64_spec ++ lo64_spec := by
  simp_all! only [Nat.sub_zero];
  repeat (unfold binary_vector_op_aux elem_set elem_get; simp)
  unfold BitVec.partInstall
  unfold sha512h compression_update_t1 sigma_big_1 ch allOnes ror
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_zero, Nat.reducePow, reduceZeroExtend,
    reduceHShiftLeft, reduceNot, reduceAnd, BitVec.zero_or, shiftLeft_zero_eq]
  cse (config := { minOccsToCSE := 2, fuelSearch := 99999, fuelEliminate := 99999 })
  trace_state
  all_goals sorry

open BitVec in
private theorem and_nop_lemma (x : BitVec 64) :
  (zeroExtend 128 x) &&& 0xffffffffffffffff#128 = (zeroExtend 128 x) := by
  bv_decide

open BitVec sha512_helpers DPSFP SHA2 in
/--
warning: declaration uses 'sorry'
---
info: a b c d e : BitVec 128
x1 x2 x3 : BitVec 64
x4 : BitVec 128
hx3 : BitVec.extractLsb' 64 64 x4 = x3
x5 : BitVec 128
x6 : BitVec 64
x7 : BitVec 128
hx4 : x7 ||| x5 = x4
x8 : BitVec 128
hx5 : x8 <<< 64 = x5
x9 : BitVec 64
hx8 : BitVec.zeroExtend 128 x9 = x8
x10 : BitVec 64
hx7 : BitVec.zeroExtend 128 x10 = x7
x11 x12 x13 x14 : BitVec 64
x15 : BitVec 128
hx12 : BitVec.extractLsb' 64 64 x15 = x12
hx13 : BitVec.extractLsb' 0 64 x15 = x13
x16 : BitVec 256
hx15 : BitVec.extractLsb' 64 128 x16 = x15
x17 x18 : BitVec 64
hx2 : x18 + x3 = x2
x19 : BitVec 128
hx16 : x19 ++ x19 = x16
x20 x21 : BitVec 64
hx17 : x20 + x21 = x17
x22 : BitVec 64
hx18 : x21 + x22 = x18
x23 : BitVec 64
x24 : BitVec 128
x25 : BitVec 64
x26 : BitVec 128
hx24 : x26 <<< 64 = x24
x27 : BitVec 128
hx19 : x27 ||| x24 = x19
x28 : BitVec 64
hx21 : x28 ^^^ x25 = x21
x29 : BitVec 64
hx26 : BitVec.zeroExtend 128 x29 = x26
x30 : BitVec 64
hx27 : BitVec.zeroExtend 128 x30 = x27
x31 x32 : BitVec 64
hx22 : x23 ^^^ x32 = x22
x33 : BitVec 64
hx23 : x33 ^^^ x31 = x23
x34 x35 : BitVec 64
hx35 : BitVec.extractLsb' 0 64 b = x35
hx1 : x2 + x35 = x1
hx6 : x35 + x11 = x6
x36 : BitVec 64
hx36 : BitVec.extractLsb' 64 64 b = x36
hx31 : x36.rotateRight 18 = x31
hx32 : x36.rotateRight 41 = x32
hx33 : x36.rotateRight 14 = x33
hx34 : ~~~x36 = x34
x37 : BitVec 64
hx37 : BitVec.extractLsb' 64 64 e = x37
x38 : BitVec 64
hx38 : BitVec.extractLsb' 64 64 d = x38
hx29 : x38 + x37 = x29
x39 : BitVec 64
hx39 : BitVec.extractLsb' 64 64 c = x39
hx9 : x39 + x12 = x9
hx20 : x39 + x22 = x20
x40 : BitVec 64
hx40 : BitVec.extractLsb' 0 64 d = x40
hx14 : x17 + x40 = x14
x41 : BitVec 64
hx41 : BitVec.extractLsb' 0 64 c = x41
hx10 : x41 + x13 = x10
x42 : BitVec 64
hx42 : BitVec.extractLsb' 0 64 a = x42
hx28 : x36 &&& x42 = x28
x43 : BitVec 64
hx43 : BitVec.extractLsb' 0 64 e = x43
hx11 : x14 + x43 = x11
hx30 : x40 + x43 = x30
x44 : BitVec 64
hx44 : BitVec.extractLsb' 64 64 a = x44
hx25 : x34 &&& x44 = x25
⊢ x2 ++
      ((x1 &&& x36 ^^^ ~~~x1 &&& x42) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        BitVec.extractLsb' 0 64 x4) =
    x11 ++
      (x41 + (x6.rotateRight 14 ^^^ x6.rotateRight 18 ^^^ x6.rotateRight 41) + (x6 &&& x36 ^^^ ~~~x6 &&& x42) + x38 +
        x37)
-/
#guard_msgs in theorem sha512h_rule_2 (a b c d e : BitVec 128) :
  let a0 := extractLsb'  0 64 a
  let a1 := extractLsb' 64 64 a
  let b0 := extractLsb'  0 64 b
  let b1 := extractLsb' 64 64 b
  let c0 := extractLsb'  0 64 c
  let c1 := extractLsb' 64 64 c
  let d0 := extractLsb'  0 64 d
  let d1 := extractLsb' 64 64 d
  let e0 := extractLsb'  0 64 e
  let e1 := extractLsb' 64 64 e
  let inner_sum := binary_vector_op_aux 0 2 64 BitVec.add d e (BitVec.zero 128)
  let concat := inner_sum ++ inner_sum
  let operand := extractLsb' 64 128 concat
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d0 e0
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d1 e1
  sha512h a b (binary_vector_op_aux 0 2 64 BitVec.add c operand (BitVec.zero 128)) =
  hi64_spec ++ lo64_spec := by
  repeat (unfold binary_vector_op_aux; simp)
  repeat (unfold BitVec.partInstall; simp)
  unfold sha512h compression_update_t1 elem_set elem_get partInstall sigma_big_1 ch ror
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.sub_zero, reduceAllOnes,
    reduceZeroExtend, Nat.zero_mul, reduceHShiftLeft, reduceNot, reduceAnd, Nat.one_mul,
    BitVec.cast_eq]
  simp only [shiftLeft_zero_eq, BitVec.zero_or, and_nop_lemma]
  cse (config := {fuelSearch := 999999, fuelEliminate := 999999})
  trace_state
  all_goals sorry

end SHA
