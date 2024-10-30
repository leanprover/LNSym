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
x5 x6 x7 x8 : BitVec 64
x9 x10 : BitVec 128
hx4 : x9 ||| x10 = x4
x11 : BitVec 64
hx2 : x11 + x3 = x2
x12 x13 : BitVec 128
hx10 : x13 <<< 64 = x10
x14 : BitVec 64
hx12 : BitVec.zeroExtend 128 x14 = x12
x15 : BitVec 64
hx13 : BitVec.zeroExtend 128 x15 = x13
x16 x17 : BitVec 64
x18 : BitVec 128
hx16 : BitVec.extractLsb' 64 64 x18 = x16
hx17 : BitVec.extractLsb' 0 64 x18 = x17
x19 x20 x21 : BitVec 64
hx8 : x19 + x21 = x8
hx11 : x21 + x20 = x11
x22 : BitVec 128
x23 : BitVec 64
x24 : BitVec 128
hx18 : x22 ||| x24 = x18
x25 x26 : BitVec 128
hx24 : x26 <<< 64 = x24
x27 x28 : BitVec 64
hx26 : BitVec.zeroExtend 128 x28 = x26
x29 : BitVec 64
hx25 : BitVec.zeroExtend 128 x29 = x25
x30 : BitVec 64
hx21 : x30 ^^^ x27 = x21
x31 : BitVec 64
hx20 : x23 ^^^ x31 = x20
x32 x33 : BitVec 64
hx23 : x32 ^^^ x33 = x23
x34 x35 : BitVec 64
hx35 : BitVec.extractLsb' 0 64 b = x35
hx1 : x2 + x35 = x1
hx5 : x35 + x6 = x5
x36 : BitVec 64
hx36 : BitVec.extractLsb' 0 64 d = x36
x37 : BitVec 64
hx37 : BitVec.extractLsb' 64 64 d = x37
hx7 : x8 + x37 = x7
x38 : BitVec 64
hx38 : BitVec.extractLsb' 0 64 a = x38
x39 : BitVec 64
hx39 : BitVec.extractLsb' 64 64 e = x39
hx6 : x7 + x39 = x6
hx15 : x16 + x39 = x15
x40 : BitVec 64
hx40 : BitVec.extractLsb' 0 64 e = x40
hx14 : x17 + x40 = x14
x41 : BitVec 64
hx41 : BitVec.extractLsb' 64 64 a = x41
hx27 : x34 &&& x41 = x27
x42 : BitVec 64
hx42 : BitVec.extractLsb' 64 64 c = x42
hx19 : x42 + x20 = x19
hx28 : x42 + x37 = x28
x43 : BitVec 64
hx43 : BitVec.extractLsb' 0 64 c = x43
hx29 : x43 + x36 = x29
x44 : BitVec 64
hx44 : BitVec.extractLsb' 64 64 b = x44
hx34 : ~~~x44 = x34
hx30 : x44 &&& x38 = x30
x45 : BitVec 128
hx9 : x12 &&& x45 = x9
hx22 : x25 &&& x45 = x22
x46 : Nat
hx46 : 14 = x46
hx32 : x44.rotateRight x46 = x32
x50 : Nat
hx50 : 18 = x50
hx33 : x44.rotateRight x50 = x33
x51 : Nat
hx51 : 18446744073709551615 = x51
hx45 : BitVec.ofNat 128 x51 = x45
x52 : Nat
hx52 : 41 = x52
hx31 : x44.rotateRight x52 = x31
⊢ x2 ++
      ((x1 &&& x44 ^^^ ~~~x1 &&& x38) + (x1.rotateRight x46 ^^^ x1.rotateRight x50 ^^^ x1.rotateRight x52) +
        BitVec.extractLsb' 0 64 x4) =
    x6 ++
      (x43 + (x5.rotateRight x46 ^^^ x5.rotateRight x50 ^^^ x5.rotateRight x52) + (x5 &&& x44 ^^^ ~~~x5 &&& x38) + x36 +
        x40)
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
x5 x6 : BitVec 128
hx5 : x6 <<< 64 = x5
x7 : BitVec 128
hx4 : x7 ||| x5 = x4
x8 : BitVec 64
hx6 : BitVec.zeroExtend 128 x8 = x6
x9 : BitVec 64
hx7 : BitVec.zeroExtend 128 x9 = x7
x10 x11 x12 x13 : BitVec 64
x14 : BitVec 128
hx11 : BitVec.extractLsb' 64 64 x14 = x11
hx12 : BitVec.extractLsb' 0 64 x14 = x12
x15 : BitVec 256
hx14 : BitVec.extractLsb' 64 128 x15 = x14
x16 x17 x18 : BitVec 64
hx2 : x18 + x3 = x2
x19 : BitVec 64
x20 : BitVec 128
hx15 : x20 ++ x20 = x15
x21 x22 : BitVec 64
hx17 : x19 + x22 = x17
hx18 : x22 + x21 = x18
x23 : BitVec 64
x24 x25 : BitVec 128
hx20 : x25 ||| x24 = x20
x26 : BitVec 128
hx24 : x26 <<< 64 = x24
x27 x28 : BitVec 64
hx26 : BitVec.zeroExtend 128 x28 = x26
x29 : BitVec 64
hx22 : x29 ^^^ x27 = x22
x30 : BitVec 64
hx25 : BitVec.zeroExtend 128 x30 = x25
x31 x32 : BitVec 64
hx21 : x23 ^^^ x32 = x21
x33 : BitVec 64
hx23 : x31 ^^^ x33 = x23
x34 x35 : BitVec 64
hx35 : BitVec.extractLsb' 0 64 a = x35
x36 : BitVec 64
hx36 : BitVec.extractLsb' 64 64 e = x36
x37 : BitVec 64
hx37 : BitVec.extractLsb' 0 64 e = x37
hx13 : x16 + x37 = x13
x38 : BitVec 64
hx38 : BitVec.extractLsb' 64 64 a = x38
hx27 : x34 &&& x38 = x27
x39 : BitVec 64
hx39 : BitVec.extractLsb' 64 64 c = x39
hx8 : x39 + x11 = x8
hx19 : x39 + x21 = x19
x40 : BitVec 64
hx40 : BitVec.extractLsb' 0 64 b = x40
hx1 : x2 + x40 = x1
hx10 : x40 + x13 = x10
x41 : BitVec 64
hx41 : BitVec.extractLsb' 64 64 d = x41
hx28 : x41 + x36 = x28
x42 : BitVec 64
hx42 : BitVec.extractLsb' 0 64 c = x42
hx9 : x42 + x12 = x9
x43 : BitVec 64
hx43 : BitVec.extractLsb' 0 64 d = x43
hx16 : x17 + x43 = x16
hx30 : x43 + x37 = x30
x44 : BitVec 64
hx44 : BitVec.extractLsb' 64 64 b = x44
hx34 : ~~~x44 = x34
hx29 : x44 &&& x35 = x29
x45 : Nat
hx45 : 14 = x45
hx31 : x44.rotateRight x45 = x31
x49 : Nat
hx49 : 18 = x49
hx33 : x44.rotateRight x49 = x33
x50 : Nat
hx50 : 41 = x50
hx32 : x44.rotateRight x50 = x32
⊢ x2 ++
      ((x1 &&& x44 ^^^ ~~~x1 &&& x35) + (x1.rotateRight x45 ^^^ x1.rotateRight x49 ^^^ x1.rotateRight x50) +
        BitVec.extractLsb' 0 64 x4) =
    x13 ++
      (x42 + (x10.rotateRight x45 ^^^ x10.rotateRight x49 ^^^ x10.rotateRight x50) + (x10 &&& x44 ^^^ ~~~x10 &&& x35) +
          x41 +
        x36)
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
