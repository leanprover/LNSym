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

-- NOTE: v4.21 moved `trace_state` output from `info:` to `trace:` severity.
/--
trace: x y z x1 x2 : Nat
hx2 : y + y = x2
hx1 : x2 + x2 = x1
⊢ x + x + x1 = x1 + x1 + x1
---
warning: declaration uses 'sorry'
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
-- NOTE: v4.21 moved `trace_state` output from `info:` to `trace:` severity.
/--
trace: y : Nat
x : BitVec (y + (y + 0))
⊢ BitVec.ofNat (y + y) (y + y) = x
---
warning: declaration uses 'sorry'
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
-/

-- NOTE: On Lean v4.19 the `cse` tactic emits a *recovered* runtime panic
-- (`Error: index out of bounds`) as an info message with a non-deterministic
-- backtrace, alongside the `trace_state` goal (also info-severity). Since
-- `#guard_msgs` can only filter by severity, we drop info here and still check
-- the deterministic `sorry` warning; the goal state cannot be pinned byte-for-byte.
#guard_msgs (drop info, warning) in theorem bitvec_subexpr  (a b c d : BitVec 64) : (zeroExtend 128
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

set_option linter.unusedSimpArgs false in
open BitVec sha512_helpers DPSFP SHA2 in
-- NOTE: v4.21 moved `trace_state` output from `info:` to `trace:` severity.
/--
trace: a b c d e : BitVec 128
x1 x2 x3 : BitVec 64
x4 : BitVec 128
hx3 : extractLsb' 64 64 x4 = x3
x5 x6 x7 x8 x9 : BitVec 64
hx2 : x9 + x3 = x2
x10 x11 : BitVec 128
hx4 : x10 ||| x11 = x4
x12 : BitVec 128
hx10 : x12 &&& 18446744073709551615#128 = x10
x13 : BitVec 128
hx11 : x13 <<< 64 = x11
x14 : BitVec 64
hx12 : zeroExtend 128 x14 = x12
x15 : BitVec 64
hx13 : zeroExtend 128 x15 = x13
x16 x17 : BitVec 64
x18 : BitVec 128
hx16 : extractLsb' 64 64 x18 = x16
hx17 : extractLsb' 0 64 x18 = x17
x19 x20 : BitVec 64
hx8 : x19 + x20 = x8
x21 : BitVec 64
hx9 : x20 + x21 = x9
x22 : BitVec 128
x23 : BitVec 64
x24 : BitVec 128
hx18 : x24 ||| x22 = x18
x25 : BitVec 128
hx24 : x25 &&& 18446744073709551615#128 = x24
x26 : BitVec 128
hx22 : x26 <<< 64 = x22
x27 x28 : BitVec 64
hx25 : zeroExtend 128 x28 = x25
x29 : BitVec 64
hx20 : x29 ^^^ x27 = x20
x30 : BitVec 64
hx26 : zeroExtend 128 x30 = x26
x31 x32 : BitVec 64
hx21 : x23 ^^^ x32 = x21
x33 x34 : BitVec 64
hx23 : x34 ^^^ x33 = x23
x35 : BitVec 64
hx35 : extractLsb' 64 64 a = x35
hx27 : x31 &&& x35 = x27
x36 : BitVec 64
hx36 : extractLsb' 0 64 a = x36
x37 : BitVec 64
hx37 : extractLsb' 64 64 c = x37
hx19 : x37 + x21 = x19
x38 : BitVec 64
hx38 : extractLsb' 64 64 d = x38
hx7 : x8 + x38 = x7
hx30 : x37 + x38 = x30
x39 : BitVec 64
hx39 : extractLsb' 64 64 e = x39
hx6 : x7 + x39 = x6
hx15 : x16 + x39 = x15
x40 : BitVec 64
hx40 : extractLsb' 0 64 d = x40
x41 : BitVec 64
hx41 : extractLsb' 64 64 b = x41
hx31 : ~~~x41 = x31
hx32 : x41.rotateRight 41 = x32
hx33 : x41.rotateRight 18 = x33
hx34 : x41.rotateRight 14 = x34
hx29 : x41 &&& x36 = x29
x42 : BitVec 64
hx42 : extractLsb' 0 64 e = x42
hx14 : x17 + x42 = x14
x43 : BitVec 64
hx43 : extractLsb' 0 64 b = x43
hx1 : x2 + x43 = x1
hx5 : x43 + x6 = x5
x44 : BitVec 64
hx44 : extractLsb' 0 64 c = x44
hx28 : x44 + x40 = x28
⊢ x2 ++
      ((x1 &&& x41 ^^^ ~~~x1 &&& x36) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        extractLsb' 0 64 x4) =
    x6 ++
      (x44 + (x5.rotateRight 14 ^^^ x5.rotateRight 18 ^^^ x5.rotateRight 41) + (x5 &&& x41 ^^^ ~~~x5 &&& x36) + x40 +
        x42)
---
warning: declaration uses 'sorry'
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
    reduceHShiftLeft, reduceNot, reduceAnd, BitVec.zero_or, shiftLeft_zero]
  cse (config := { minOccsToCSE := 2, fuelSearch := 99999, fuelEliminate := 99999 })
  trace_state
  all_goals sorry

open BitVec in
private theorem and_nop_lemma (x : BitVec 64) :
  (zeroExtend 128 x) &&& 0xffffffffffffffff#128 = (zeroExtend 128 x) := by
  bv_decide

set_option linter.unusedSimpArgs false in
open BitVec sha512_helpers DPSFP SHA2 in
-- NOTE: v4.21 moved `trace_state` output from `info:` to `trace:` severity.
/--
trace: a b c d e : BitVec 128
x1 x2 x3 : BitVec 64
x4 : BitVec 128
hx3 : extractLsb' 64 64 x4 = x3
x5 : BitVec 128
x6 : BitVec 64
x7 : BitVec 128
hx4 : x7 ||| x5 = x4
x8 : BitVec 128
hx5 : x8 <<< 64 = x5
x9 : BitVec 64
hx7 : zeroExtend 128 x9 = x7
x10 : BitVec 64
hx8 : zeroExtend 128 x10 = x8
x11 x12 x13 x14 : BitVec 64
x15 : BitVec 128
hx12 : extractLsb' 64 64 x15 = x12
hx13 : extractLsb' 0 64 x15 = x13
x16 : BitVec 256
hx15 : extractLsb' 64 128 x16 = x15
x17 x18 : BitVec 64
hx2 : x18 + x3 = x2
x19 : BitVec 64
x20 : BitVec 128
hx16 : x20 ++ x20 = x16
x21 : BitVec 64
hx17 : x19 + x21 = x17
x22 : BitVec 64
hx18 : x21 + x22 = x18
x23 : BitVec 64
x24 : BitVec 128
x25 : BitVec 64
x26 : BitVec 128
hx20 : x26 ||| x24 = x20
x27 : BitVec 128
hx24 : x27 <<< 64 = x24
x28 : BitVec 64
hx26 : zeroExtend 128 x28 = x26
x29 : BitVec 64
hx27 : zeroExtend 128 x29 = x27
x30 : BitVec 64
hx21 : x30 ^^^ x25 = x21
x31 : BitVec 64
hx22 : x23 ^^^ x31 = x22
x32 x33 x34 : BitVec 64
hx23 : x34 ^^^ x33 = x23
x35 : BitVec 64
hx35 : extractLsb' 0 64 a = x35
x36 : BitVec 64
hx36 : extractLsb' 64 64 a = x36
hx25 : x32 &&& x36 = x25
x37 : BitVec 64
hx37 : extractLsb' 64 64 e = x37
x38 : BitVec 64
hx38 : extractLsb' 0 64 b = x38
hx1 : x2 + x38 = x1
hx6 : x38 + x11 = x6
x39 : BitVec 64
hx39 : extractLsb' 0 64 d = x39
hx14 : x17 + x39 = x14
x40 : BitVec 64
hx40 : extractLsb' 64 64 b = x40
hx31 : x40.rotateRight 41 = x31
hx32 : ~~~x40 = x32
hx33 : x40.rotateRight 18 = x33
hx34 : x40.rotateRight 14 = x34
hx30 : x40 &&& x35 = x30
x41 : BitVec 64
hx41 : extractLsb' 0 64 c = x41
hx9 : x41 + x13 = x9
x42 : BitVec 64
hx42 : extractLsb' 64 64 c = x42
hx10 : x42 + x12 = x10
hx19 : x42 + x22 = x19
x43 : BitVec 64
hx43 : extractLsb' 64 64 d = x43
hx29 : x43 + x37 = x29
x44 : BitVec 64
hx44 : extractLsb' 0 64 e = x44
hx11 : x14 + x44 = x11
hx28 : x39 + x44 = x28
⊢ x2 ++
      ((x1 &&& x40 ^^^ ~~~x1 &&& x35) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        extractLsb' 0 64 x4) =
    x11 ++
      (x41 + (x6.rotateRight 14 ^^^ x6.rotateRight 18 ^^^ x6.rotateRight 41) + (x6 &&& x40 ^^^ ~~~x6 &&& x35) + x43 +
        x37)
---
warning: declaration uses 'sorry'
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
  simp only [shiftLeft_zero, BitVec.zero_or, and_nop_lemma]
  cse (config := {fuelSearch := 999999, fuelEliminate := 999999})
  trace_state
  all_goals sorry

end SHA
