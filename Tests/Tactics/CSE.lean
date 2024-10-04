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

set_option trace.Tactic.cse.summary true in
/--
warning: declaration uses 'sorry'
---
info: [Tactic.cse.summary] CSE collecting hypotheses:
  [Tactic.cse.summary] (x + x + (y + y + (y + y)) =
        y + y + (y + y) + (y + y + (y + y)) + (y + y + (y + y))):(Prop) [relevant? ❌️] (unfold for subexpressions...)
    [Tactic.cse.summary] (x + x + (y + y + (y + y))):(Nat) [relevant? ✅️] (unfold for subexpressions...)
      [Tactic.cse.summary] (x + x):(Nat) [relevant? ✅️] (unfold for subexpressions...)
        [Tactic.cse.summary] (x):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 1 }) (NOTE: can be large)
            [Tactic.cse.summary] x
        [Tactic.cse.summary] (x):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 2, size := 1 }) (NOTE: can be large)
            [Tactic.cse.summary] x
        [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 3 }) (NOTE: can be large)
          [Tactic.cse.summary] x + x
      [Tactic.cse.summary] (y + y + (y + y)):(Nat) [relevant? ✅️] (unfold for subexpressions...)
        [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 2, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 3 }) (NOTE: can be large)
            [Tactic.cse.summary] y + y
        [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 3, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 4, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 2, size := 3 }) (NOTE: can be large)
            [Tactic.cse.summary] y + y
        [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 7 }) (NOTE: can be large)
          [Tactic.cse.summary] y + y + (y + y)
      [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 11 }) (NOTE: can be large)
        [Tactic.cse.summary] x + x + (y + y + (y + y))
    [Tactic.cse.summary] (y + y + (y + y) + (y + y + (y + y)) +
          (y + y + (y + y))):(Nat) [relevant? ✅️] (unfold for subexpressions...)
      [Tactic.cse.summary] (y + y + (y + y) + (y + y + (y + y))):(Nat) [relevant? ✅️] (unfold for subexpressions...)
        [Tactic.cse.summary] (y + y + (y + y)):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 5, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 6, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 3, size := 3 }) (NOTE: can be large)
              [Tactic.cse.summary] y + y
          [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 7, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 8, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 4, size := 3 }) (NOTE: can be large)
              [Tactic.cse.summary] y + y
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 2, size := 7 }) (NOTE: can be large)
            [Tactic.cse.summary] y + y + (y + y)
        [Tactic.cse.summary] (y + y + (y + y)):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 9, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 10, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 5, size := 3 }) (NOTE: can be large)
              [Tactic.cse.summary] y + y
          [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 11, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
              [Tactic.cse.summary] updated expr (...) with info ({ occs := 12, size := 1 }) (NOTE: can be large)
                [Tactic.cse.summary] y
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 6, size := 3 }) (NOTE: can be large)
              [Tactic.cse.summary] y + y
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 3, size := 7 }) (NOTE: can be large)
            [Tactic.cse.summary] y + y + (y + y)
        [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 15 }) (NOTE: can be large)
          [Tactic.cse.summary] y + y + (y + y) + (y + y + (y + y))
      [Tactic.cse.summary] (y + y + (y + y)):(Nat) [relevant? ✅️] (unfold for subexpressions...)
        [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 13, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 14, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 7, size := 3 }) (NOTE: can be large)
            [Tactic.cse.summary] y + y
        [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 15, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
            [Tactic.cse.summary] updated expr (...) with info ({ occs := 16, size := 1 }) (NOTE: can be large)
              [Tactic.cse.summary] y
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 8, size := 3 }) (NOTE: can be large)
            [Tactic.cse.summary] y + y
        [Tactic.cse.summary] updated expr (...) with info ({ occs := 4, size := 7 }) (NOTE: can be large)
          [Tactic.cse.summary] y + y + (y + y)
      [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 23 }) (NOTE: can be large)
        [Tactic.cse.summary] y + y + (y + y) + (y + y + (y + y)) + (y + y + (y + y))
[Tactic.cse.summary] ⏭️ CSE eliminiating unprofitable expressions (#expressions:8):
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 16, size := 1 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: y
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 2, size := 1 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: x
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 1, size := 3 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: x + x
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 1, size := 23 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: y + y + (y + y) + (y + y + (y + y)) + (y + y + (y + y))
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 1, size := 11 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: x + x + (y + y + (y + y))
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 1, size := 15 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: y + y + (y + y) + (y + y + (y + y))
[Tactic.cse.summary] CSE summary of profitable expressions (#expressions:2):
  [Tactic.cse.summary] 1) { occs := 8, size := 3 } (NOTE: can be large)
    [Tactic.cse.summary] y + y
  [Tactic.cse.summary] 2) { occs := 4, size := 7 } (NOTE: can be large)
    [Tactic.cse.summary] y + y + (y + y)
[Tactic.cse.summary] CSE rewriting (#expressions:2):
  [Tactic.cse.summary] ⌛ Generalizing hx1: x1 = ... (NOTE: can be large)
    [Tactic.cse.summary] y + y + (y + y)
  [Tactic.cse.summary] ✅️ succeeded in generalizing hx1. (NOTE: can be large)
    [Tactic.cse.summary] x y z x1 : Nat
        hx1 : y + y + (y + y) = x1
        ⊢ x + x + x1 = x1 + x1 + x1
  [Tactic.cse.summary] ⌛ Generalizing hx2: x2 = ... (NOTE: can be large)
    [Tactic.cse.summary] y + y
  [Tactic.cse.summary] ✅️ succeeded in generalizing hx2. (NOTE: can be large)
    [Tactic.cse.summary] x y z x1 x2 : Nat hx2 : y + y = x2 hx1 : x2 + x2 = x1 ⊢ x + x + x1 = x1 + x1 + x1
-/
#guard_msgs in theorem many_subexpr (x y z : Nat) : (x + x) + ((y + y) + (y + y)) =
  (((y + y) + (y + y)) + ((y + y) + (y + y))) + (((y + y) + (y + y))) := by
  cse (config := {minOccsToCSE := 2})
  all_goals sorry


/- ### Test that generalize fails gracefully

In this test case, we try to generalize on `64`, which is a dependent index
of the type `BitVec 64`. Therefore, this should fail to generalize.
-/
set_option trace.Tactic.cse.summary true in
/--
warning: declaration uses 'sorry'
---
info: [Tactic.cse.summary] CSE collecting hypotheses:
  [Tactic.cse.summary] (BitVec.ofNat (y + y) (y + y) = x):(Prop) [relevant? ❌️] (unfold for subexpressions...)
    [Tactic.cse.summary] (BitVec.ofNat (y + y) (y + y)):(BitVec (y + y)) [relevant? ✅️] (unfold for subexpressions...)
      [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
        [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 1 }) (NOTE: can be large)
            [Tactic.cse.summary] y
        [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 2, size := 1 }) (NOTE: can be large)
            [Tactic.cse.summary] y
        [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 3 }) (NOTE: can be large)
          [Tactic.cse.summary] y + y
      [Tactic.cse.summary] (y + y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
        [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 3, size := 1 }) (NOTE: can be large)
            [Tactic.cse.summary] y
        [Tactic.cse.summary] (y):(Nat) [relevant? ✅️] (unfold for subexpressions...)
          [Tactic.cse.summary] updated expr (...) with info ({ occs := 4, size := 1 }) (NOTE: can be large)
            [Tactic.cse.summary] y
        [Tactic.cse.summary] updated expr (...) with info ({ occs := 2, size := 3 }) (NOTE: can be large)
          [Tactic.cse.summary] y + y
      [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 7 }) (NOTE: can be large)
        [Tactic.cse.summary] BitVec.ofNat (y + y) (y + y)
    [Tactic.cse.summary] (x):(BitVec (y + (y + 0))) [relevant? ✅️] (unfold for subexpressions...)
      [Tactic.cse.summary] Added new expr (...) with info ({ occs := 1, size := 1 }) (NOTE: can be large)
        [Tactic.cse.summary] x
[Tactic.cse.summary] ⏭️ CSE eliminiating unprofitable expressions (#expressions:4):
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 4, size := 1 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: y
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 1, size := 1 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: x
  [Tactic.cse.summary] ⏭️ Unprofitable { occs := 1, size := 7 } . (NOTE: can be large)
    [Tactic.cse.summary] expr: BitVec.ofNat (y + y) (y + y)
[Tactic.cse.summary] CSE summary of profitable expressions (#expressions:1):
  [Tactic.cse.summary] 1) { occs := 2, size := 3 } (NOTE: can be large)
    [Tactic.cse.summary] y + y
[Tactic.cse.summary] CSE rewriting (#expressions:1):
  [Tactic.cse.summary] ⌛ Generalizing hx1: x1 = ... (NOTE: can be large)
    [Tactic.cse.summary] y + y
  [Tactic.cse.summary] 💥️ failed to generalize hx1 (NOTE: can be large)
    [Tactic.cse.summary] tactic 'generalize' failed, result is not type correct
          ∀ (x1 : Nat), BitVec.ofNat x1 x1 = x
        y : Nat
        x : BitVec (y + (y + 0))
        ⊢ BitVec.ofNat (y + y) (y + y) = x
-/
#guard_msgs in theorem generalize_failure (x : BitVec (y + (y + 0))) :
    (BitVec.ofNat (y + y) (y + y)) = x := by
  cse
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
info: H : 64 > 0
a b c d e : BitVec 128
x1 x2 x3 : BitVec 64
x4 : BitVec 128
hx3 : BitVec.extractLsb' 64 64 x4 = x3
x5 x6 x7 x8 x9 : BitVec 64
hx2 : x9 + x3 = x2
x10 x11 : BitVec 128
hx4 : x10 ||| x11 = x4
x12 : BitVec 128
hx10 : x12 &&& 18446744073709551615#128 = x10
x13 : BitVec 128
hx11 : x13 <<< 64 = x11
x14 : BitVec 64
hx12 : BitVec.zeroExtend 128 x14 = x12
x15 : BitVec 64
hx13 : BitVec.zeroExtend 128 x15 = x13
x16 x17 : BitVec 64
x18 : BitVec 128
hx16 : BitVec.extractLsb' 0 64 x18 = x16
hx17 : BitVec.extractLsb' 64 64 x18 = x17
x19 x20 : BitVec 64
hx8 : x19 + x20 = x8
x21 : BitVec 64
hx9 : x20 + x21 = x9
x22 x23 : BitVec 128
hx18 : x22 ||| x23 = x18
x24 : BitVec 64
x25 : BitVec 128
hx23 : x25 <<< 64 = x23
x26 : BitVec 128
hx22 : x26 &&& 18446744073709551615#128 = x22
x27 x28 : BitVec 64
hx26 : BitVec.zeroExtend 128 x28 = x26
x29 : BitVec 64
hx20 : x29 ^^^ x27 = x20
x30 : BitVec 64
hx25 : BitVec.zeroExtend 128 x30 = x25
x31 x32 x33 : BitVec 64
hx21 : x24 ^^^ x33 = x21
x34 : BitVec 64
hx24 : x32 ^^^ x34 = x24
x35 : BitVec 64
hx35 : BitVec.extractLsb' 0 64 a = x35
x36 : BitVec 64
hx36 : BitVec.extractLsb' 0 64 e = x36
hx14 : x16 + x36 = x14
x37 : BitVec 64
hx37 : BitVec.extractLsb' 64 64 b = x37
hx31 : ~~~x37 = x31
hx32 : x37.rotateRight 14 = x32
hx33 : x37.rotateRight 41 = x33
hx34 : x37.rotateRight 18 = x34
hx29 : x37 &&& x35 = x29
x38 : BitVec 64
hx38 : BitVec.extractLsb' 0 64 b = x38
hx1 : x2 + x38 = x1
hx5 : x38 + x6 = x5
x39 : BitVec 64
hx39 : BitVec.extractLsb' 64 64 c = x39
hx19 : x39 + x21 = x19
x40 : BitVec 64
hx40 : BitVec.extractLsb' 0 64 c = x40
x41 : BitVec 64
hx41 : BitVec.extractLsb' 0 64 d = x41
hx28 : x40 + x41 = x28
x42 : BitVec 64
hx42 : BitVec.extractLsb' 64 64 a = x42
hx27 : x31 &&& x42 = x27
x43 : BitVec 64
hx43 : BitVec.extractLsb' 64 64 d = x43
hx7 : x8 + x43 = x7
hx30 : x39 + x43 = x30
x44 : BitVec 64
hx44 : BitVec.extractLsb' 64 64 e = x44
hx6 : x7 + x44 = x6
hx15 : x17 + x44 = x15
⊢ x2 ++
      ((x1 &&& x37 ^^^ ~~~x1 &&& x35) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        BitVec.extractLsb' 0 64 x4) =
    x6 ++
      (x40 + (x5.rotateRight 14 ^^^ x5.rotateRight 18 ^^^ x5.rotateRight 41) + (x5 &&& x37 ^^^ ~~~x5 &&& x35) + x41 +
        x36)
-/
#guard_msgs in theorem sha512h_rule_1 (a b c d e : BitVec 128) :
  let elements := 2
  let esize := 64
  let inner_sum := (binary_vector_op_aux 0 elements esize BitVec.add c d (BitVec.zero 128) H)
  let outer_sum := (binary_vector_op_aux 0 elements esize BitVec.add inner_sum e (BitVec.zero 128) H)
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
info: h1 h2 : 64 > 0
a b c d e : BitVec 128
x1 x2 x3 : BitVec 64
x4 : BitVec 128
hx3 : BitVec.extractLsb' 64 64 x4 = x3
x5 : BitVec 64
x6 x7 : BitVec 128
hx4 : x7 ||| x6 = x4
x8 : BitVec 128
hx6 : x8 <<< 64 = x6
x9 : BitVec 64
hx8 : BitVec.zeroExtend 128 x9 = x8
x10 : BitVec 64
hx7 : BitVec.zeroExtend 128 x10 = x7
x11 x12 x13 x14 : BitVec 64
x15 : BitVec 128
hx12 : BitVec.extractLsb' 0 64 x15 = x12
hx13 : BitVec.extractLsb' 64 64 x15 = x13
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
x23 : BitVec 128
x24 : BitVec 64
x25 : BitVec 128
hx19 : x25 ||| x23 = x19
x26 : BitVec 64
x27 : BitVec 128
hx23 : x27 <<< 64 = x23
x28 : BitVec 64
hx27 : BitVec.zeroExtend 128 x28 = x27
x29 : BitVec 64
hx21 : x29 ^^^ x26 = x21
x30 : BitVec 64
hx25 : BitVec.zeroExtend 128 x30 = x25
x31 x32 : BitVec 64
hx24 : x32 ^^^ x31 = x24
x33 x34 : BitVec 64
hx22 : x24 ^^^ x34 = x22
x35 : BitVec 64
hx35 : BitVec.extractLsb' 0 64 b = x35
hx1 : x2 + x35 = x1
hx5 : x35 + x11 = x5
x36 : BitVec 64
hx36 : BitVec.extractLsb' 64 64 d = x36
x37 : BitVec 64
hx37 : BitVec.extractLsb' 64 64 e = x37
hx28 : x36 + x37 = x28
x38 : BitVec 64
hx38 : BitVec.extractLsb' 0 64 a = x38
x39 : BitVec 64
hx39 : BitVec.extractLsb' 64 64 c = x39
hx9 : x39 + x13 = x9
hx20 : x39 + x22 = x20
x40 : BitVec 64
hx40 : BitVec.extractLsb' 0 64 c = x40
hx10 : x40 + x12 = x10
x41 : BitVec 64
hx41 : BitVec.extractLsb' 0 64 e = x41
hx11 : x14 + x41 = x11
x42 : BitVec 64
hx42 : BitVec.extractLsb' 64 64 a = x42
hx26 : x33 &&& x42 = x26
x43 : BitVec 64
hx43 : BitVec.extractLsb' 0 64 d = x43
hx14 : x17 + x43 = x14
hx30 : x43 + x41 = x30
x44 : BitVec 64
hx44 : BitVec.extractLsb' 64 64 b = x44
hx31 : x44.rotateRight 18 = x31
hx32 : x44.rotateRight 14 = x32
hx33 : ~~~x44 = x33
hx34 : x44.rotateRight 41 = x34
hx29 : x44 &&& x38 = x29
⊢ x2 ++
      ((x1 &&& x44 ^^^ ~~~x1 &&& x38) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        BitVec.extractLsb' 0 64 x4) =
    x11 ++
      (x40 + (x5.rotateRight 14 ^^^ x5.rotateRight 18 ^^^ x5.rotateRight 41) + (x5 &&& x44 ^^^ ~~~x5 &&& x38) + x36 +
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
  let inner_sum := binary_vector_op_aux 0 2 64 BitVec.add d e (BitVec.zero 128) h1
  let concat := inner_sum ++ inner_sum
  let operand := extractLsb' 64 128 concat
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d0 e0
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d1 e1
  sha512h a b (binary_vector_op_aux 0 2 64 BitVec.add c operand (BitVec.zero 128) h2) =
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
