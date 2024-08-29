import Tactics.CSE

import Arm.Insts.DPSFP.Insts
import Specs.SHA512
import Std.Tactic.BVDecide
import Tactics.CSE


/- ### Test that CSE succeeds and counts subexpressions correctly.

We want to check that it correctly ees that there are:
- `16` occurrences of `y`,
- `8` occurrences of `y + y`,
- `4` occurrences of `(y + y) + (y + y)`.

-/

set_option trace.Tactic.cse.generalize true in
set_option trace.Tactic.cse.summary true in
/--
warning: declaration uses 'sorry'
---
info: [Tactic.cse.summary] CSE collected expressions: ⏎
    y := { occs := 16, size := 1 }
    y + y + (y + y) + (y + y + (y + y)) + (y + y + (y + y)) := { occs := 1, size := 23 }
    y + y + (y + y) + (y + y + (y + y)) := { occs := 1, size := 15 }
    y + y + (y + y) := { occs := 4, size := 7 }
    x + x := { occs := 1, size := 3 }
    x := { occs := 2, size := 1 }
    x + x + (y + y + (y + y)) := { occs := 1, size := 11 }
    y + y := { occs := 8, size := 3 }
[Tactic.cse.generalize] ⏭️ Skipping y + y + (y + y) + (y + y + (y + y)) +
      (y + y + (y + y)): Unprofitable { occs := 1, size := 23 } .
[Tactic.cse.generalize] ⏭️ Skipping y + y + (y + y) + (y + y + (y + y)): Unprofitable { occs := 1, size := 15 } .
[Tactic.cse.generalize] ⏭️ Skipping x + x + (y + y + (y + y)): Unprofitable { occs := 1, size := 11 } .
[Tactic.cse.generalize] ⌛ Generalizing hx1 : y + y + (y + y) = x1
[Tactic.cse.generalize] ✅ succeeded in generalizing hx1. (x y z x1 : Nat
    hx1 : y + y + (y + y) = x1
    ⊢ x + x + x1 = x1 + x1 + x1)
[Tactic.cse.generalize] ⌛ Generalizing hx2 : y + y = x2
[Tactic.cse.generalize] ✅ succeeded in generalizing hx2. (x y z x1 x2 : Nat
    hx2 : y + y = x2
    hx1 : x2 + x2 = x1
    ⊢ x + x + x1 = x1 + x1 + x1)
[Tactic.cse.generalize] ⏭️ Skipping x + x: Unprofitable { occs := 1, size := 3 } .
[Tactic.cse.generalize] ⏭️ Skipping x: Unprofitable { occs := 2, size := 1 } .
[Tactic.cse.generalize] ⏭️ Skipping y: Unprofitable { occs := 16, size := 1 } .
-/
#guard_msgs in example (x y z : Nat) : (x + x) + ((y + y) + (y + y)) =
  (((y + y) + (y + y)) + ((y + y) + (y + y))) + (((y + y) + (y + y))) := by
  cse (config := {minOccsToCSE := 2})
  all_goals sorry


/- ### Test that generalize fails gracefully

In this test case, we try to generalize on `64`, which is a dependent index
of the type `BitVec 64`. Therefore, this should fail to generalize.
-/
set_option trace.Tactic.cse.generalize true in
/--
warning: declaration uses 'sorry'
---
info: [Tactic.cse.generalize] ⏭️ Skipping BitVec.ofNat (y + y) (y + y): Unprofitable { occs := 1, size := 7 } .
[Tactic.cse.generalize] ⌛ Generalizing hx1 : y + y = x1
[Tactic.cse.generalize] ✅ succeeded in generalizing hx1. (y x1 : Nat
    hx1 : y + y = x1
    x : BitVec x1
    ⊢ BitVec.ofNat x1 x1 = x)
[Tactic.cse.generalize] ⏭️ Skipping y: Unprofitable { occs := 4, size := 1 } .
[Tactic.cse.generalize] ⏭️ Skipping x: Unprofitable { occs := 1, size := 1 } .
-/
#guard_msgs in example (x : BitVec (y+y)) : (BitVec.ofNat (y+y) (y+y)) = x := by
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
x3 : BitVec (127 - 64 + 1)
hx3 : BitVec.extractLsb 127 64 c = x3
hx2 : BitVec.zeroExtend 128 x3 = x2
⊢ BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 x1) ||| BitVec.zeroExtend 128 (BitVec.extractLsb 127 64 x1) =
    sorryAx (BitVec 128)
-/
#guard_msgs in example  (a b c d : BitVec 64) : (zeroExtend 128
              (extractLsb 63 0
                  (
                    zeroExtend 128 (extractLsb 127 64 c) <<< 64)) |||
          zeroExtend 128
              (extractLsb 127 64
                  (zeroExtend 128 (extractLsb 127 64 c) <<< 64))) = sorry := by
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
x1 x2 : BitVec 64
x3 : BitVec (127 - 64 + 1)
x4 : BitVec 128
hx3 : BitVec.extractLsb 127 64 x4 = x3
x5 x6 x7 x8 x9 : BitVec 64
hx2 : x9 + x3 = x2
x10 x11 : BitVec 128
hx4 : x10 ||| x11 = x4
x12 : BitVec 128
hx10 : x12 &&& 18446744073709551615#128 = x10
x13 : BitVec 128
hx11 : x13 <<< 64 = x11
x14 : BitVec 64
hx13 : BitVec.zeroExtend 128 x14 = x13
x15 : BitVec 64
hx12 : BitVec.zeroExtend 128 x15 = x12
x16 : BitVec (127 - 64 + 1)
x17 : BitVec (63 - 0 + 1)
x18 : BitVec 128
hx16 : BitVec.extractLsb 127 64 x18 = x16
hx17 : BitVec.extractLsb 63 0 x18 = x17
x19 x20 : BitVec 64
hx8 : x19 + x20 = x8
x21 : BitVec 64
hx9 : x20 + x21 = x9
x22 : BitVec 128
x23 : BitVec 64
x24 : BitVec 128
hx18 : x22 ||| x24 = x18
x25 : BitVec 64
x26 : BitVec 128
hx22 : x26 &&& 18446744073709551615#128 = x22
x27 : BitVec 128
hx24 : x27 <<< 64 = x24
x28 : BitVec 64
hx27 : BitVec.zeroExtend 128 x28 = x27
x29 : BitVec 64
hx26 : BitVec.zeroExtend 128 x29 = x26
x30 : BitVec 64
hx20 : x30 ^^^ x25 = x20
x31 x32 : BitVec 64
hx21 : x23 ^^^ x32 = x21
x33 x34 : BitVec 64
hx23 : x34 ^^^ x33 = x23
x35 : BitVec (63 - 0 + 1)
hx35 : BitVec.extractLsb 63 0 a = x35
x36 : BitVec (127 - 64 + 1)
hx36 : BitVec.extractLsb 127 64 c = x36
hx19 : x36 + x21 = x19
x37 : BitVec (127 - 64 + 1)
hx37 : BitVec.extractLsb 127 64 d = x37
hx7 : x8 + x37 = x7
hx28 : x36 + x37 = x28
x38 : BitVec (127 - 64 + 1)
hx38 : BitVec.extractLsb 127 64 e = x38
hx6 : x7 + x38 = x6
hx14 : x16 + x38 = x14
x39 : BitVec (63 - 0 + 1)
hx39 : BitVec.extractLsb 63 0 d = x39
x40 : BitVec (127 - 64 + 1)
hx40 : BitVec.extractLsb 127 64 a = x40
hx25 : x31 &&& x40 = x25
x41 : BitVec (63 - 0 + 1)
hx41 : BitVec.extractLsb 63 0 e = x41
hx15 : x17 + x41 = x15
x42 : BitVec (63 - 0 + 1)
hx42 : BitVec.extractLsb 63 0 c = x42
hx29 : x42 + x39 = x29
x43 : BitVec (127 - 64 + 1)
hx43 : BitVec.extractLsb 127 64 b = x43
hx31 : ~~~x43 = x31
hx32 : x43.rotateRight 41 = x32
hx33 : x43.rotateRight 18 = x33
hx34 : x43.rotateRight 14 = x34
hx30 : x43 &&& x35 = x30
x44 : BitVec (63 - 0 + 1)
hx44 : BitVec.extractLsb 63 0 b = x44
hx1 : x2 + x44 = x1
hx5 : x44 + x6 = x5
⊢ x2 ++
      ((x1 &&& x43 ^^^ ~~~x1 &&& x35) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        BitVec.extractLsb 63 0 x4) =
    x6 ++
      (x42 + (x5.rotateRight 14 ^^^ x5.rotateRight 18 ^^^ x5.rotateRight 41) + (x5 &&& x43 ^^^ ~~~x5 &&& x35) + x39 +
        x41)
-/
#guard_msgs in theorem sha512h_rule_1 (a b c d e : BitVec 128) :
  let elements := 2
  let esize := 64
  let inner_sum := (binary_vector_op_aux 0 elements esize BitVec.add c d (BitVec.zero 128) H)
  let outer_sum := (binary_vector_op_aux 0 elements esize BitVec.add inner_sum e (BitVec.zero 128) H)
  let a0 := extractLsb 63 0   a
  let a1 := extractLsb 127 64 a
  let b0 := extractLsb 63 0   b
  let b1 := extractLsb 127 64 b
  let c0 := extractLsb 63 0   c
  let c1 := extractLsb 127 64 c
  let d0 := extractLsb 63 0   d
  let d1 := extractLsb 127 64 d
  let e0 := extractLsb 63 0   e
  let e1 := extractLsb 127 64 e
  let hi64_spec := compression_update_t1 b1 a0 a1 c1 d1 e1
  let lo64_spec := compression_update_t1 (b0 + hi64_spec) b1 a0 c0 d0 e0
  sha512h a b outer_sum = hi64_spec ++ lo64_spec := by
  simp_all! only [Nat.sub_zero];
  repeat (unfold binary_vector_op_aux elem_set elem_get; simp)
  unfold BitVec.partInstall
  unfold sha512h compression_update_t1 sigma_big_1 ch allOnes ror
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_zero, Nat.reducePow, reduceZeroExtend,
    reduceHShiftLeft, reduceNot, reduceAnd, BitVec.zero_or, shiftLeft_zero_eq]
  cse (config := { minOccsToCSE := 2})
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
x1 x2 : BitVec 64
x3 : BitVec (127 - 64 + 1)
x4 : BitVec 128
hx3 : BitVec.extractLsb 127 64 x4 = x3
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
x11 : BitVec 64
x12 : BitVec (63 - 0 + 1)
x13 : BitVec (127 - 64 + 1)
x14 : BitVec 64
x15 : BitVec (191 - 64 + 1)
hx12 : BitVec.extractLsb 63 0 x15 = x12
hx13 : BitVec.extractLsb 127 64 x15 = x13
x16 : BitVec 256
hx15 : BitVec.extractLsb 191 64 x16 = x15
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
x24 x25 : BitVec 128
hx24 : x25 <<< 64 = x24
x26 : BitVec 64
x27 : BitVec 128
hx20 : x27 ||| x24 = x20
x28 : BitVec 64
hx21 : x28 ^^^ x26 = x21
x29 : BitVec 64
hx25 : BitVec.zeroExtend 128 x29 = x25
x30 : BitVec 64
hx27 : BitVec.zeroExtend 128 x30 = x27
x31 x32 x33 : BitVec 64
hx22 : x23 ^^^ x33 = x22
x34 : BitVec 64
hx23 : x31 ^^^ x34 = x23
x35 : BitVec (63 - 0 + 1)
hx35 : BitVec.extractLsb 63 0 d = x35
hx14 : x17 + x35 = x14
x36 : BitVec (63 - 0 + 1)
hx36 : BitVec.extractLsb 63 0 c = x36
hx10 : x36 + x12 = x10
x37 : BitVec (127 - 64 + 1)
hx37 : BitVec.extractLsb 127 64 b = x37
hx31 : x37.rotateRight 14 = x31
hx32 : ~~~x37 = x32
hx33 : x37.rotateRight 41 = x33
hx34 : x37.rotateRight 18 = x34
x38 : BitVec (127 - 64 + 1)
hx38 : BitVec.extractLsb 127 64 d = x38
x39 : BitVec (127 - 64 + 1)
hx39 : BitVec.extractLsb 127 64 a = x39
hx26 : x32 &&& x39 = x26
x40 : BitVec (127 - 64 + 1)
hx40 : BitVec.extractLsb 127 64 e = x40
hx29 : x38 + x40 = x29
x41 : BitVec (63 - 0 + 1)
hx41 : BitVec.extractLsb 63 0 b = x41
hx1 : x2 + x41 = x1
hx6 : x41 + x11 = x6
x42 : BitVec (127 - 64 + 1)
hx42 : BitVec.extractLsb 127 64 c = x42
hx9 : x42 + x13 = x9
hx19 : x42 + x22 = x19
x43 : BitVec (63 - 0 + 1)
hx43 : BitVec.extractLsb 63 0 a = x43
hx28 : x37 &&& x43 = x28
x44 : BitVec (63 - 0 + 1)
hx44 : BitVec.extractLsb 63 0 e = x44
hx11 : x14 + x44 = x11
hx30 : x35 + x44 = x30
⊢ x2 ++
      ((x1 &&& x37 ^^^ ~~~x1 &&& x43) + (x1.rotateRight 14 ^^^ x1.rotateRight 18 ^^^ x1.rotateRight 41) +
        BitVec.extractLsb 63 0 x4) =
    x11 ++
      (x36 + (x6.rotateRight 14 ^^^ x6.rotateRight 18 ^^^ x6.rotateRight 41) + (x6 &&& x37 ^^^ ~~~x6 &&& x43) + x38 +
        x40)
-/
#guard_msgs in theorem sha512h_rule_2 (a b c d e : BitVec 128) :
  let a0 := extractLsb 63 0   a
  let a1 := extractLsb 127 64 a
  let b0 := extractLsb 63 0   b
  let b1 := extractLsb 127 64 b
  let c0 := extractLsb 63 0   c
  let c1 := extractLsb 127 64 c
  let d0 := extractLsb 63 0   d
  let d1 := extractLsb 127 64 d
  let e0 := extractLsb 63 0   e
  let e1 := extractLsb 127 64 e
  let inner_sum := binary_vector_op_aux 0 2 64 BitVec.add d e (BitVec.zero 128) h1
  let concat := inner_sum ++ inner_sum
  let operand := extractLsb 191 64 concat
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
  cse
  trace_state
  all_goals sorry

end SHA
