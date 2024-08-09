import Tactics.CSE

import Arm.Insts.DPSFP.Insts
import Specs.SHA512
import LeanSAT
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
info: [Tactic.cse.generalize] ⏭️ Skipping 64#64: Unprofitable { occs := 1, size := 5 } .
[Tactic.cse.generalize] ⌛ Generalizing hx1 : 64 = x1
[Tactic.cse.generalize] 💥 failed to generalize hx1
[Tactic.cse.generalize] ⏭️ Skipping x: Unprofitable { occs := 1, size := 1 } .
[Tactic.cse.generalize] ⏭️ Skipping 64: Unprofitable { occs := 2, size := 1 } .
-/
#guard_msgs in example (x : BitVec 64) : (BitVec.ofNat 64 64) = x := by
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
x16 : BitVec (127 - 64 + 1)
x17 : BitVec (63 - 0 + 1)
x18 : BitVec 128
hx16 : BitVec.extractLsb 127 64 x18 = x16
hx17 : BitVec.extractLsb 63 0 x18 = x17
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
hx21 : x29 ^^^ x27 = x21
x30 : BitVec 64
hx25 : BitVec.zeroExtend 128 x30 = x25
x31 x32 : BitVec 64
hx20 : x23 ^^^ x32 = x20
x33 : BitVec 64
hx23 : x33 ^^^ x31 = x23
x34 : BitVec 64
x35 : BitVec (63 - 0 + 1)
hx35 : BitVec.extractLsb 63 0 e = x35
hx14 : x17 + x35 = x14
x36 : BitVec (63 - 0 + 1)
hx36 : BitVec.extractLsb 63 0 c = x36
x37 : BitVec (127 - 64 + 1)
hx37 : BitVec.extractLsb 127 64 b = x37
hx34 : ~~~x37 = x34
x38 : BitVec (127 - 64 + 1)
hx38 : BitVec.extractLsb 127 64 a = x38
hx27 : x34 &&& x38 = x27
x39 : BitVec (127 - 64 + 1)
hx39 : BitVec.extractLsb 127 64 c = x39
hx19 : x39 + x20 = x19
x40 : BitVec (63 - 0 + 1)
hx40 : BitVec.extractLsb 63 0 d = x40
hx30 : x36 + x40 = x30
x41 : BitVec (63 - 0 + 1)
hx41 : BitVec.extractLsb 63 0 a = x41
hx29 : x37 &&& x41 = x29
x42 : BitVec (63 - 0 + 1)
hx42 : BitVec.extractLsb 63 0 b = x42
hx1 : x2 + x42 = x1
hx5 : x42 + x6 = x5
x43 : BitVec (127 - 64 + 1)
hx43 : BitVec.extractLsb 127 64 e = x43
hx6 : x7 + x43 = x6
hx15 : x16 + x43 = x15
x44 : BitVec (127 - 64 + 1)
hx44 : BitVec.extractLsb 127 64 d = x44
hx7 : x8 + x44 = x7
hx28 : x39 + x44 = x28
x45 : BitVec 128
hx9 : x12 &&& x45 = x9
hx22 : x25 &&& x45 = x22
x46 : Nat
hx46 : 18 = x46
hx31 : x37.rotateRight x46 = x31
x50 : Nat
hx50 : 18446744073709551615 = x50
hx45 : BitVec.ofNat 128 x50 = x45
x51 : Nat
hx51 : 14 = x51
hx33 : x37.rotateRight x51 = x33
x52 : Nat
hx52 : 41 = x52
hx32 : x37.rotateRight x52 = x32
⊢ x2 ++
      ((x1 &&& x37 ^^^ ~~~x1 &&& x41) + (x1.rotateRight x51 ^^^ x1.rotateRight x46 ^^^ x1.rotateRight x52) +
        BitVec.extractLsb 63 0 x4) =
    x6 ++
      (x36 + (x5.rotateRight x51 ^^^ x5.rotateRight x46 ^^^ x5.rotateRight x52) + (x5 &&& x37 ^^^ ~~~x5 &&& x41) + x40 +
        x35)
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
x5 x6 : BitVec 128
hx4 : x6 ||| x5 = x4
x7 : BitVec 128
hx5 : x7 <<< 64 = x5
x8 : BitVec 64
hx6 : BitVec.zeroExtend 128 x8 = x6
x9 : BitVec 64
hx7 : BitVec.zeroExtend 128 x9 = x7
x10 : BitVec 64
x11 : BitVec (127 - 64 + 1)
x12 : BitVec (63 - 0 + 1)
x13 : BitVec 64
x14 : BitVec (191 - 64 + 1)
hx11 : BitVec.extractLsb 127 64 x14 = x11
hx12 : BitVec.extractLsb 63 0 x14 = x12
x15 : BitVec 256
hx14 : BitVec.extractLsb 191 64 x15 = x14
x16 x17 x18 : BitVec 64
hx2 : x18 + x3 = x2
x19 : BitVec 128
hx15 : x19 ++ x19 = x15
x20 x21 x22 : BitVec 64
hx17 : x20 + x22 = x17
hx18 : x22 + x21 = x18
x23 : BitVec 64
x24 x25 : BitVec 128
hx19 : x25 ||| x24 = x19
x26 : BitVec 128
hx24 : x26 <<< 64 = x24
x27 x28 : BitVec 64
hx22 : x28 ^^^ x27 = x22
x29 : BitVec 64
hx26 : BitVec.zeroExtend 128 x29 = x26
x30 : BitVec 64
hx25 : BitVec.zeroExtend 128 x30 = x25
x31 : BitVec 64
hx21 : x23 ^^^ x31 = x21
x32 x33 : BitVec 64
hx23 : x33 ^^^ x32 = x23
x34 : BitVec 64
x35 : BitVec (63 - 0 + 1)
hx35 : BitVec.extractLsb 63 0 c = x35
hx8 : x35 + x12 = x8
x36 : BitVec (127 - 64 + 1)
hx36 : BitVec.extractLsb 127 64 b = x36
hx34 : ~~~x36 = x34
x37 : BitVec (63 - 0 + 1)
hx37 : BitVec.extractLsb 63 0 e = x37
hx13 : x16 + x37 = x13
x38 : BitVec (63 - 0 + 1)
hx38 : BitVec.extractLsb 63 0 a = x38
hx28 : x36 &&& x38 = x28
x39 : BitVec (127 - 64 + 1)
hx39 : BitVec.extractLsb 127 64 a = x39
hx27 : x34 &&& x39 = x27
x40 : BitVec (63 - 0 + 1)
hx40 : BitVec.extractLsb 63 0 b = x40
hx1 : x2 + x40 = x1
hx10 : x40 + x13 = x10
x41 : BitVec (63 - 0 + 1)
hx41 : BitVec.extractLsb 63 0 d = x41
hx16 : x17 + x41 = x16
hx30 : x41 + x37 = x30
x42 : BitVec (127 - 64 + 1)
hx42 : BitVec.extractLsb 127 64 e = x42
x43 : BitVec (127 - 64 + 1)
hx43 : BitVec.extractLsb 127 64 d = x43
hx29 : x43 + x42 = x29
x44 : BitVec (127 - 64 + 1)
hx44 : BitVec.extractLsb 127 64 c = x44
hx9 : x44 + x11 = x9
hx20 : x44 + x21 = x20
x46 : Nat
hx46 : 41 = x46
hx31 : x36.rotateRight x46 = x31
x48 : Nat
hx48 : 14 = x48
hx33 : x36.rotateRight x48 = x33
x53 : Nat
hx53 : 18 = x53
hx32 : x36.rotateRight x53 = x32
⊢ x2 ++
      ((x1 &&& x36 ^^^ ~~~x1 &&& x38) + (x1.rotateRight x48 ^^^ x1.rotateRight x53 ^^^ x1.rotateRight x46) +
        BitVec.extractLsb 63 0 x4) =
    x13 ++
      (x35 + (x10.rotateRight x48 ^^^ x10.rotateRight x53 ^^^ x10.rotateRight x46) + (x10 &&& x36 ^^^ ~~~x10 &&& x38) +
          x43 +
        x42)
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
