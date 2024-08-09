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
