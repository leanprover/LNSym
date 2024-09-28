/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/

/-
In this file, we test our `simp_mem_lint` tactic which lints the current goal state for
bitvec expessions that are poorly understood by the bitblaster.
-/
import Arm.Memory.SeparateAutomation


/--
warning: BitVec.ofNat 64 (x + 1) has a call of 'HAdd.hAdd' with a `Nat` argument. Here be dragons 💀.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in def lintAdd (x : Nat) : BitVec.ofNat 64 (x + 1) = 0#64 := by
  simp_mem_lint
  sorry

/--
warning: declaration uses 'sorry'
-/
#guard_msgs in def noLintAppOfNonNatFn (xs : List Int) : BitVec.ofNat 64 (xs.length) = 0#64 := by
  simp_mem_lint
  sorry


/--
warning: BitVec.ofNat 64 (xs.length * 8) has a call of 'HMul.hMul' with a `Nat` argument. Here be dragons 💀.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in def lintMul (xs : List Int) : BitVec.ofNat 64 (xs.length * 8) = 0#64 := by
  simp_mem_lint
  sorry

/--
warning: 'BitVec.ofNat 64 x.toNat' has a bitvector value being converted to a Nat. Here be dragons 💀.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in def lintOfNatToNat (x : BitVec 64) : (BitVec.ofNat 64 x.toNat) = 0#64 := by
  simp_mem_lint
  sorry

/--
warning: '↑x.toNat' casting a bitvector to a Nat. Here be dragons 💀.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in def lintOfNatCoe (x : BitVec 64) : (x.toNat  : BitVec 64) = 0#64 := by
  simp_mem_lint
  sorry

/--
warning: '↑n' casting a bitvector to a Nat. Here be dragons 💀.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in def lintOfNatCoe' (n : Nat) : (↑ n) + 0#64 = 0#64 := by
  simp_mem_lint
  sorry

/--
warning: '↑(xs.length * 8)' casting a bitvector to a Nat. Here be dragons 💀.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in def eg₁ (xs : List Int) :
  mem_separate' ktbl_addr (↑(xs.length * 8)) (SP + 0xfffffffffffffff0#64) ↑16 := by
    simp_mem_lint
    sorry
