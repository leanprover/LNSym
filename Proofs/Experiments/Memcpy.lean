/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

The goal is to prove that this program implements memcpy correctly.
-/
import Arm

def ArmState.x (n : Nat) : ArmState → BitVec 64
| s => read_gpr 64 n s

def ArmState.x0 := ArmState.x 0
def ArmState.x1 := ArmState.x 1
def ArmState.x2 := ArmState.x 2


namespace Memcpy
def program : Program :=
  def_program
    [
     /- 00000000000008e0 <mem_copy>:                         -/
     (0x8e0#64, 0x14000004#32),  /- b   8f0 <loop_test>      -/
     /- 00000000000008e4 <mem_copy_loop>:                    -/
     (0x8e4#64, 0x3cc10424#32),  /- ldr q4, [x1], #16        -/
     (0x8e8#64, 0x3c810444#32),  /- str q4, [x2], #16        -/
     (0x8ec#64, 0xd1000400#32),  /- sub x0, x0, #0x1         -/
     /- 00000000000008f0 <loop_test>:                        -/
     (0x8f0#64, 0xf100001f#32),  /- cmp x0, #0x0             -/
     (0x8f4#64, 0x54ffff81#32),  /- b.ne 8e4 <mem_copy_loop> -/
     (0x8f8#64, 0xd65f03c0#32)   /- ret                      -/
    ]

def spec (x y : BitVec 32) : BitVec 32 :=
  if BitVec.slt y x then x else y


structure Correct (s0 sf : ArmState) : Prop where
  /-- The destination in the final state is a copy of the source in the initial state. -/
  hdest : read_mem_bytes s0.x0.toNat x₂ sf = read_mem_bytes s0.x0.toNat x₁ s0
  /-- All memory regions that do not overlap with the destination are unchanged. -/
  hdisjoint : ∀ (n : Nat)
    (addr : BitVec 64)
    (hsep : mem_separate s0.x2 (s0.x2 + s0.x0 - 1) addr (addr + (BitVec.ofNat _ n) - 1)),
      read_mem_bytes n addr sf = read_mem_bytes n addr s0
  herr : read_err sf  = .None

/-
Note that the theorem also holds when src = dest, but does *not* hold
when src and dest overlap.

num bytes to be copied is x0.
src address is in x1.
dest address is in x2.
-/
theorem correct_separate
  {s0 sf : ArmState}
  (h_s0_pc : read_pc s0 = 0x4005d0#64)
  (h_s0_program : s0.program = int_abs_program)
  (h_s0_err : read_err s0 = StateError.None)
  (h_run : sf = run program.length s0)
  (hx₀ : x₀ = read_gpr 64 0 s0)
  (hx₁ : x₁ = read_gpr 64 1 s0)
  (hx₂ : x₂ = read_gpr 64 2 s0)
  (h_s0_mem : mem_separate  x₁ (x₀ + x₁ - 1) x₂ (x₂ + x₀ - 1)) : -- TODO: These are closed intervals.
  Correct s0 sf := sorry

end Memcpy
