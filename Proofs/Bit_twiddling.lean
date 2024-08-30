/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Nathan Wetzler

The goal is to stress-test LeanSAT's performance using some classic
bit-twiddling problems as benchmarks.
-/

import Std.Tactic.BVDecide

namespace BitTwiddlingTests

open BitVec

notation:50 x " ≤ᵤ " y => BitVec.ule x y
notation:50 x " <ᵤ " y => BitVec.ult x y
notation:50 x " ≥ᵤ " y => BitVec.ule y x
notation:50 x " >ᵤ " y => BitVec.ult y x

notation:50 x " ≤ₛ " y => BitVec.sle x y
notation:50 x " <ₛ " y => BitVec.slt x y
notation:50 x " ≥ₛ " y => BitVec.sle y x
notation:50 x " >ₛ " y => BitVec.slt y x

notation:50 x " >>>ᵤ " y => BitVec.ushiftRight x y
notation:50 x " >>>ₛ " y => BitVec.sshiftRight x y
-- notation:50 x " <<< " y => BitVec.shiftLeft x y

-- Note that replacing 0 with 0#32 in some lemmas below will remove the need for ofNat_eq_ofNat.

-- ============================================================

/--
1. Compute the sign of an integer
(https://graphics.stanford.edu/~seander/bithacks.html#CopyIntegerSign)

int v;      // we want to find the sign of v
int sign;   // the result goes here

// CHAR_BIT is the number of bits per byte (normally 8).
sign = -(v < 0);  // if v < 0 then -1, else 0.
// or, for one less instruction (but not portable):
sign = v >> (sizeof(int) * CHAR_BIT - 1);
-/
def c_slt {n : Nat} (x : BitVec n) (y : BitVec n) : (BitVec n) :=
  if (x <ₛ y) then 1 else 0

theorem computing_sign (x : BitVec 32) :
  (x <ₛ 0#32) ↔ ((x >>>ₛ 31) = -1#32) := by
  bv_decide

theorem computing_sign1 (x : BitVec 32) :
  -(c_slt x 0#32) = (x >>>ₛ 31) := by
  unfold c_slt
  split <;> bv_decide

-- ============================================================

/--
2. Detect if two integers have opposite signs
(https://graphics.stanford.edu/~seander/bithacks.html#DetectOppositeSigns)

int x, y;               // input values to compare signs

bool f = ((x ^ y) < 0); // true iff x and y have opposite signs
-/
theorem opposite_signs (x : BitVec 32) (y : BitVec 32) :
  ((0#32 ≤ₛ x) ∧ (y <ₛ 0#32)) ∨ ((x <ₛ 0#32) ∧ (0#32 ≤ₛ y)) ↔ ((x ^^^ y) <ₛ 0#32) := by
  bv_decide

-- ============================================================

/--
3. Compute the integer absolute value (abs) without branching
(https://graphics.stanford.edu/~seander/bithacks.html#IntegerAbs)

int v;           // we want to find the absolute value of v
unsigned int r;  // the result goes here
int const mask = v >> sizeof(int) * CHAR_BIT - 1;

r = (v + mask) ^ mask;
-/

theorem abs_no_branch (x : BitVec 32) (mask : BitVec 32)
  (h_mask : mask = (x >>>ₛ 31)) :
  (BitVec.abs x) = ((x + mask) ^^^ mask) := by
  unfold BitVec.abs
  split <;> bv_decide

-- ============================================================

/--
4. Compute the minimum (min) or maximum (max) of two integers without branching
(https://graphics.stanford.edu/~seander/bithacks.html#IntegerMinOrMax)

int x;  // we want to find the minimum of x and y
int y;
int r;  // the result goes here

r = y ^ ((x ^ y) & -(x < y)); // min(x, y)

To find the maximum, use:

r = x ^ ((x ^ y) & -(x < y)); // max(x, y)
-/

def bv_min {n : Nat} (x : BitVec n) (y : BitVec n) : (BitVec n) :=
    if (x <ₛ y) then x else y

def bv_max {n : Nat} (x : BitVec n) (y : BitVec n) : (BitVec n) :=
    if (x <ₛ y) then y else x

theorem min_no_branch (x : BitVec 32) (y : BitVec 32) :
  bv_min x y = (y ^^^ ((x ^^^ y) &&& -(c_slt x y))) := by
  unfold bv_min c_slt
  split <;> bv_decide

theorem max_no_branch (x : BitVec 32) (y : BitVec 32) :
  bv_max x y = (x ^^^ ((x ^^^ y) &&& -(c_slt x y))) := by
  unfold bv_max c_slt
  split <;> bv_decide

-- ============================================================

/--
5. Determining if an integer is a power of 2
(https://graphics.stanford.edu/~seander/bithacks.html#DetermineIfPowerOf2)

unsigned int v; // we want to see if v is a power of 2
bool f;         // the result goes here

f = (v & (v - 1)) == 0;

Note that 0 is incorrectly considered a power of 2 here. To remedy this, use:

f = v && !(v & (v - 1));
-/

theorem power_of_two (x : BitVec 32) (i : BitVec 5)
  (hi : (0#5 ≤ i) ∧ (i < 32#5))
  (hx : x = BitVec.twoPow 32 i.toNat) :
  ((x ≠ 0#32) ∧ ((x &&& (x - 1)) = 0#32)) := by
  unfold BitVec.twoPow at hx
  bv_decide

-- Add recursive definition???
-- This is not quite complete because we're only checking the positive case.

-- ============================================================

/--
6. Conditionally set or clear bits without branching
(https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching)

bool f;         // conditional flag
unsigned int m; // the bit mask
unsigned int w; // the word to modify:  if (f) w |= m; else w &= ~m;

w ^= (-f ^ w) & m;
-/

theorem set_clear_no_branch (x : BitVec 32) (f : Bool) (mask : BitVec 32) :
  (if f then (x ||| mask) else (x &&& ~~~mask)) =
  (x ^^^ (((-(BitVec.zeroExtend 32 (BitVec.ofBool f))) ^^^ x) &&& mask)) := by
  split <;> bv_decide

-- ============================================================

/--
7. Conditionally negate a value without branching
(https://graphics.stanford.edu/~seander/bithacks.html#ConditionalNegate)

bool fNegate;  // Flag indicating if we should negate v.
int v;         // Input value to negate if fNegate is true.
int r;         // result = fNegate ? -v : v;

r = (v ^ -fNegate) + fNegate;
-/

theorem negate_no_branch (x : BitVec 32) (fNegate : Bool) :
  (if fNegate then -x else x) =
  ((x ^^^ -(BitVec.zeroExtend 32 (BitVec.ofBool fNegate))) + (BitVec.zeroExtend 32 (BitVec.ofBool fNegate))) := by
  split <;> bv_decide

-- ============================================================

/--
8. Merge bits from two values according to a mask
(https://graphics.stanford.edu/~seander/bithacks.html#MaskedMerge)

unsigned int a;    // value to merge in non-masked bits
unsigned int b;    // value to merge in masked bits
unsigned int mask; // 1 where bits from b should be selected; 0 where from a.
unsigned int r;    // result of (a & ~mask) | (b & mask) goes here

r = a ^ ((a ^ b) & mask);
-/

theorem merge_from_mask (x : BitVec 32) (y : BitVec 32) (mask : BitVec 32) :
  ((x &&& ~~~mask) ||| (y &&& mask)) = (x ^^^ ((x ^^^ y) &&& mask)) := by
  bv_decide

-- ============================================================

/--
9. Counting bits set, in parallel
(https://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel)

v = v - ((v >> 1) & 0x55555555);                    // reuse input as temporary
v = (v & 0x33333333) + ((v >> 2) & 0x33333333);     // temp
c = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24; // count
-/

def popcount32_spec_rec (i : Nat) (x : BitVec 32) : (BitVec 32) :=
  match i with
  | 0 => BitVec.zero 32
  | i' + 1 =>
    let bit_idx := BitVec.extractLsb i' i' x
    let bv_idx := (BitVec.zeroExtend 32 bit_idx)
    (bv_idx + (popcount32_spec_rec i' x))

def popcount32_spec (x : BitVec 32) : BitVec 32 :=
  popcount32_spec_rec 32 x

def popcount32_impl (x : BitVec 32) : BitVec 32 :=
  let x' := x - ((x >>>ᵤ 1) &&& 0x55555555#32)
  let x'' := (x' &&& 0x33333333#32) + ((x' >>>ᵤ 2) &&& 0x33333333#32)
  ((x'' + (x'' >>>ᵤ 4) &&& 0x0f0f0f0f#32) * 0x01010101#32) >>>ᵤ 24

theorem popcount32_correct (x : BitVec 32) :
  (popcount32_spec x) = (popcount32_impl x) := by
  unfold popcount32_spec popcount32_impl
  repeat (unfold popcount32_spec_rec)
  unfold BitVec.zero
  bv_decide

-- ============================================================

/--
10. Compute parity in parallel
(https://graphics.stanford.edu/~seander/bithacks.html#ParityParallel)

unsigned int v;  // word value to compute the parity of
v ^= v >> 16;
v ^= v >> 8;
v ^= v >> 4;
v &= 0xf;
return (0x6996 >> v) & 1;
-/

def parity32_spec_rec (i : Nat) (x : BitVec 32) : Bool :=
  match i with
  | 0 => false
  | i' + 1 =>
    let bit_idx := BitVec.getLsb x i'
    -- let bv_idx := (BitVec.zeroExtend 32 (BitVec.ofBool bit_idx))
    Bool.xor bit_idx (parity32_spec_rec i' x)

def parity32_spec (x : BitVec 32) : Bool :=
  parity32_spec_rec 32 x

def parity32_impl (x : BitVec 32) : BitVec 32 :=
  let x1 := x ^^^ (x >>> 16)
  let x2 := x1 ^^^ (x1 >>> 8)
  let x3 := x2 ^^^ (x2 >>> 4)
  let x4 := x3 &&& 0x0000000f#32
  (0x00006996#32 >>> x4) &&& 1#32

theorem parity32_correct (x : BitVec 32) :
  (parity32_spec x) = ((parity32_impl x).getLsb 0) := by
  unfold parity32_spec parity32_impl
  repeat (unfold parity32_spec_rec)
  bv_decide

end BitTwiddlingTests
