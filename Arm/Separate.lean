/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.State

section Separate

open Std.BitVec

----------------------------------------------------------------------

-- [x1, x2] denotes a memory region X whose first address is x1 and
-- last address is x2. Note that empty memory regions are ruled out by
-- this formalization.

-- All addresses are 64-bit bitvectors.

-- Note that the `-` operation in the definitions in this file is
-- bitvector subtraction, i.e.,
-- let x and y be n-bit bitvectors:
-- BV2Nat (x - y) =
-- (Nat.mod (Nat.add (BV2Nat x) (Nat.sub 2^n (BV2Nat y))) 2^n).

----------------------------------------------------------------------
-- `mem_overlap`: returns true when memory regions A and B overlap.
--
-- Here is some intuition for this definition: in the first two
-- disjuncts, the frame of reference on the number line (which is
-- really a circle for modular arithmetic) is a1, and in the last two
-- disjuncts, the frame is b1.
--
-- Here are some examples:
--
-- Example 1: The first part of B overlaps with the second part of A;
-- no region wraps around.
--
-- Original number line:
--
--   0     a1    b1    a2    b2
--   |-----|-----|-----|-----|-----...
--
-- Number line with a1 as the frame of reference: b1 <= a2 is true.
--
--   a1     b1    a2    b2
--   |-----|-----|-----|--------...
--
-- Example 2: A and B overlap, and B wraps around (note b2 appears
-- before b1 on the number line).
--
-- Original number line:
--
--   0     a1    b2    a2    b1
--   |-----|-----|-----|-----|-----...
--
-- Number line with a1 as the frame of reference: b2 <= a2 is true.
--
--   a1     b2    a2    b1
--   |-----|-----|-----|--------...
--
-- Example 3: A and B overlap, and B wraps around again.
--
-- Original number line:
--
--   0     a1    a2    b2    b1
--   |-----|-----|-----|-----|-----...
--
-- Number line with b1 as the frame of reference: a1 <= b2 is true (as
-- is a2 <= b2 for this example).
--
--   b1     a1    a2    b2
--   |-----|-----|-----|--------...
--
--
def mem_overlap (a1 a2 b1 b2 : BitVec 64) : Bool :=
  b1 - a1 <= a2 - a1 ||
  b2 - a1 <= a2 - a1 ||
  a1 - b1 <= b2 - b1 ||
  a2 - b1 <= b2 - b1

----------------------------------------------------------------------
-- `mem_separate`: returns true when memory regions A and B are
-- separate from each other.

def mem_separate (a1 a2 b1 b2 : BitVec 64) : Bool :=
  not (mem_overlap a1 a2 b1 b2)

----------------------------------------------------------------------
-- `mem_subset`: returns true when A is a subset of B.
def mem_subset (a1 a2 b1 b2 : BitVec 64) : Bool :=
  (b2 - b1 = (2^64 - 1)#64) ||
  ((a2 - b1 <= b2 - b1 && a1 - b1 <= a2 - b1))

example : mem_subset 0#64 2#64 0#64 10#64 = true := rfl

example : mem_subset 8#64 10#64 8#64 2#64 = true := rfl

example : mem_subset 10#64 1#64 8#64 2#64 = true := rfl

example : mem_subset 0#64 1#64 8#64 2#64 = true := rfl

example : mem_subset 0#64 2#64 (2^64 - 1)#64 10#64 = true := rfl

-- The second region is just 2 bytes long, but the first one spans the
-- whole memory.
example : mem_subset 0#64 (2^64 - 1)#64 (2^64 - 1)#64 0#64 = false := rfl

-- Every region is a subset of the whole memory.
example : mem_subset (2^64 - 1)#64 0#64 0#64 (2^64 - 1)#64 = true := rfl

----------------------------------------------------------------------
-- `mem_legal`: returns true when the specified region does not wrap
-- around.
def mem_legal (a1 a2 : BitVec 64) : Bool :=
  a1 <= a2

end Separate

----------------------------------------------------------------------
