/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

The goal is to prove that this program implements max correctly.
-/
import Arm 

def max_program : Program :=
  def_program [
  (0x894#64, 0xd10083ff#32),  --         sub  sp, sp, #0x20
  (0x898#64, 0xb9000fe0#32),  --         str  w0, [sp, #12]
  (0x89c#64, 0xb9000be1#32),  --         str  w1, [sp, #8]
  (0x8a0#64, 0xb9400fe1#32),  --         ldr  w1, [sp, #12]
  (0x8a4#64, 0xb9400be0#32),  --         ldr  w0, [sp, #8]
  (0x8a8#64, 0x6b00003f#32),  --         cmp  w1, w0
  (0x8ac#64, 0x5400008d#32),  --         b.le 8bc <max+0x28>
  (0x8b0#64, 0xb9400fe0#32),  --         ldr  w0, [sp, #12]
  (0x8b4#64, 0xb9001fe0#32),  --         str  w0, [sp, #28]
  (0x8b8#64, 0x14000003#32),  --         b  8c4 <max+0x30>
  (0x8bc#64, 0xb9400be0#32),  --         ldr  w0, [sp, #8]
  (0x8c0#64, 0xb9001fe0#32),  --         str  w0, [sp, #28]
  (0x8c4#64, 0xb9401fe0#32),  --         ldr  w0, [sp, #28]
  (0x8c8#64, 0x910083ff#32),  --         add  sp, sp, #0x20
  (0x8cc#64, 0xd65f03c0#32)   --         ret
]

def maxSpec (x y : BitVec 32) : BitVec 32 :=
  if BitVec.slt y x then
    x
  else
    y


def state : ArmState := 
  { 
    ArmState.default with 
    program := max_program, pc := 0x894#64
  }

