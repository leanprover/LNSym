/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

The goal is to prove that this program implements memcpy correctly.
-/
import Arm 

def mem_copy_program : Program :=
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



