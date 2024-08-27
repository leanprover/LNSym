/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat

The goal is to prove that this program implements max correctly.
-/
import Arm
import Arm.BitVec
import Tactics.Sym
import Tactics.StepThms


namespace Max

def program : Program :=
  def_program [
/- 0x0   -/  (0x894#64, 0xd10083ff#32),  --  sub  sp, sp, #0x20  ;
/- 0x4   -/  (0x898#64, 0xb9000fe0#32),  --  str  w0, [sp, #12]  ; sp[12] = w0_a
/- 0x8   -/  (0x89c#64, 0xb9000be1#32),  --  str  w1, [sp, #8]   ; sp[8] = w1_a
/- 0xc   -/  (0x8a0#64, 0xb9400fe1#32),  --  ldr  w1, [sp, #12]  ; w1_b = sp[12]
/- 0x10  -/  (0x8a4#64, 0xb9400be0#32),  --  ldr  w0, [sp, #8]   ; w0_b = sp[8]
/- 0x14  -/  (0x8a8#64, 0x6b00003f#32),  --  cmp  w1, w0         ; w1_b - w0_b
/- 0x18  -/  (0x8ac#64, 0x5400008d#32),  --  b.le 8bc <max+0x28> ;
--                          LOAD FROM sp[8] = w1_a (which is > w0_a) AND STORE IN w0
/- 0x1c  -/  (0x8b0#64, 0xb9400fe0#32),  --  ldr  w0, [sp, #12]  ;  w0_c = sp[12] = w0_a
/- 0x20  -/  (0x8b4#64, 0xb9001fe0#32),  --  str  w0, [sp, #28]  ; sp[28] = w0_c = w0_a
/- 0x24  -/  (0x8b8#64, 0x14000003#32),  --  b  8c4 <max+0x30>   ;
--                          LOAD FROM sp[8] = w1_a (which is > w0_a) AND STORE IN w0
/- 0x28  -/  (0x8bc#64, 0xb9400be0#32),  --  ldr  w0, [sp, #8]   ; w0_d = sp[8] = w1_a
/- 0x2c  -/  (0x8c0#64, 0xb9001fe0#32),  --  str  w0, [sp, #28]  ; sp[28] = w0_d = w1_a
--                              LOAD FROM sp[28] AND STORE IN w0
/- 0x30  -/  (0x8c4#64, 0xb9401fe0#32),  --  ldr  w0, [sp, #28]  ; w0 = sp[28]
/- 0x34  -/  (0x8c8#64, 0x910083ff#32),  --  add  sp, sp, #0x20  ; sp = sp + 0x20
/- 0x38  -/  (0x8cc#64, 0xd65f03c0#32)   --  ret -- return
]

#genStepEqTheorems program

def spec (x y : BitVec 32) : BitVec 32 :=
  if BitVec.slt y x then x else y


end Max
