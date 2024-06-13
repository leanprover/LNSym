/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec

namespace AESHWCtr32EncryptBlocksProgram

open BitVec

/-
  void aes_hw_ctr32_encrypt_blocks(const uint8_t *in, uint8_t *out, size_t len,
                                   const AES_KEY *key, const uint8_t ivec[16]);

  input: in - message blocks (x0)
         len - number of message blocks (x2)
         key - AES key schedule and rounds (x3)
         ivec - counter (x4)
  output: out - ciphertext (x1)

-/

def aes_hw_ctr32_encrypt_blocks_program : program :=
  def_program
  [ -- 000000000079f8a0 <aes_hw_ctr32_encrypt_blocks>:
    (0x79f8a0#64,  0xa9bf7bfd#32),   -- stp  x29, x30, [sp, #-16]!
    (0x79f8a4#64,  0x910003fd#32),   -- mov  x29, sp
    (0x79f8a8#64,  0xb940f065#32),   -- ldr  w5, [x3, #240]
    (0x79f8ac#64,  0xb9400c88#32),   -- ldr  w8, [x4, #12]
    (0x79f8b0#64,  0x4c407880#32),   -- ld1  {v0.4s}, [x4]
    (0x79f8b4#64,  0x4c40a870#32),   -- ld1  {v16.4s, v17.4s}, [x3]
    (0x79f8b8#64,  0x510010a5#32),   -- sub  w5, w5, #0x4
    (0x79f8bc#64,  0xd280020c#32),   -- mov  x12, #0x10                    // #16
    (0x79f8c0#64,  0xf100085f#32),   -- cmp  x2, #0x2
    (0x79f8c4#64,  0x8b051067#32),   -- add  x7, x3, x5, lsl #4
    (0x79f8c8#64,  0x510008a5#32),   -- sub  w5, w5, #0x2
    (0x79f8cc#64,  0x4cdfa8f4#32),   -- ld1  {v20.4s, v21.4s}, [x7], #32
    (0x79f8d0#64,  0x4cdfa8f6#32),   -- ld1  {v22.4s, v23.4s}, [x7], #32
    (0x79f8d4#64,  0x4c4078e7#32),   -- ld1  {v7.4s}, [x7]
    (0x79f8d8#64,  0x91008067#32),   -- add  x7, x3, #0x20
    (0x79f8dc#64,  0x2a0503e6#32),   -- mov  w6, w5
    (0x79f8e0#64,  0x9a8c33ec#32),   -- csel  x12, xzr, x12, cc  // cc = lo, ul, last
    (0x79f8e4#64,  0x5ac00908#32),   -- rev  w8, w8
    (0x79f8e8#64,  0x1100050a#32),   -- add  w10, w8, #0x1
    (0x79f8ec#64,  0x4ea01c06#32),   -- mov  v6.16b, v0.16b
    (0x79f8f0#64,  0x5ac0094a#32),   -- rev  w10, w10
    (0x79f8f4#64,  0x4e1c1d46#32),   -- mov  v6.s[3], w10
    (0x79f8f8#64,  0x11000908#32),   -- add  w8, w8, #0x2
    (0x79f8fc#64,  0x4ea61cc1#32),   -- mov  v1.16b, v6.16b
    (0x79f900#64,  0x54000b89#32),   -- b.ls  79fa70 <.Lctr32_tail>  // b.plast
    (0x79f904#64,  0x5ac0090c#32),   -- rev  w12, w8
    (0x79f908#64,  0x4e1c1d86#32),   -- mov  v6.s[3], w12
    (0x79f90c#64,  0xd1000c42#32),   -- sub  x2, x2, #0x3
    (0x79f910#64,  0x4ea61cd2#32),   -- mov  v18.16b, v6.16b
    (0x79f914#64,  0x14000003#32),   -- b  79f920 <.Loop3x_ctr32>
    (0x79f918#64,  0xd503201f#32),   -- nop
    (0x79f91c#64,  0xd503201f#32),   -- nop

    -- 000000000079f920 <.Loop3x_ctr32>:
    (0x79f920#64,  0x4e284a00#32),   -- aese  v0.16b, v16.16b
    (0x79f924#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79f928#64,  0x4e284a01#32),   -- aese  v1.16b, v16.16b
    (0x79f92c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79f930#64,  0x4e284a12#32),   -- aese  v18.16b, v16.16b
    (0x79f934#64,  0x4e286a52#32),   -- aesmc  v18.16b, v18.16b
    (0x79f938#64,  0x4cdf78f0#32),   -- ld1  {v16.4s}, [x7], #16
    (0x79f93c#64,  0x710008c6#32),   -- subs  w6, w6, #0x2
    (0x79f940#64,  0x4e284a20#32),   -- aese  v0.16b, v17.16b
    (0x79f944#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79f948#64,  0x4e284a21#32),   -- aese  v1.16b, v17.16b
    (0x79f94c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79f950#64,  0x4e284a32#32),   -- aese  v18.16b, v17.16b
    (0x79f954#64,  0x4e286a52#32),   -- aesmc  v18.16b, v18.16b
    (0x79f958#64,  0x4cdf78f1#32),   -- ld1  {v17.4s}, [x7], #16
    (0x79f95c#64,  0x54fffe2c#32),   -- b.gt  79f920 <.Loop3x_ctr32>
    (0x79f960#64,  0x4e284a00#32),   -- aese  v0.16b, v16.16b
    (0x79f964#64,  0x4e286804#32),   -- aesmc  v4.16b, v0.16b
    (0x79f968#64,  0x4e284a01#32),   -- aese  v1.16b, v16.16b
    (0x79f96c#64,  0x4e286825#32),   -- aesmc  v5.16b, v1.16b
    (0x79f970#64,  0x4cdf7002#32),   -- ld1  {v2.16b}, [x0], #16
    (0x79f974#64,  0x11000509#32),   -- add  w9, w8, #0x1
    (0x79f978#64,  0x4e284a12#32),   -- aese  v18.16b, v16.16b
    (0x79f97c#64,  0x4e286a52#32),   -- aesmc  v18.16b, v18.16b
    (0x79f980#64,  0x4cdf7003#32),   -- ld1  {v3.16b}, [x0], #16
    (0x79f984#64,  0x5ac00929#32),   -- rev  w9, w9
    (0x79f988#64,  0x4e284a24#32),   -- aese  v4.16b, v17.16b
    (0x79f98c#64,  0x4e286884#32),   -- aesmc  v4.16b, v4.16b
    (0x79f990#64,  0x4e284a25#32),   -- aese  v5.16b, v17.16b
    (0x79f994#64,  0x4e2868a5#32),   -- aesmc  v5.16b, v5.16b
    (0x79f998#64,  0x4cdf7013#32),   -- ld1  {v19.16b}, [x0], #16
    (0x79f99c#64,  0xaa0303e7#32),   -- mov  x7, x3
    (0x79f9a0#64,  0x4e284a32#32),   -- aese  v18.16b, v17.16b
    (0x79f9a4#64,  0x4e286a51#32),   -- aesmc  v17.16b, v18.16b
    (0x79f9a8#64,  0x4e284a84#32),   -- aese  v4.16b, v20.16b
    (0x79f9ac#64,  0x4e286884#32),   -- aesmc  v4.16b, v4.16b
    (0x79f9b0#64,  0x4e284a85#32),   -- aese  v5.16b, v20.16b
    (0x79f9b4#64,  0x4e2868a5#32),   -- aesmc  v5.16b, v5.16b
    (0x79f9b8#64,  0x6e271c42#32),   -- eor  v2.16b, v2.16b, v7.16b
    (0x79f9bc#64,  0x1100090a#32),   -- add  w10, w8, #0x2
    (0x79f9c0#64,  0x4e284a91#32),   -- aese  v17.16b, v20.16b
    (0x79f9c4#64,  0x4e286a31#32),   -- aesmc  v17.16b, v17.16b
    (0x79f9c8#64,  0x6e271c63#32),   -- eor  v3.16b, v3.16b, v7.16b
    (0x79f9cc#64,  0x11000d08#32),   -- add  w8, w8, #0x3
    (0x79f9d0#64,  0x4e284aa4#32),   -- aese  v4.16b, v21.16b
    (0x79f9d4#64,  0x4e286884#32),   -- aesmc  v4.16b, v4.16b
    (0x79f9d8#64,  0x4e284aa5#32),   -- aese  v5.16b, v21.16b
    (0x79f9dc#64,  0x4e2868a5#32),   -- aesmc  v5.16b, v5.16b
    (0x79f9e0#64,  0x6e271e73#32),   -- eor  v19.16b, v19.16b, v7.16b
    (0x79f9e4#64,  0x4e1c1d26#32),   -- mov  v6.s[3], w9
    (0x79f9e8#64,  0x4e284ab1#32),   -- aese  v17.16b, v21.16b
    (0x79f9ec#64,  0x4e286a31#32),   -- aesmc  v17.16b, v17.16b
    (0x79f9f0#64,  0x4ea61cc0#32),   -- mov  v0.16b, v6.16b
    (0x79f9f4#64,  0x5ac0094a#32),   -- rev  w10, w10
    (0x79f9f8#64,  0x4e284ac4#32),   -- aese  v4.16b, v22.16b
    (0x79f9fc#64,  0x4e286884#32),   -- aesmc  v4.16b, v4.16b
    (0x79fa00#64,  0x4e1c1d46#32),   -- mov  v6.s[3], w10
    (0x79fa04#64,  0x5ac0090c#32),   -- rev  w12, w8
    (0x79fa08#64,  0x4e284ac5#32),   -- aese  v5.16b, v22.16b
    (0x79fa0c#64,  0x4e2868a5#32),   -- aesmc  v5.16b, v5.16b
    (0x79fa10#64,  0x4ea61cc1#32),   -- mov  v1.16b, v6.16b
    (0x79fa14#64,  0x4e1c1d86#32),   -- mov  v6.s[3], w12
    (0x79fa18#64,  0x4e284ad1#32),   -- aese  v17.16b, v22.16b
    (0x79fa1c#64,  0x4e286a31#32),   -- aesmc  v17.16b, v17.16b
    (0x79fa20#64,  0x4ea61cd2#32),   -- mov  v18.16b, v6.16b
    (0x79fa24#64,  0xf1000c42#32),   -- subs  x2, x2, #0x3
    (0x79fa28#64,  0x4e284ae4#32),   -- aese  v4.16b, v23.16b
    (0x79fa2c#64,  0x4e284ae5#32),   -- aese  v5.16b, v23.16b
    (0x79fa30#64,  0x4e284af1#32),   -- aese  v17.16b, v23.16b
    (0x79fa34#64,  0x6e241c42#32),   -- eor  v2.16b, v2.16b, v4.16b
    (0x79fa38#64,  0x4cdf78f0#32),   -- ld1  {v16.4s}, [x7], #16
    (0x79fa3c#64,  0x4c9f7022#32),   -- st1  {v2.16b}, [x1], #16
    (0x79fa40#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79fa44#64,  0x2a0503e6#32),   -- mov  w6, w5
    (0x79fa48#64,  0x4c9f7023#32),   -- st1  {v3.16b}, [x1], #16
    (0x79fa4c#64,  0x6e311e73#32),   -- eor  v19.16b, v19.16b, v17.16b
    (0x79fa50#64,  0x4cdf78f1#32),   -- ld1  {v17.4s}, [x7], #16
    (0x79fa54#64,  0x4c9f7033#32),   -- st1  {v19.16b}, [x1], #16
    (0x79fa58#64,  0x54fff642#32),   -- b.cs  79f920 <.Loop3x_ctr32>  // b.hs, b.nlast
    (0x79fa5c#64,  0xb1000c42#32),   -- adds  x2, x2, #0x3
    (0x79fa60#64,  0x54000600#32),   -- b.eq  79fb20 <.Lctr32_done>  // b.none
    (0x79fa64#64,  0xf100045f#32),   -- cmp  x2, #0x1
    (0x79fa68#64,  0xd280020c#32),   -- mov  x12, #0x10                    // #16
    (0x79fa6c#64,  0x9a8c03ec#32),   -- csel  x12, xzr, x12, eq  // eq = none

    -- 000000000079fa70 <.Lctr32_tail>:
    (0x79fa70#64,  0x4e284a00#32),   -- aese  v0.16b, v16.16b
    (0x79fa74#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79fa78#64,  0x4e284a01#32),   -- aese  v1.16b, v16.16b
    (0x79fa7c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79fa80#64,  0x4cdf78f0#32),   -- ld1  {v16.4s}, [x7], #16
    (0x79fa84#64,  0x710008c6#32),   -- subs  w6, w6, #0x2
    (0x79fa88#64,  0x4e284a20#32),   -- aese  v0.16b, v17.16b
    (0x79fa8c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79fa90#64,  0x4e284a21#32),   -- aese  v1.16b, v17.16b
    (0x79fa94#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79fa98#64,  0x4cdf78f1#32),   -- ld1  {v17.4s}, [x7], #16
    (0x79fa9c#64,  0x54fffeac#32),   -- b.gt  79fa70 <.Lctr32_tail>
    (0x79faa0#64,  0x4e284a00#32),   -- aese  v0.16b, v16.16b
    (0x79faa4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79faa8#64,  0x4e284a01#32),   -- aese  v1.16b, v16.16b
    (0x79faac#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79fab0#64,  0x4e284a20#32),   -- aese  v0.16b, v17.16b
    (0x79fab4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79fab8#64,  0x4e284a21#32),   -- aese  v1.16b, v17.16b
    (0x79fabc#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79fac0#64,  0x4ccc7002#32),   -- ld1  {v2.16b}, [x0], x12
    (0x79fac4#64,  0x4e284a80#32),   -- aese  v0.16b, v20.16b
    (0x79fac8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79facc#64,  0x4e284a81#32),   -- aese  v1.16b, v20.16b
    (0x79fad0#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79fad4#64,  0x4c407003#32),   -- ld1  {v3.16b}, [x0]
    (0x79fad8#64,  0x4e284aa0#32),   -- aese  v0.16b, v21.16b
    (0x79fadc#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79fae0#64,  0x4e284aa1#32),   -- aese  v1.16b, v21.16b
    (0x79fae4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79fae8#64,  0x6e271c42#32),   -- eor  v2.16b, v2.16b, v7.16b
    (0x79faec#64,  0x4e284ac0#32),   -- aese  v0.16b, v22.16b
    (0x79faf0#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x79faf4#64,  0x4e284ac1#32),   -- aese  v1.16b, v22.16b
    (0x79faf8#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x79fafc#64,  0x6e271c63#32),   -- eor  v3.16b, v3.16b, v7.16b
    (0x79fb00#64,  0x4e284ae0#32),   -- aese  v0.16b, v23.16b
    (0x79fb04#64,  0x4e284ae1#32),   -- aese  v1.16b, v23.16b
    (0x79fb08#64,  0xf100045f#32),   -- cmp  x2, #0x1
    (0x79fb0c#64,  0x6e201c42#32),   -- eor  v2.16b, v2.16b, v0.16b
    (0x79fb10#64,  0x6e211c63#32),   -- eor  v3.16b, v3.16b, v1.16b
    (0x79fb14#64,  0x4c9f7022#32),   -- st1  {v2.16b}, [x1], #16
    (0x79fb18#64,  0x54000040#32),   -- b.eq  79fb20 <.Lctr32_done>  // b.none
    (0x79fb1c#64,  0x4c007023#32),   -- st1  {v3.16b}, [x1]

    -- 000000000079fb20 <.Lctr32_done>:
    (0x79fb20#64,  0xf84107fd#32),   -- ldr  x29, [sp], #16
    (0x79fb24#64,  0xd65f03c0#32),   -- ret
  ]

end AESHWCtr32EncryptBlocksProgram
