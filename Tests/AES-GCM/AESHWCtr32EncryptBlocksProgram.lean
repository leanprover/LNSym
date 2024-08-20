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

def aes_hw_ctr32_encrypt_blocks_program : Program :=
  def_program
  [ -- 00000000007dfe20 <aes_hw_ctr32_encrypt_blocks>:
    (0x7dfe20#64, 0xa9bf7bfd#32),        -- stp     x29, x30, [sp, #-16]!
    (0x7dfe24#64, 0x910003fd#32),        -- mov     x29, sp
    (0x7dfe28#64, 0xb940f065#32),        -- ldr     w5, [x3, #240]
    (0x7dfe2c#64, 0xb9400c88#32),        -- ldr     w8, [x4, #12]
    (0x7dfe30#64, 0x4c407880#32),        -- ld1     {v0.4s}, [x4]
    (0x7dfe34#64, 0x4c40a870#32),        -- ld1     {v16.4s, v17.4s}, [x3]
    (0x7dfe38#64, 0x510010a5#32),        -- sub     w5, w5, #0x4
    (0x7dfe3c#64, 0xd280020c#32),        -- mov     x12, #0x10                      // #16
    (0x7dfe40#64, 0xf100085f#32),        -- cmp     x2, #0x2
    (0x7dfe44#64, 0x8b051067#32),        -- add     x7, x3, x5, lsl #4
    (0x7dfe48#64, 0x510008a5#32),        -- sub     w5, w5, #0x2
    (0x7dfe4c#64, 0x4cdfa8f4#32),        -- ld1     {v20.4s, v21.4s}, [x7], #32
    (0x7dfe50#64, 0x4cdfa8f6#32),        -- ld1     {v22.4s, v23.4s}, [x7], #32
    (0x7dfe54#64, 0x4c4078e7#32),        -- ld1     {v7.4s}, [x7]
    (0x7dfe58#64, 0x91008067#32),        -- add     x7, x3, #0x20
    (0x7dfe5c#64, 0x2a0503e6#32),        -- mov     w6, w5
    (0x7dfe60#64, 0x5ac00908#32),        -- rev     w8, w8
    (0x7dfe64#64, 0x1100050a#32),        -- add     w10, w8, #0x1
    (0x7dfe68#64, 0x4ea01c06#32),        -- mov     v6.16b, v0.16b
    (0x7dfe6c#64, 0x5ac0094a#32),        -- rev     w10, w10
    (0x7dfe70#64, 0x4e1c1d46#32),        -- mov     v6.s[3], w10
    (0x7dfe74#64, 0x11000908#32),        -- add     w8, w8, #0x2
    (0x7dfe78#64, 0x4ea61cc1#32),        -- mov     v1.16b, v6.16b
    (0x7dfe7c#64, 0x54000b49#32),        -- b.ls    7dffe4 <.Lctr32_tail>  // b.plast
    (0x7dfe80#64, 0x5ac0090c#32),        -- rev     w12, w8
    (0x7dfe84#64, 0x4e1c1d86#32),        -- mov     v6.s[3], w12
    (0x7dfe88#64, 0xd1000c42#32),        -- sub     x2, x2, #0x3
    (0x7dfe8c#64, 0x4ea61cd2#32),        -- mov     v18.16b, v6.16b
    (0x7dfe90#64, 0x14000004#32),        -- b       7dfea0 <.Loop3x_ctr32>
    (0x7dfe94#64, 0xd503201f#32),        -- nop
    (0x7dfe98#64, 0xd503201f#32),        -- nop
    (0x7dfe9c#64, 0xd503201f#32),        -- nop

    -- 00000000007dfea0 <.Loop3x_ctr32>:
    (0x7dfea0#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7dfea4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7dfea8#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7dfeac#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7dfeb0#64, 0x4e284a12#32),        -- aese    v18.16b, v16.16b
    (0x7dfeb4#64, 0x4e286a52#32),        -- aesmc   v18.16b, v18.16b
    (0x7dfeb8#64, 0x4cdf78f0#32),        -- ld1     {v16.4s}, [x7], #16
    (0x7dfebc#64, 0x710008c6#32),        -- subs    w6, w6, #0x2
    (0x7dfec0#64, 0x4e284a20#32),        -- aese    v0.16b, v17.16b
    (0x7dfec4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7dfec8#64, 0x4e284a21#32),        -- aese    v1.16b, v17.16b
    (0x7dfecc#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7dfed0#64, 0x4e284a32#32),        -- aese    v18.16b, v17.16b
    (0x7dfed4#64, 0x4e286a52#32),        -- aesmc   v18.16b, v18.16b
    (0x7dfed8#64, 0x4cdf78f1#32),        -- ld1     {v17.4s}, [x7], #16
    (0x7dfedc#64, 0x54fffe2c#32),        -- b.gt    7dfea0 <.Loop3x_ctr32>
    (0x7dfee0#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7dfee4#64, 0x4e286804#32),        -- aesmc   v4.16b, v0.16b
    (0x7dfee8#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7dfeec#64, 0x4e286825#32),        -- aesmc   v5.16b, v1.16b
    (0x7dfef0#64, 0x4cdf7002#32),        -- ld1     {v2.16b}, [x0], #16
    (0x7dfef4#64, 0x11000509#32),        -- add     w9, w8, #0x1
    (0x7dfef8#64, 0x4e284a12#32),        -- aese    v18.16b, v16.16b
    (0x7dfefc#64, 0x4e286a52#32),        -- aesmc   v18.16b, v18.16b
    (0x7dff00#64, 0x4cdf7003#32),        -- ld1     {v3.16b}, [x0], #16
    (0x7dff04#64, 0x5ac00929#32),        -- rev     w9, w9
    (0x7dff08#64, 0x4e284a24#32),        -- aese    v4.16b, v17.16b
    (0x7dff0c#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7dff10#64, 0x4e284a25#32),        -- aese    v5.16b, v17.16b
    (0x7dff14#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7dff18#64, 0x4cdf7013#32),        -- ld1     {v19.16b}, [x0], #16
    (0x7dff1c#64, 0xaa0303e7#32),        -- mov     x7, x3
    (0x7dff20#64, 0x4e284a32#32),        -- aese    v18.16b, v17.16b
    (0x7dff24#64, 0x4e286a51#32),        -- aesmc   v17.16b, v18.16b
    (0x7dff28#64, 0x4e284a84#32),        -- aese    v4.16b, v20.16b
    (0x7dff2c#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7dff30#64, 0x4e284a85#32),        -- aese    v5.16b, v20.16b
    (0x7dff34#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7dff38#64, 0x6e271c42#32),        -- eor     v2.16b, v2.16b, v7.16b
    (0x7dff3c#64, 0x1100090a#32),        -- add     w10, w8, #0x2
    (0x7dff40#64, 0x4e284a91#32),        -- aese    v17.16b, v20.16b
    (0x7dff44#64, 0x4e286a31#32),        -- aesmc   v17.16b, v17.16b
    (0x7dff48#64, 0x6e271c63#32),        -- eor     v3.16b, v3.16b, v7.16b
    (0x7dff4c#64, 0x11000d08#32),        -- add     w8, w8, #0x3
    (0x7dff50#64, 0x4e284aa4#32),        -- aese    v4.16b, v21.16b
    (0x7dff54#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7dff58#64, 0x4e284aa5#32),        -- aese    v5.16b, v21.16b
    (0x7dff5c#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7dff60#64, 0x6e271e73#32),        -- eor     v19.16b, v19.16b, v7.16b
    (0x7dff64#64, 0x4e1c1d26#32),        -- mov     v6.s[3], w9
    (0x7dff68#64, 0x4e284ab1#32),        -- aese    v17.16b, v21.16b
    (0x7dff6c#64, 0x4e286a31#32),        -- aesmc   v17.16b, v17.16b
    (0x7dff70#64, 0x4ea61cc0#32),        -- mov     v0.16b, v6.16b
    (0x7dff74#64, 0x5ac0094a#32),        -- rev     w10, w10
    (0x7dff78#64, 0x4e284ac4#32),        -- aese    v4.16b, v22.16b
    (0x7dff7c#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7dff80#64, 0x4e1c1d46#32),        -- mov     v6.s[3], w10
    (0x7dff84#64, 0x5ac0090c#32),        -- rev     w12, w8
    (0x7dff88#64, 0x4e284ac5#32),        -- aese    v5.16b, v22.16b
    (0x7dff8c#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7dff90#64, 0x4ea61cc1#32),        -- mov     v1.16b, v6.16b
    (0x7dff94#64, 0x4e1c1d86#32),        -- mov     v6.s[3], w12
    (0x7dff98#64, 0x4e284ad1#32),        -- aese    v17.16b, v22.16b
    (0x7dff9c#64, 0x4e286a31#32),        -- aesmc   v17.16b, v17.16b
    (0x7dffa0#64, 0x4ea61cd2#32),        -- mov     v18.16b, v6.16b
    (0x7dffa4#64, 0xf1000c42#32),        -- subs    x2, x2, #0x3
    (0x7dffa8#64, 0x4e284ae4#32),        -- aese    v4.16b, v23.16b
    (0x7dffac#64, 0x4e284ae5#32),        -- aese    v5.16b, v23.16b
    (0x7dffb0#64, 0x4e284af1#32),        -- aese    v17.16b, v23.16b
    (0x7dffb4#64, 0x6e241c42#32),        -- eor     v2.16b, v2.16b, v4.16b
    (0x7dffb8#64, 0x4cdf78f0#32),        -- ld1     {v16.4s}, [x7], #16
    (0x7dffbc#64, 0x4c9f7022#32),        -- st1     {v2.16b}, [x1], #16
    (0x7dffc0#64, 0x6e251c63#32),        -- eor     v3.16b, v3.16b, v5.16b
    (0x7dffc4#64, 0x2a0503e6#32),        -- mov     w6, w5
    (0x7dffc8#64, 0x4c9f7023#32),        -- st1     {v3.16b}, [x1], #16
    (0x7dffcc#64, 0x6e311e73#32),        -- eor     v19.16b, v19.16b, v17.16b
    (0x7dffd0#64, 0x4cdf78f1#32),        -- ld1     {v17.4s}, [x7], #16
    (0x7dffd4#64, 0x4c9f7033#32),        -- st1     {v19.16b}, [x1], #16
    (0x7dffd8#64, 0x54fff642#32),        -- b.cs    7dfea0 <.Loop3x_ctr32>  // b.hs, b.nlast
    (0x7dffdc#64, 0xb1000c42#32),        -- adds    x2, x2, #0x3
    (0x7dffe0#64, 0x54000600#32),        -- b.eq    7e00a0 <.Lctr32_done>  // b.none

    -- 00000000007dffe4 <.Lctr32_tail>:
    (0x7dffe4#64, 0xf100045f#32),        -- cmp     x2, #0x1
    (0x7dffe8#64, 0x540005cb#32),        -- b.lt    7e00a0 <.Lctr32_done>  // b.tstop
    (0x7dffec#64, 0xd280020c#32),        -- mov     x12, #0x10                      // #16
    (0x7dfff0#64, 0x9a8c03ec#32),        -- csel    x12, xzr, x12, eq  // eq = none
    (0x7dfff4#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7dfff8#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7dfffc#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7e0000#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7e0004#64, 0x4cdf78f0#32),        -- ld1     {v16.4s}, [x7], #16
    (0x7e0008#64, 0x710008c6#32),        -- subs    w6, w6, #0x2
    (0x7e000c#64, 0x4e284a20#32),        -- aese    v0.16b, v17.16b
    (0x7e0010#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7e0014#64, 0x4e284a21#32),        -- aese    v1.16b, v17.16b
    (0x7e0018#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7e001c#64, 0x4cdf78f1#32),        -- ld1     {v17.4s}, [x7], #16
    (0x7e0020#64, 0x54fffe2c#32),        -- b.gt    7dffe4 <.Lctr32_tail>
    (0x7e0024#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7e0028#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7e002c#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7e0030#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7e0034#64, 0x4e284a20#32),        -- aese    v0.16b, v17.16b
    (0x7e0038#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7e003c#64, 0x4e284a21#32),        -- aese    v1.16b, v17.16b
    (0x7e0040#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7e0044#64, 0x4ccc7002#32),        -- ld1     {v2.16b}, [x0], x12
    (0x7e0048#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7e004c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7e0050#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7e0054#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7e0058#64, 0x4c407003#32),        -- ld1     {v3.16b}, [x0]
    (0x7e005c#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7e0060#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7e0064#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7e0068#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7e006c#64, 0x6e271c42#32),        -- eor     v2.16b, v2.16b, v7.16b
    (0x7e0070#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7e0074#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7e0078#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7e007c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7e0080#64, 0x6e271c63#32),        -- eor     v3.16b, v3.16b, v7.16b
    (0x7e0084#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7e0088#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7e008c#64, 0x6e201c42#32),        -- eor     v2.16b, v2.16b, v0.16b
    (0x7e0090#64, 0x6e211c63#32),        -- eor     v3.16b, v3.16b, v1.16b
    (0x7e0094#64, 0x4c9f7022#32),        -- st1     {v2.16b}, [x1], #16
    (0x7e0098#64, 0xb400004c#32),        -- cbz     x12, 7e00a0 <.Lctr32_done>
    (0x7e009c#64, 0x4c007023#32),        -- st1     {v3.16b}, [x1]

    -- 00000000007e00a0 <.Lctr32_done>:
    (0x7e00a0#64, 0xf84107fd#32),        -- ldr     x29, [sp], #16
    (0x7e00a4#64, 0xd65f03c0#32),        -- ret
  ]

end AESHWCtr32EncryptBlocksProgram
