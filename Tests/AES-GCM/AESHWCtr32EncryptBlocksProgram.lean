/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
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
  [ -- 00000000007d2680 <aes_hw_ctr32_encrypt_blocks>:
    (0x7d2680#64, 0xa9bf7bfd#32),        -- stp     x29, x30, [sp, #-16]!
    (0x7d2684#64, 0x910003fd#32),        -- mov     x29, sp
    (0x7d2688#64, 0xb940f065#32),        -- ldr     w5, [x3, #240]
    (0x7d268c#64, 0xb9400c88#32),        -- ldr     w8, [x4, #12]
    (0x7d2690#64, 0x4c407880#32),        -- ld1     {v0.4s}, [x4]
    (0x7d2694#64, 0x4c40a870#32),        -- ld1     {v16.4s, v17.4s}, [x3]
    (0x7d2698#64, 0x510010a5#32),        -- sub     w5, w5, #0x4
    (0x7d269c#64, 0xd280020c#32),        -- mov     x12, #0x10                      // #16
    (0x7d26a0#64, 0xf100085f#32),        -- cmp     x2, #0x2
    (0x7d26a4#64, 0x8b051067#32),        -- add     x7, x3, x5, lsl #4
    (0x7d26a8#64, 0x510008a5#32),        -- sub     w5, w5, #0x2
    (0x7d26ac#64, 0x4cdfa8f4#32),        -- ld1     {v20.4s, v21.4s}, [x7], #32
    (0x7d26b0#64, 0x4cdfa8f6#32),        -- ld1     {v22.4s, v23.4s}, [x7], #32
    (0x7d26b4#64, 0x4c4078e7#32),        -- ld1     {v7.4s}, [x7]
    (0x7d26b8#64, 0x91008067#32),        -- add     x7, x3, #0x20
    (0x7d26bc#64, 0x2a0503e6#32),        -- mov     w6, w5
    (0x7d26c0#64, 0x5ac00908#32),        -- rev     w8, w8
    (0x7d26c4#64, 0x1100050a#32),        -- add     w10, w8, #0x1
    (0x7d26c8#64, 0x4ea01c06#32),        -- mov     v6.16b, v0.16b
    (0x7d26cc#64, 0x5ac0094a#32),        -- rev     w10, w10
    (0x7d26d0#64, 0x4e1c1d46#32),        -- mov     v6.s[3], w10
    (0x7d26d4#64, 0x11000908#32),        -- add     w8, w8, #0x2
    (0x7d26d8#64, 0x4ea61cc1#32),        -- mov     v1.16b, v6.16b
    (0x7d26dc#64, 0x54000b49#32),        -- b.ls    7d2844 <.Lctr32_tail>  // b.plast
    (0x7d26e0#64, 0x5ac0090c#32),        -- rev     w12, w8
    (0x7d26e4#64, 0x4e1c1d86#32),        -- mov     v6.s[3], w12
    (0x7d26e8#64, 0xd1000c42#32),        -- sub     x2, x2, #0x3
    (0x7d26ec#64, 0x4ea61cd2#32),        -- mov     v18.16b, v6.16b
    (0x7d26f0#64, 0x14000004#32),        -- b       7d2700 <.Loop3x_ctr32>
    (0x7d26f4#64, 0xd503201f#32),        -- nop
    (0x7d26f8#64, 0xd503201f#32),        -- nop
    (0x7d26fc#64, 0xd503201f#32),        -- nop

    -- 00000000007d2700 <.Loop3x_ctr32>:
    (0x7d2700#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7d2704#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d2708#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7d270c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d2710#64, 0x4e284a12#32),        -- aese    v18.16b, v16.16b
    (0x7d2714#64, 0x4e286a52#32),        -- aesmc   v18.16b, v18.16b
    (0x7d2718#64, 0x4cdf78f0#32),        -- ld1     {v16.4s}, [x7], #16
    (0x7d271c#64, 0x710008c6#32),        -- subs    w6, w6, #0x2
    (0x7d2720#64, 0x4e284a20#32),        -- aese    v0.16b, v17.16b
    (0x7d2724#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d2728#64, 0x4e284a21#32),        -- aese    v1.16b, v17.16b
    (0x7d272c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d2730#64, 0x4e284a32#32),        -- aese    v18.16b, v17.16b
    (0x7d2734#64, 0x4e286a52#32),        -- aesmc   v18.16b, v18.16b
    (0x7d2738#64, 0x4cdf78f1#32),        -- ld1     {v17.4s}, [x7], #16
    (0x7d273c#64, 0x54fffe2c#32),        -- b.gt    7d2700 <.Loop3x_ctr32>
    (0x7d2740#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7d2744#64, 0x4e286804#32),        -- aesmc   v4.16b, v0.16b
    (0x7d2748#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7d274c#64, 0x4e286825#32),        -- aesmc   v5.16b, v1.16b
    (0x7d2750#64, 0x4cdf7002#32),        -- ld1     {v2.16b}, [x0], #16
    (0x7d2754#64, 0x11000509#32),        -- add     w9, w8, #0x1
    (0x7d2758#64, 0x4e284a12#32),        -- aese    v18.16b, v16.16b
    (0x7d275c#64, 0x4e286a52#32),        -- aesmc   v18.16b, v18.16b
    (0x7d2760#64, 0x4cdf7003#32),        -- ld1     {v3.16b}, [x0], #16
    (0x7d2764#64, 0x5ac00929#32),        -- rev     w9, w9
    (0x7d2768#64, 0x4e284a24#32),        -- aese    v4.16b, v17.16b
    (0x7d276c#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7d2770#64, 0x4e284a25#32),        -- aese    v5.16b, v17.16b
    (0x7d2774#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7d2778#64, 0x4cdf7013#32),        -- ld1     {v19.16b}, [x0], #16
    (0x7d277c#64, 0xaa0303e7#32),        -- mov     x7, x3
    (0x7d2780#64, 0x4e284a32#32),        -- aese    v18.16b, v17.16b
    (0x7d2784#64, 0x4e286a51#32),        -- aesmc   v17.16b, v18.16b
    (0x7d2788#64, 0x4e284a84#32),        -- aese    v4.16b, v20.16b
    (0x7d278c#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7d2790#64, 0x4e284a85#32),        -- aese    v5.16b, v20.16b
    (0x7d2794#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7d2798#64, 0x6e271c42#32),        -- eor     v2.16b, v2.16b, v7.16b
    (0x7d279c#64, 0x1100090a#32),        -- add     w10, w8, #0x2
    (0x7d27a0#64, 0x4e284a91#32),        -- aese    v17.16b, v20.16b
    (0x7d27a4#64, 0x4e286a31#32),        -- aesmc   v17.16b, v17.16b
    (0x7d27a8#64, 0x6e271c63#32),        -- eor     v3.16b, v3.16b, v7.16b
    (0x7d27ac#64, 0x11000d08#32),        -- add     w8, w8, #0x3
    (0x7d27b0#64, 0x4e284aa4#32),        -- aese    v4.16b, v21.16b
    (0x7d27b4#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7d27b8#64, 0x4e284aa5#32),        -- aese    v5.16b, v21.16b
    (0x7d27bc#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7d27c0#64, 0x6e271e73#32),        -- eor     v19.16b, v19.16b, v7.16b
    (0x7d27c4#64, 0x4e1c1d26#32),        -- mov     v6.s[3], w9
    (0x7d27c8#64, 0x4e284ab1#32),        -- aese    v17.16b, v21.16b
    (0x7d27cc#64, 0x4e286a31#32),        -- aesmc   v17.16b, v17.16b
    (0x7d27d0#64, 0x4ea61cc0#32),        -- mov     v0.16b, v6.16b
    (0x7d27d4#64, 0x5ac0094a#32),        -- rev     w10, w10
    (0x7d27d8#64, 0x4e284ac4#32),        -- aese    v4.16b, v22.16b
    (0x7d27dc#64, 0x4e286884#32),        -- aesmc   v4.16b, v4.16b
    (0x7d27e0#64, 0x4e1c1d46#32),        -- mov     v6.s[3], w10
    (0x7d27e4#64, 0x5ac0090c#32),        -- rev     w12, w8
    (0x7d27e8#64, 0x4e284ac5#32),        -- aese    v5.16b, v22.16b
    (0x7d27ec#64, 0x4e2868a5#32),        -- aesmc   v5.16b, v5.16b
    (0x7d27f0#64, 0x4ea61cc1#32),        -- mov     v1.16b, v6.16b
    (0x7d27f4#64, 0x4e1c1d86#32),        -- mov     v6.s[3], w12
    (0x7d27f8#64, 0x4e284ad1#32),        -- aese    v17.16b, v22.16b
    (0x7d27fc#64, 0x4e286a31#32),        -- aesmc   v17.16b, v17.16b
    (0x7d2800#64, 0x4ea61cd2#32),        -- mov     v18.16b, v6.16b
    (0x7d2804#64, 0xf1000c42#32),        -- subs    x2, x2, #0x3
    (0x7d2808#64, 0x4e284ae4#32),        -- aese    v4.16b, v23.16b
    (0x7d280c#64, 0x4e284ae5#32),        -- aese    v5.16b, v23.16b
    (0x7d2810#64, 0x4e284af1#32),        -- aese    v17.16b, v23.16b
    (0x7d2814#64, 0x6e241c42#32),        -- eor     v2.16b, v2.16b, v4.16b
    (0x7d2818#64, 0x4cdf78f0#32),        -- ld1     {v16.4s}, [x7], #16
    (0x7d281c#64, 0x4c9f7022#32),        -- st1     {v2.16b}, [x1], #16
    (0x7d2820#64, 0x6e251c63#32),        -- eor     v3.16b, v3.16b, v5.16b
    (0x7d2824#64, 0x2a0503e6#32),        -- mov     w6, w5
    (0x7d2828#64, 0x4c9f7023#32),        -- st1     {v3.16b}, [x1], #16
    (0x7d282c#64, 0x6e311e73#32),        -- eor     v19.16b, v19.16b, v17.16b
    (0x7d2830#64, 0x4cdf78f1#32),        -- ld1     {v17.4s}, [x7], #16
    (0x7d2834#64, 0x4c9f7033#32),        -- st1     {v19.16b}, [x1], #16
    (0x7d2838#64, 0x54fff642#32),        -- b.cs    7d2700 <.Loop3x_ctr32>  // b.hs, b.nlast
    (0x7d283c#64, 0xb1000c42#32),        -- adds    x2, x2, #0x3
    (0x7d2840#64, 0x54000600#32),        -- b.eq    7d2900 <.Lctr32_done>  // b.none

    -- 00000000007d2844 <.Lctr32_tail>:
    (0x7d2844#64, 0xf100045f#32),        -- cmp     x2, #0x1
    (0x7d2848#64, 0xd280020c#32),        -- mov     x12, #0x10                      // #16
    (0x7d284c#64, 0x9a8c03ec#32),        -- csel    x12, xzr, x12, eq  // eq = none
    (0x7d2850#64, 0x5400058b#32),        -- b.lt    7d2900 <.Lctr32_done>  // b.tstop
    (0x7d2854#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7d2858#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d285c#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7d2860#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d2864#64, 0x4cdf78f0#32),        -- ld1     {v16.4s}, [x7], #16
    (0x7d2868#64, 0x710008c6#32),        -- subs    w6, w6, #0x2
    (0x7d286c#64, 0x4e284a20#32),        -- aese    v0.16b, v17.16b
    (0x7d2870#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d2874#64, 0x4e284a21#32),        -- aese    v1.16b, v17.16b
    (0x7d2878#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d287c#64, 0x4cdf78f1#32),        -- ld1     {v17.4s}, [x7], #16
    (0x7d2880#64, 0x54fffe2c#32),        -- b.gt    7d2844 <.Lctr32_tail>
    (0x7d2884#64, 0x4e284a00#32),        -- aese    v0.16b, v16.16b
    (0x7d2888#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d288c#64, 0x4e284a01#32),        -- aese    v1.16b, v16.16b
    (0x7d2890#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d2894#64, 0x4e284a20#32),        -- aese    v0.16b, v17.16b
    (0x7d2898#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d289c#64, 0x4e284a21#32),        -- aese    v1.16b, v17.16b
    (0x7d28a0#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d28a4#64, 0x4ccc7002#32),        -- ld1     {v2.16b}, [x0], x12
    (0x7d28a8#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7d28ac#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d28b0#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7d28b4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d28b8#64, 0x4c407003#32),        -- ld1     {v3.16b}, [x0]
    (0x7d28bc#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7d28c0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d28c4#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7d28c8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d28cc#64, 0x6e271c42#32),        -- eor     v2.16b, v2.16b, v7.16b
    (0x7d28d0#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7d28d4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d28d8#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7d28dc#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d28e0#64, 0x6e271c63#32),        -- eor     v3.16b, v3.16b, v7.16b
    (0x7d28e4#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7d28e8#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7d28ec#64, 0x6e201c42#32),        -- eor     v2.16b, v2.16b, v0.16b
    (0x7d28f0#64, 0x6e211c63#32),        -- eor     v3.16b, v3.16b, v1.16b
    (0x7d28f4#64, 0x4c9f7022#32),        -- st1     {v2.16b}, [x1], #16
    (0x7d28f8#64, 0xb400004c#32),        -- cbz     x12, 7d2900 <.Lctr32_done>
    (0x7d28fc#64, 0x4c007023#32),        -- st1     {v3.16b}, [x1]

    -- 00000000007d2900 <.Lctr32_done>:
    (0x7d2900#64, 0xf84107fd#32),        -- ldr     x29, [sp], #16
    (0x7d2904#64, 0xd65f03c0#32)         -- ret
  ]

end AESHWCtr32EncryptBlocksProgram
