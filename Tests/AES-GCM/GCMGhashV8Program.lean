/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.Exec

namespace GCMGhashV8Program

open BitVec

/-
  void gcm_ghash_v8(u64 Xi[2],const u128 Htable[16],const u8 *inp,size_t len);

  input:  Htable - table precomputed in gcm_init_v8; (x1)
          Xi - current hash value Xi; (x0)
          inp - pointer to input data; (x2)
          len - length of input data in bytes, but divisible by block size; (x3)
  output: Xi - next hash value Xi; (x0)
-/

def gcm_ghash_v8_program : Program :=
  def_program
  [ -- 00000000007d8870 <gcm_ghash_v8>:
    (0x7d8870#64, 0xf101007f#32),        -- cmp     x3, #0x40
    (0x7d8874#64, 0x54000b62#32),        -- b.cs    7d89e0 <gcm_ghash_v8_4x>  // b.hs, b.nlast
    (0x7d8878#64, 0x4c407c00#32),        -- ld1     {v0.2d}, [x0]
    (0x7d887c#64, 0xf1008063#32),        -- subs    x3, x3, #0x20
    (0x7d8880#64, 0xd280020c#32),        -- mov     x12, #0x10                      // #16
    (0x7d8884#64, 0x4cdfac34#32),        -- ld1     {v20.2d, v21.2d}, [x1], #32
    (0x7d8888#64, 0x6e144294#32),        -- ext     v20.16b, v20.16b, v20.16b, #8
    (0x7d888c#64, 0x4f07e433#32),        -- movi    v19.16b, #0xe1
    (0x7d8890#64, 0x4c407c36#32),        -- ld1     {v22.2d}, [x1]
    (0x7d8894#64, 0x6e1642d6#32),        -- ext     v22.16b, v22.16b, v22.16b, #8
    (0x7d8898#64, 0x9a8c03ec#32),        -- csel    x12, xzr, x12, eq  // eq = none
    (0x7d889c#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d88a0#64, 0x4cdf7c50#32),        -- ld1     {v16.2d}, [x2], #16
    (0x7d88a4#64, 0x4f795673#32),        -- shl     v19.2d, v19.2d, #57
    (0x7d88a8#64, 0x4e200a10#32),        -- rev64   v16.16b, v16.16b
    (0x7d88ac#64, 0x4e200800#32),        -- rev64   v0.16b, v0.16b
    (0x7d88b0#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d88b4#64, 0x54000663#32),        -- b.cc    7d8980 <.Lodd_tail_v8>  // b.lo, b.ul, b.last
    (0x7d88b8#64, 0x4ccc7c51#32),        -- ld1     {v17.2d}, [x2], x12
    (0x7d88bc#64, 0x4e200a31#32),        -- rev64   v17.16b, v17.16b
    (0x7d88c0#64, 0x6e114227#32),        -- ext     v7.16b, v17.16b, v17.16b, #8
    (0x7d88c4#64, 0x6e201c63#32),        -- eor     v3.16b, v3.16b, v0.16b
    (0x7d88c8#64, 0x0ee7e284#32),        -- pmull   v4.1q, v20.1d, v7.1d
    (0x7d88cc#64, 0x6e271e31#32),        -- eor     v17.16b, v17.16b, v7.16b
    (0x7d88d0#64, 0x4ee7e286#32),        -- pmull2  v6.1q, v20.2d, v7.2d
    (0x7d88d4#64, 0x14000003#32),        -- b       7d88e0 <.Loop_mod2x_v8>
    (0x7d88d8#64, 0xd503201f#32),        -- nop
    (0x7d88dc#64, 0xd503201f#32),        -- nop

    -- 00000000007d88e0 <.Loop_mod2x_v8>:
    (0x7d88e0#64, 0x6e034072#32),        -- ext     v18.16b, v3.16b, v3.16b, #8
    (0x7d88e4#64, 0xf1008063#32),        -- subs    x3, x3, #0x20
    (0x7d88e8#64, 0x0ee3e2c0#32),        -- pmull   v0.1q, v22.1d, v3.1d
    (0x7d88ec#64, 0x9a8c33ec#32),        -- csel    x12, xzr, x12, cc  // cc = lo, ul, last
    (0x7d88f0#64, 0x0ef1e2a5#32),        -- pmull   v5.1q, v21.1d, v17.1d
    (0x7d88f4#64, 0x6e231e52#32),        -- eor     v18.16b, v18.16b, v3.16b
    (0x7d88f8#64, 0x4ee3e2c2#32),        -- pmull2  v2.1q, v22.2d, v3.2d
    (0x7d88fc#64, 0x6e241c00#32),        -- eor     v0.16b, v0.16b, v4.16b
    (0x7d8900#64, 0x4ef2e2a1#32),        -- pmull2  v1.1q, v21.2d, v18.2d
    (0x7d8904#64, 0x4ccc7c50#32),        -- ld1     {v16.2d}, [x2], x12
    (0x7d8908#64, 0x6e261c42#32),        -- eor     v2.16b, v2.16b, v6.16b
    (0x7d890c#64, 0x9a8c03ec#32),        -- csel    x12, xzr, x12, eq  // eq = none
    (0x7d8910#64, 0x6e251c21#32),        -- eor     v1.16b, v1.16b, v5.16b
    (0x7d8914#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d8918#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d891c#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8920#64, 0x4ccc7c51#32),        -- ld1     {v17.2d}, [x2], x12
    (0x7d8924#64, 0x4e200a10#32),        -- rev64   v16.16b, v16.16b
    (0x7d8928#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d892c#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8930#64, 0x4e200a31#32),        -- rev64   v17.16b, v17.16b
    (0x7d8934#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8938#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d893c#64, 0x6e114227#32),        -- ext     v7.16b, v17.16b, v17.16b, #8
    (0x7d8940#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d8944#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8948#64, 0x0ee7e284#32),        -- pmull   v4.1q, v20.1d, v7.1d
    (0x7d894c#64, 0x6e221c63#32),        -- eor     v3.16b, v3.16b, v2.16b
    (0x7d8950#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8954#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8958#64, 0x6e321c63#32),        -- eor     v3.16b, v3.16b, v18.16b
    (0x7d895c#64, 0x6e271e31#32),        -- eor     v17.16b, v17.16b, v7.16b
    (0x7d8960#64, 0x6e201c63#32),        -- eor     v3.16b, v3.16b, v0.16b
    (0x7d8964#64, 0x4ee7e286#32),        -- pmull2  v6.1q, v20.2d, v7.2d
    (0x7d8968#64, 0x54fffbc2#32),        -- b.cs    7d88e0 <.Loop_mod2x_v8>  // b.hs, b.nlast
    (0x7d896c#64, 0x6e321c42#32),        -- eor     v2.16b, v2.16b, v18.16b
    (0x7d8970#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d8974#64, 0xb1008063#32),        -- adds    x3, x3, #0x20
    (0x7d8978#64, 0x6e221c00#32),        -- eor     v0.16b, v0.16b, v2.16b
    (0x7d897c#64, 0x54000280#32),        -- b.eq    7d89cc <.Ldone_v8>  // b.none

    -- 00000000007d8980 <.Lodd_tail_v8>:
    (0x7d8980#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8984#64, 0x6e201c63#32),        -- eor     v3.16b, v3.16b, v0.16b
    (0x7d8988#64, 0x6e321e11#32),        -- eor     v17.16b, v16.16b, v18.16b
    (0x7d898c#64, 0x0ee3e280#32),        -- pmull   v0.1q, v20.1d, v3.1d
    (0x7d8990#64, 0x6e231e31#32),        -- eor     v17.16b, v17.16b, v3.16b
    (0x7d8994#64, 0x4ee3e282#32),        -- pmull2  v2.1q, v20.2d, v3.2d
    (0x7d8998#64, 0x0ef1e2a1#32),        -- pmull   v1.1q, v21.1d, v17.1d
    (0x7d899c#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d89a0#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d89a4#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d89a8#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d89ac#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d89b0#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d89b4#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d89b8#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d89bc#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d89c0#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d89c4#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d89c8#64, 0x6e321c00#32),        -- eor     v0.16b, v0.16b, v18.16b

    -- 00000000007d89cc <.Ldone_v8>:
    (0x7d89cc#64, 0x4e200800#32),        -- rev64   v0.16b, v0.16b
    (0x7d89d0#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d89d4#64, 0x4c007c00#32),        -- st1     {v0.2d}, [x0]
    (0x7d89d8#64, 0xd65f03c0#32),        -- ret
    (0x7d89dc#64, 0xd503201f#32),        -- nop

    -- 00000000007d89e0 <gcm_ghash_v8_4x>:
    (0x7d89e0#64, 0x4c407c00#32),        -- ld1     {v0.2d}, [x0]
    (0x7d89e4#64, 0x4cdf6c34#32),        -- ld1     {v20.2d-v22.2d}, [x1], #48
    (0x7d89e8#64, 0x6e144294#32),        -- ext     v20.16b, v20.16b, v20.16b, #8
    (0x7d89ec#64, 0x6e1642d6#32),        -- ext     v22.16b, v22.16b, v22.16b, #8
    (0x7d89f0#64, 0x4f07e433#32),        -- movi    v19.16b, #0xe1
    (0x7d89f4#64, 0x4c406c3a#32),        -- ld1     {v26.2d-v28.2d}, [x1]
    (0x7d89f8#64, 0x6e1a435a#32),        -- ext     v26.16b, v26.16b, v26.16b, #8
    (0x7d89fc#64, 0x6e1c439c#32),        -- ext     v28.16b, v28.16b, v28.16b, #8
    (0x7d8a00#64, 0x4f795673#32),        -- shl     v19.2d, v19.2d, #57
    (0x7d8a04#64, 0x4cdf2c44#32),        -- ld1     {v4.2d-v7.2d}, [x2], #64
    (0x7d8a08#64, 0x4e200800#32),        -- rev64   v0.16b, v0.16b
    (0x7d8a0c#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7d8a10#64, 0x4e2008c6#32),        -- rev64   v6.16b, v6.16b
    (0x7d8a14#64, 0x4e2008e7#32),        -- rev64   v7.16b, v7.16b
    (0x7d8a18#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7d8a1c#64, 0x6e0740f9#32),        -- ext     v25.16b, v7.16b, v7.16b, #8
    (0x7d8a20#64, 0x6e0640d8#32),        -- ext     v24.16b, v6.16b, v6.16b, #8
    (0x7d8a24#64, 0x6e0540b7#32),        -- ext     v23.16b, v5.16b, v5.16b, #8
    (0x7d8a28#64, 0x0ef9e29d#32),        -- pmull   v29.1q, v20.1d, v25.1d
    (0x7d8a2c#64, 0x6e391ce7#32),        -- eor     v7.16b, v7.16b, v25.16b
    (0x7d8a30#64, 0x4ef9e29f#32),        -- pmull2  v31.1q, v20.2d, v25.2d
    (0x7d8a34#64, 0x0ee7e2be#32),        -- pmull   v30.1q, v21.1d, v7.1d
    (0x7d8a38#64, 0x0ef8e2d0#32),        -- pmull   v16.1q, v22.1d, v24.1d
    (0x7d8a3c#64, 0x6e381cc6#32),        -- eor     v6.16b, v6.16b, v24.16b
    (0x7d8a40#64, 0x4ef8e2d8#32),        -- pmull2  v24.1q, v22.2d, v24.2d
    (0x7d8a44#64, 0x4ee6e2a6#32),        -- pmull2  v6.1q, v21.2d, v6.2d
    (0x7d8a48#64, 0x6e301fbd#32),        -- eor     v29.16b, v29.16b, v16.16b
    (0x7d8a4c#64, 0x6e381fff#32),        -- eor     v31.16b, v31.16b, v24.16b
    (0x7d8a50#64, 0x6e261fde#32),        -- eor     v30.16b, v30.16b, v6.16b
    (0x7d8a54#64, 0x0ef7e347#32),        -- pmull   v7.1q, v26.1d, v23.1d
    (0x7d8a58#64, 0x6e371ca5#32),        -- eor     v5.16b, v5.16b, v23.16b
    (0x7d8a5c#64, 0x4ef7e357#32),        -- pmull2  v23.1q, v26.2d, v23.2d
    (0x7d8a60#64, 0x0ee5e365#32),        -- pmull   v5.1q, v27.1d, v5.1d
    (0x7d8a64#64, 0x6e271fbd#32),        -- eor     v29.16b, v29.16b, v7.16b
    (0x7d8a68#64, 0x6e371fff#32),        -- eor     v31.16b, v31.16b, v23.16b
    (0x7d8a6c#64, 0x6e251fde#32),        -- eor     v30.16b, v30.16b, v5.16b
    (0x7d8a70#64, 0xf1020063#32),        -- subs    x3, x3, #0x80
    (0x7d8a74#64, 0x540006a3#32),        -- b.cc    7d8b48 <.Ltail4x>  // b.lo, b.ul, b.last
    (0x7d8a78#64, 0x14000002#32),        -- b       7d8a80 <.Loop4x>
    (0x7d8a7c#64, 0xd503201f#32),        -- nop

    -- 00000000007d8a80 <.Loop4x>:
    (0x7d8a80#64, 0x6e201c90#32),        -- eor     v16.16b, v4.16b, v0.16b
    (0x7d8a84#64, 0x4cdf2c44#32),        -- ld1     {v4.2d-v7.2d}, [x2], #64
    (0x7d8a88#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d8a8c#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7d8a90#64, 0x4e2008c6#32),        -- rev64   v6.16b, v6.16b
    (0x7d8a94#64, 0x4e2008e7#32),        -- rev64   v7.16b, v7.16b
    (0x7d8a98#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7d8a9c#64, 0x0ee3e380#32),        -- pmull   v0.1q, v28.1d, v3.1d
    (0x7d8aa0#64, 0x6e231e10#32),        -- eor     v16.16b, v16.16b, v3.16b
    (0x7d8aa4#64, 0x4ee3e382#32),        -- pmull2  v2.1q, v28.2d, v3.2d
    (0x7d8aa8#64, 0x6e0740f9#32),        -- ext     v25.16b, v7.16b, v7.16b, #8
    (0x7d8aac#64, 0x4ef0e361#32),        -- pmull2  v1.1q, v27.2d, v16.2d
    (0x7d8ab0#64, 0x6e3d1c00#32),        -- eor     v0.16b, v0.16b, v29.16b
    (0x7d8ab4#64, 0x6e3f1c42#32),        -- eor     v2.16b, v2.16b, v31.16b
    (0x7d8ab8#64, 0x6e0640d8#32),        -- ext     v24.16b, v6.16b, v6.16b, #8
    (0x7d8abc#64, 0x6e3e1c21#32),        -- eor     v1.16b, v1.16b, v30.16b
    (0x7d8ac0#64, 0x6e0540b7#32),        -- ext     v23.16b, v5.16b, v5.16b, #8
    (0x7d8ac4#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d8ac8#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8acc#64, 0x0ef9e29d#32),        -- pmull   v29.1q, v20.1d, v25.1d
    (0x7d8ad0#64, 0x6e391ce7#32),        -- eor     v7.16b, v7.16b, v25.16b
    (0x7d8ad4#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8ad8#64, 0x4ef9e29f#32),        -- pmull2  v31.1q, v20.2d, v25.2d
    (0x7d8adc#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8ae0#64, 0x0ee7e2be#32),        -- pmull   v30.1q, v21.1d, v7.1d
    (0x7d8ae4#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8ae8#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8aec#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8af0#64, 0x0ef8e2d0#32),        -- pmull   v16.1q, v22.1d, v24.1d
    (0x7d8af4#64, 0x6e381cc6#32),        -- eor     v6.16b, v6.16b, v24.16b
    (0x7d8af8#64, 0x4ef8e2d8#32),        -- pmull2  v24.1q, v22.2d, v24.2d
    (0x7d8afc#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8b00#64, 0x4ee6e2a6#32),        -- pmull2  v6.1q, v21.2d, v6.2d
    (0x7d8b04#64, 0x6e301fbd#32),        -- eor     v29.16b, v29.16b, v16.16b
    (0x7d8b08#64, 0x6e381fff#32),        -- eor     v31.16b, v31.16b, v24.16b
    (0x7d8b0c#64, 0x6e261fde#32),        -- eor     v30.16b, v30.16b, v6.16b
    (0x7d8b10#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8b14#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8b18#64, 0x0ef7e347#32),        -- pmull   v7.1q, v26.1d, v23.1d
    (0x7d8b1c#64, 0x6e371ca5#32),        -- eor     v5.16b, v5.16b, v23.16b
    (0x7d8b20#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8b24#64, 0x4ef7e357#32),        -- pmull2  v23.1q, v26.2d, v23.2d
    (0x7d8b28#64, 0x0ee5e365#32),        -- pmull   v5.1q, v27.1d, v5.1d
    (0x7d8b2c#64, 0x6e321c00#32),        -- eor     v0.16b, v0.16b, v18.16b
    (0x7d8b30#64, 0x6e271fbd#32),        -- eor     v29.16b, v29.16b, v7.16b
    (0x7d8b34#64, 0x6e371fff#32),        -- eor     v31.16b, v31.16b, v23.16b
    (0x7d8b38#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d8b3c#64, 0x6e251fde#32),        -- eor     v30.16b, v30.16b, v5.16b
    (0x7d8b40#64, 0xf1010063#32),        -- subs    x3, x3, #0x40
    (0x7d8b44#64, 0x54fff9e2#32),        -- b.cs    7d8a80 <.Loop4x>  // b.hs, b.nlast

    -- 00000000007d8b48 <.Ltail4x>:
    (0x7d8b48#64, 0x6e201c90#32),        -- eor     v16.16b, v4.16b, v0.16b
    (0x7d8b4c#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d8b50#64, 0x0ee3e380#32),        -- pmull   v0.1q, v28.1d, v3.1d
    (0x7d8b54#64, 0x6e231e10#32),        -- eor     v16.16b, v16.16b, v3.16b
    (0x7d8b58#64, 0x4ee3e382#32),        -- pmull2  v2.1q, v28.2d, v3.2d
    (0x7d8b5c#64, 0x4ef0e361#32),        -- pmull2  v1.1q, v27.2d, v16.2d
    (0x7d8b60#64, 0x6e3d1c00#32),        -- eor     v0.16b, v0.16b, v29.16b
    (0x7d8b64#64, 0x6e3f1c42#32),        -- eor     v2.16b, v2.16b, v31.16b
    (0x7d8b68#64, 0x6e3e1c21#32),        -- eor     v1.16b, v1.16b, v30.16b
    (0x7d8b6c#64, 0xb1010063#32),        -- adds    x3, x3, #0x40
    (0x7d8b70#64, 0x54000c20#32),        -- b.eq    7d8cf4 <.Ldone4x>  // b.none
    (0x7d8b74#64, 0xf100807f#32),        -- cmp     x3, #0x20
    (0x7d8b78#64, 0x54000943#32),        -- b.cc    7d8ca0 <.Lone>  // b.lo, b.ul, b.last
    (0x7d8b7c#64, 0x54000520#32),        -- b.eq    7d8c20 <.Ltwo>  // b.none

    -- 00000000007d8b80 <.Lthree>:
    (0x7d8b80#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d8b84#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8b88#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8b8c#64, 0x4c406c44#32),        -- ld1     {v4.2d-v6.2d}, [x2]
    (0x7d8b90#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8b94#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7d8b98#64, 0x4e2008c6#32),        -- rev64   v6.16b, v6.16b
    (0x7d8b9c#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7d8ba0#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8ba4#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8ba8#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8bac#64, 0x6e0640d8#32),        -- ext     v24.16b, v6.16b, v6.16b, #8
    (0x7d8bb0#64, 0x6e0540b7#32),        -- ext     v23.16b, v5.16b, v5.16b, #8
    (0x7d8bb4#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8bb8#64, 0x0ef8e29d#32),        -- pmull   v29.1q, v20.1d, v24.1d
    (0x7d8bbc#64, 0x6e381cc6#32),        -- eor     v6.16b, v6.16b, v24.16b
    (0x7d8bc0#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8bc4#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8bc8#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8bcc#64, 0x4ef8e29f#32),        -- pmull2  v31.1q, v20.2d, v24.2d
    (0x7d8bd0#64, 0x0ee6e2be#32),        -- pmull   v30.1q, v21.1d, v6.1d
    (0x7d8bd4#64, 0x6e321c00#32),        -- eor     v0.16b, v0.16b, v18.16b
    (0x7d8bd8#64, 0x0ef7e2c7#32),        -- pmull   v7.1q, v22.1d, v23.1d
    (0x7d8bdc#64, 0x6e371ca5#32),        -- eor     v5.16b, v5.16b, v23.16b
    (0x7d8be0#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d8be4#64, 0x4ef7e2d7#32),        -- pmull2  v23.1q, v22.2d, v23.2d
    (0x7d8be8#64, 0x6e201c90#32),        -- eor     v16.16b, v4.16b, v0.16b
    (0x7d8bec#64, 0x4ee5e2a5#32),        -- pmull2  v5.1q, v21.2d, v5.2d
    (0x7d8bf0#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d8bf4#64, 0x6e271fbd#32),        -- eor     v29.16b, v29.16b, v7.16b
    (0x7d8bf8#64, 0x6e371fff#32),        -- eor     v31.16b, v31.16b, v23.16b
    (0x7d8bfc#64, 0x6e251fde#32),        -- eor     v30.16b, v30.16b, v5.16b
    (0x7d8c00#64, 0x0ee3e340#32),        -- pmull   v0.1q, v26.1d, v3.1d
    (0x7d8c04#64, 0x6e231e10#32),        -- eor     v16.16b, v16.16b, v3.16b
    (0x7d8c08#64, 0x4ee3e342#32),        -- pmull2  v2.1q, v26.2d, v3.2d
    (0x7d8c0c#64, 0x0ef0e361#32),        -- pmull   v1.1q, v27.1d, v16.1d
    (0x7d8c10#64, 0x6e3d1c00#32),        -- eor     v0.16b, v0.16b, v29.16b
    (0x7d8c14#64, 0x6e3f1c42#32),        -- eor     v2.16b, v2.16b, v31.16b
    (0x7d8c18#64, 0x6e3e1c21#32),        -- eor     v1.16b, v1.16b, v30.16b
    (0x7d8c1c#64, 0x14000036#32),        -- b       7d8cf4 <.Ldone4x>

    -- 00000000007d8c20 <.Ltwo>:
    (0x7d8c20#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d8c24#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8c28#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8c2c#64, 0x4c40ac44#32),        -- ld1     {v4.2d, v5.2d}, [x2]
    (0x7d8c30#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8c34#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7d8c38#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7d8c3c#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8c40#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8c44#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8c48#64, 0x6e0540b7#32),        -- ext     v23.16b, v5.16b, v5.16b, #8
    (0x7d8c4c#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8c50#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8c54#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8c58#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8c5c#64, 0x6e321c00#32),        -- eor     v0.16b, v0.16b, v18.16b
    (0x7d8c60#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d8c64#64, 0x0ef7e29d#32),        -- pmull   v29.1q, v20.1d, v23.1d
    (0x7d8c68#64, 0x6e371ca5#32),        -- eor     v5.16b, v5.16b, v23.16b
    (0x7d8c6c#64, 0x6e201c90#32),        -- eor     v16.16b, v4.16b, v0.16b
    (0x7d8c70#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d8c74#64, 0x4ef7e29f#32),        -- pmull2  v31.1q, v20.2d, v23.2d
    (0x7d8c78#64, 0x0ee5e2be#32),        -- pmull   v30.1q, v21.1d, v5.1d
    (0x7d8c7c#64, 0x0ee3e2c0#32),        -- pmull   v0.1q, v22.1d, v3.1d
    (0x7d8c80#64, 0x6e231e10#32),        -- eor     v16.16b, v16.16b, v3.16b
    (0x7d8c84#64, 0x4ee3e2c2#32),        -- pmull2  v2.1q, v22.2d, v3.2d
    (0x7d8c88#64, 0x4ef0e2a1#32),        -- pmull2  v1.1q, v21.2d, v16.2d
    (0x7d8c8c#64, 0x6e3d1c00#32),        -- eor     v0.16b, v0.16b, v29.16b
    (0x7d8c90#64, 0x6e3f1c42#32),        -- eor     v2.16b, v2.16b, v31.16b
    (0x7d8c94#64, 0x6e3e1c21#32),        -- eor     v1.16b, v1.16b, v30.16b
    (0x7d8c98#64, 0x14000017#32),        -- b       7d8cf4 <.Ldone4x>
    (0x7d8c9c#64, 0xd503201f#32),        -- nop

    -- 00000000007d8ca0 <.Lone>:
    (0x7d8ca0#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d8ca4#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8ca8#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8cac#64, 0x4c407c44#32),        -- ld1     {v4.2d}, [x2]
    (0x7d8cb0#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8cb4#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7d8cb8#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8cbc#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8cc0#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8cc4#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8cc8#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8ccc#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8cd0#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8cd4#64, 0x6e321c00#32),        -- eor     v0.16b, v0.16b, v18.16b
    (0x7d8cd8#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d8cdc#64, 0x6e201c90#32),        -- eor     v16.16b, v4.16b, v0.16b
    (0x7d8ce0#64, 0x6e104203#32),        -- ext     v3.16b, v16.16b, v16.16b, #8
    (0x7d8ce4#64, 0x0ee3e280#32),        -- pmull   v0.1q, v20.1d, v3.1d
    (0x7d8ce8#64, 0x6e231e10#32),        -- eor     v16.16b, v16.16b, v3.16b
    (0x7d8cec#64, 0x4ee3e282#32),        -- pmull2  v2.1q, v20.2d, v3.2d
    (0x7d8cf0#64, 0x0ef0e2a1#32),        -- pmull   v1.1q, v21.1d, v16.1d

    -- 00000000007d8cf4 <.Ldone4x>:
    (0x7d8cf4#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d8cf8#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8cfc#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8d00#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8d04#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8d08#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8d0c#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8d10#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8d14#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8d18#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8d1c#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8d20#64, 0x6e321c00#32),        -- eor     v0.16b, v0.16b, v18.16b
    (0x7d8d24#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d8d28#64, 0x4e200800#32),        -- rev64   v0.16b, v0.16b
    (0x7d8d2c#64, 0x4c007c00#32),        -- st1     {v0.2d}, [x0]
    (0x7d8d30#64, 0xd65f03c0#32)         -- ret
  ]

end GCMGhashV8Program
