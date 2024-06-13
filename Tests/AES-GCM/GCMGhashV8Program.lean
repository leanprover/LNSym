/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
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

def gcm_ghash_v8_program : program :=
  def_program
  [ -- 00000000007aa490 <gcm_ghash_v8>:
    (0x7aa490#64,  0xf101007f#32),   -- cmp  x3, #0x40
    (0x7aa494#64,  0x54000ae2#32),   -- b.cs  7aa5f0 <gcm_ghash_v8_4x>  // b.hs, b.nlast
    (0x7aa498#64,  0x4c407c00#32),   -- ld1  {v0.2d}, [x0]
    (0x7aa49c#64,  0xf1008063#32),   -- subs  x3, x3, #0x20
    (0x7aa4a0#64,  0xd280020c#32),   -- mov  x12, #0x10                    // #16
    (0x7aa4a4#64,  0x4cdfac34#32),   -- ld1  {v20.2d, v21.2d}, [x1], #32
    (0x7aa4a8#64,  0x4f07e433#32),   -- movi  v19.16b, #0xe1
    (0x7aa4ac#64,  0x4c407c36#32),   -- ld1  {v22.2d}, [x1]
    (0x7aa4b0#64,  0x9a8c03ec#32),   -- csel  x12, xzr, x12, eq  // eq = none
    (0x7aa4b4#64,  0x6e004000#32),   -- ext  v0.16b, v0.16b, v0.16b, #8
    (0x7aa4b8#64,  0x4cdf7c50#32),   -- ld1  {v16.2d}, [x2], #16
    (0x7aa4bc#64,  0x4f795673#32),   -- shl  v19.2d, v19.2d, #57
    (0x7aa4c0#64,  0x4e200a10#32),   -- rev64  v16.16b, v16.16b
    (0x7aa4c4#64,  0x4e200800#32),   -- rev64  v0.16b, v0.16b
    (0x7aa4c8#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa4cc#64,  0x54000623#32),   -- b.cc  7aa590 <.Lodd_tail_v8>  // b.lo, b.ul, b.last
    (0x7aa4d0#64,  0x4ccc7c51#32),   -- ld1  {v17.2d}, [x2], x12
    (0x7aa4d4#64,  0x4e200a31#32),   -- rev64  v17.16b, v17.16b
    (0x7aa4d8#64,  0x6e114227#32),   -- ext  v7.16b, v17.16b, v17.16b, #8
    (0x7aa4dc#64,  0x6e201c63#32),   -- eor  v3.16b, v3.16b, v0.16b
    (0x7aa4e0#64,  0x0ee7e284#32),   -- pmull  v4.1q, v20.1d, v7.1d
    (0x7aa4e4#64,  0x6e271e31#32),   -- eor  v17.16b, v17.16b, v7.16b
    (0x7aa4e8#64,  0x4ee7e286#32),   -- pmull2  v6.1q, v20.2d, v7.2d
    (0x7aa4ec#64,  0x14000001#32),   -- b  7aa4f0 <.Loop_mod2x_v8>

    -- 00000000007aa4f0 <.Loop_mod2x_v8>:
    (0x7aa4f0#64,  0x6e034072#32),   -- ext  v18.16b, v3.16b, v3.16b, #8
    (0x7aa4f4#64,  0xf1008063#32),   -- subs  x3, x3, #0x20
    (0x7aa4f8#64,  0x0ee3e2c0#32),   -- pmull  v0.1q, v22.1d, v3.1d
    (0x7aa4fc#64,  0x9a8c33ec#32),   -- csel  x12, xzr, x12, cc  // cc = lo, ul, last
    (0x7aa500#64,  0x0ef1e2a5#32),   -- pmull  v5.1q, v21.1d, v17.1d
    (0x7aa504#64,  0x6e231e52#32),   -- eor  v18.16b, v18.16b, v3.16b
    (0x7aa508#64,  0x4ee3e2c2#32),   -- pmull2  v2.1q, v22.2d, v3.2d
    (0x7aa50c#64,  0x6e241c00#32),   -- eor  v0.16b, v0.16b, v4.16b
    (0x7aa510#64,  0x4ef2e2a1#32),   -- pmull2  v1.1q, v21.2d, v18.2d
    (0x7aa514#64,  0x4ccc7c50#32),   -- ld1  {v16.2d}, [x2], x12
    (0x7aa518#64,  0x6e261c42#32),   -- eor  v2.16b, v2.16b, v6.16b
    (0x7aa51c#64,  0x9a8c03ec#32),   -- csel  x12, xzr, x12, eq  // eq = none
    (0x7aa520#64,  0x6e251c21#32),   -- eor  v1.16b, v1.16b, v5.16b
    (0x7aa524#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa528#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa52c#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa530#64,  0x4ccc7c51#32),   -- ld1  {v17.2d}, [x2], x12
    (0x7aa534#64,  0x4e200a10#32),   -- rev64  v16.16b, v16.16b
    (0x7aa538#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa53c#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa540#64,  0x4e200a31#32),   -- rev64  v17.16b, v17.16b
    (0x7aa544#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa548#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa54c#64,  0x6e114227#32),   -- ext  v7.16b, v17.16b, v17.16b, #8
    (0x7aa550#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa554#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa558#64,  0x0ee7e284#32),   -- pmull  v4.1q, v20.1d, v7.1d
    (0x7aa55c#64,  0x6e221c63#32),   -- eor  v3.16b, v3.16b, v2.16b
    (0x7aa560#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa564#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa568#64,  0x6e321c63#32),   -- eor  v3.16b, v3.16b, v18.16b
    (0x7aa56c#64,  0x6e271e31#32),   -- eor  v17.16b, v17.16b, v7.16b
    (0x7aa570#64,  0x6e201c63#32),   -- eor  v3.16b, v3.16b, v0.16b
    (0x7aa574#64,  0x4ee7e286#32),   -- pmull2  v6.1q, v20.2d, v7.2d
    (0x7aa578#64,  0x54fffbc2#32),   -- b.cs  7aa4f0 <.Loop_mod2x_v8>  // b.hs, b.nlast
    (0x7aa57c#64,  0x6e321c42#32),   -- eor  v2.16b, v2.16b, v18.16b
    (0x7aa580#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa584#64,  0xb1008063#32),   -- adds  x3, x3, #0x20
    (0x7aa588#64,  0x6e221c00#32),   -- eor  v0.16b, v0.16b, v2.16b
    (0x7aa58c#64,  0x54000280#32),   -- b.eq  7aa5dc <.Ldone_v8>  // b.none

    -- 00000000007aa590 <.Lodd_tail_v8>:
    (0x7aa590#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa594#64,  0x6e201c63#32),   -- eor  v3.16b, v3.16b, v0.16b
    (0x7aa598#64,  0x6e321e11#32),   -- eor  v17.16b, v16.16b, v18.16b
    (0x7aa59c#64,  0x0ee3e280#32),   -- pmull  v0.1q, v20.1d, v3.1d
    (0x7aa5a0#64,  0x6e231e31#32),   -- eor  v17.16b, v17.16b, v3.16b
    (0x7aa5a4#64,  0x4ee3e282#32),   -- pmull2  v2.1q, v20.2d, v3.2d
    (0x7aa5a8#64,  0x0ef1e2a1#32),   -- pmull  v1.1q, v21.1d, v17.1d
    (0x7aa5ac#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa5b0#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa5b4#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa5b8#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa5bc#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa5c0#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa5c4#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa5c8#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa5cc#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa5d0#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa5d4#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa5d8#64,  0x6e321c00#32),   -- eor  v0.16b, v0.16b, v18.16b

    -- 00000000007aa5dc <.Ldone_v8>:
    (0x7aa5dc#64,  0x4e200800#32),   -- rev64  v0.16b, v0.16b
    (0x7aa5e0#64,  0x6e004000#32),   -- ext  v0.16b, v0.16b, v0.16b, #8
    (0x7aa5e4#64,  0x4c007c00#32),   -- st1  {v0.2d}, [x0]
    (0x7aa5e8#64,  0xd65f03c0#32),   -- ret
    (0x7aa5ec#64,  0xd503201f#32),   -- nop

    -- 00000000007aa5f0 <gcm_ghash_v8_4x>:
    (0x7aa5f0#64,  0x4c407c00#32),   -- ld1  {v0.2d}, [x0]
    (0x7aa5f4#64,  0x4cdf6c34#32),   -- ld1  {v20.2d-v22.2d}, [x1], #48
    (0x7aa5f8#64,  0x4f07e433#32),   -- movi  v19.16b, #0xe1
    (0x7aa5fc#64,  0x4c406c3a#32),   -- ld1  {v26.2d-v28.2d}, [x1]
    (0x7aa600#64,  0x4f795673#32),   -- shl  v19.2d, v19.2d, #57
    (0x7aa604#64,  0x4cdf2c44#32),   -- ld1  {v4.2d-v7.2d}, [x2], #64
    (0x7aa608#64,  0x4e200800#32),   -- rev64  v0.16b, v0.16b
    (0x7aa60c#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7aa610#64,  0x4e2008c6#32),   -- rev64  v6.16b, v6.16b
    (0x7aa614#64,  0x4e2008e7#32),   -- rev64  v7.16b, v7.16b
    (0x7aa618#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7aa61c#64,  0x6e0740f9#32),   -- ext  v25.16b, v7.16b, v7.16b, #8
    (0x7aa620#64,  0x6e0640d8#32),   -- ext  v24.16b, v6.16b, v6.16b, #8
    (0x7aa624#64,  0x6e0540b7#32),   -- ext  v23.16b, v5.16b, v5.16b, #8
    (0x7aa628#64,  0x0ef9e29d#32),   -- pmull  v29.1q, v20.1d, v25.1d
    (0x7aa62c#64,  0x6e391ce7#32),   -- eor  v7.16b, v7.16b, v25.16b
    (0x7aa630#64,  0x4ef9e29f#32),   -- pmull2  v31.1q, v20.2d, v25.2d
    (0x7aa634#64,  0x0ee7e2be#32),   -- pmull  v30.1q, v21.1d, v7.1d
    (0x7aa638#64,  0x0ef8e2d0#32),   -- pmull  v16.1q, v22.1d, v24.1d
    (0x7aa63c#64,  0x6e381cc6#32),   -- eor  v6.16b, v6.16b, v24.16b
    (0x7aa640#64,  0x4ef8e2d8#32),   -- pmull2  v24.1q, v22.2d, v24.2d
    (0x7aa644#64,  0x4ee6e2a6#32),   -- pmull2  v6.1q, v21.2d, v6.2d
    (0x7aa648#64,  0x6e301fbd#32),   -- eor  v29.16b, v29.16b, v16.16b
    (0x7aa64c#64,  0x6e381fff#32),   -- eor  v31.16b, v31.16b, v24.16b
    (0x7aa650#64,  0x6e261fde#32),   -- eor  v30.16b, v30.16b, v6.16b
    (0x7aa654#64,  0x0ef7e347#32),   -- pmull  v7.1q, v26.1d, v23.1d
    (0x7aa658#64,  0x6e371ca5#32),   -- eor  v5.16b, v5.16b, v23.16b
    (0x7aa65c#64,  0x4ef7e357#32),   -- pmull2  v23.1q, v26.2d, v23.2d
    (0x7aa660#64,  0x0ee5e365#32),   -- pmull  v5.1q, v27.1d, v5.1d
    (0x7aa664#64,  0x6e271fbd#32),   -- eor  v29.16b, v29.16b, v7.16b
    (0x7aa668#64,  0x6e371fff#32),   -- eor  v31.16b, v31.16b, v23.16b
    (0x7aa66c#64,  0x6e251fde#32),   -- eor  v30.16b, v30.16b, v5.16b
    (0x7aa670#64,  0xf1020063#32),   -- subs  x3, x3, #0x80
    (0x7aa674#64,  0x540006a3#32),   -- b.cc  7aa748 <.Ltail4x>  // b.lo, b.ul, b.last
    (0x7aa678#64,  0x14000002#32),   -- b  7aa680 <.Loop4x>
    (0x7aa67c#64,  0xd503201f#32),   -- nop

    -- 00000000007aa680 <.Loop4x>:
    (0x7aa680#64,  0x6e201c90#32),   -- eor  v16.16b, v4.16b, v0.16b
    (0x7aa684#64,  0x4cdf2c44#32),   -- ld1  {v4.2d-v7.2d}, [x2], #64
    (0x7aa688#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa68c#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7aa690#64,  0x4e2008c6#32),   -- rev64  v6.16b, v6.16b
    (0x7aa694#64,  0x4e2008e7#32),   -- rev64  v7.16b, v7.16b
    (0x7aa698#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7aa69c#64,  0x0ee3e380#32),   -- pmull  v0.1q, v28.1d, v3.1d
    (0x7aa6a0#64,  0x6e231e10#32),   -- eor  v16.16b, v16.16b, v3.16b
    (0x7aa6a4#64,  0x4ee3e382#32),   -- pmull2  v2.1q, v28.2d, v3.2d
    (0x7aa6a8#64,  0x6e0740f9#32),   -- ext  v25.16b, v7.16b, v7.16b, #8
    (0x7aa6ac#64,  0x4ef0e361#32),   -- pmull2  v1.1q, v27.2d, v16.2d
    (0x7aa6b0#64,  0x6e3d1c00#32),   -- eor  v0.16b, v0.16b, v29.16b
    (0x7aa6b4#64,  0x6e3f1c42#32),   -- eor  v2.16b, v2.16b, v31.16b
    (0x7aa6b8#64,  0x6e0640d8#32),   -- ext  v24.16b, v6.16b, v6.16b, #8
    (0x7aa6bc#64,  0x6e3e1c21#32),   -- eor  v1.16b, v1.16b, v30.16b
    (0x7aa6c0#64,  0x6e0540b7#32),   -- ext  v23.16b, v5.16b, v5.16b, #8
    (0x7aa6c4#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa6c8#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa6cc#64,  0x0ef9e29d#32),   -- pmull  v29.1q, v20.1d, v25.1d
    (0x7aa6d0#64,  0x6e391ce7#32),   -- eor  v7.16b, v7.16b, v25.16b
    (0x7aa6d4#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa6d8#64,  0x4ef9e29f#32),   -- pmull2  v31.1q, v20.2d, v25.2d
    (0x7aa6dc#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa6e0#64,  0x0ee7e2be#32),   -- pmull  v30.1q, v21.1d, v7.1d
    (0x7aa6e4#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa6e8#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa6ec#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa6f0#64,  0x0ef8e2d0#32),   -- pmull  v16.1q, v22.1d, v24.1d
    (0x7aa6f4#64,  0x6e381cc6#32),   -- eor  v6.16b, v6.16b, v24.16b
    (0x7aa6f8#64,  0x4ef8e2d8#32),   -- pmull2  v24.1q, v22.2d, v24.2d
    (0x7aa6fc#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa700#64,  0x4ee6e2a6#32),   -- pmull2  v6.1q, v21.2d, v6.2d
    (0x7aa704#64,  0x6e301fbd#32),   -- eor  v29.16b, v29.16b, v16.16b
    (0x7aa708#64,  0x6e381fff#32),   -- eor  v31.16b, v31.16b, v24.16b
    (0x7aa70c#64,  0x6e261fde#32),   -- eor  v30.16b, v30.16b, v6.16b
    (0x7aa710#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa714#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa718#64,  0x0ef7e347#32),   -- pmull  v7.1q, v26.1d, v23.1d
    (0x7aa71c#64,  0x6e371ca5#32),   -- eor  v5.16b, v5.16b, v23.16b
    (0x7aa720#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa724#64,  0x4ef7e357#32),   -- pmull2  v23.1q, v26.2d, v23.2d
    (0x7aa728#64,  0x0ee5e365#32),   -- pmull  v5.1q, v27.1d, v5.1d
    (0x7aa72c#64,  0x6e321c00#32),   -- eor  v0.16b, v0.16b, v18.16b
    (0x7aa730#64,  0x6e271fbd#32),   -- eor  v29.16b, v29.16b, v7.16b
    (0x7aa734#64,  0x6e371fff#32),   -- eor  v31.16b, v31.16b, v23.16b
    (0x7aa738#64,  0x6e004000#32),   -- ext  v0.16b, v0.16b, v0.16b, #8
    (0x7aa73c#64,  0x6e251fde#32),   -- eor  v30.16b, v30.16b, v5.16b
    (0x7aa740#64,  0xf1010063#32),   -- subs  x3, x3, #0x40
    (0x7aa744#64,  0x54fff9e2#32),   -- b.cs  7aa680 <.Loop4x>  // b.hs, b.nlast

    -- 00000000007aa748 <.Ltail4x>:
    (0x7aa748#64,  0x6e201c90#32),   -- eor  v16.16b, v4.16b, v0.16b
    (0x7aa74c#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa750#64,  0x0ee3e380#32),   -- pmull  v0.1q, v28.1d, v3.1d
    (0x7aa754#64,  0x6e231e10#32),   -- eor  v16.16b, v16.16b, v3.16b
    (0x7aa758#64,  0x4ee3e382#32),   -- pmull2  v2.1q, v28.2d, v3.2d
    (0x7aa75c#64,  0x4ef0e361#32),   -- pmull2  v1.1q, v27.2d, v16.2d
    (0x7aa760#64,  0x6e3d1c00#32),   -- eor  v0.16b, v0.16b, v29.16b
    (0x7aa764#64,  0x6e3f1c42#32),   -- eor  v2.16b, v2.16b, v31.16b
    (0x7aa768#64,  0x6e3e1c21#32),   -- eor  v1.16b, v1.16b, v30.16b
    (0x7aa76c#64,  0xb1010063#32),   -- adds  x3, x3, #0x40
    (0x7aa770#64,  0x54000c20#32),   -- b.eq  7aa8f4 <.Ldone4x>  // b.none
    (0x7aa774#64,  0xf100807f#32),   -- cmp  x3, #0x20
    (0x7aa778#64,  0x54000943#32),   -- b.cc  7aa8a0 <.Lone>  // b.lo, b.ul, b.last
    (0x7aa77c#64,  0x54000520#32),   -- b.eq  7aa820 <.Ltwo>  // b.none

    -- 00000000007aa780 <.Lthree>:
    (0x7aa780#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa784#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa788#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa78c#64,  0x4c406c44#32),   -- ld1  {v4.2d-v6.2d}, [x2]
    (0x7aa790#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa794#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7aa798#64,  0x4e2008c6#32),   -- rev64  v6.16b, v6.16b
    (0x7aa79c#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7aa7a0#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa7a4#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa7a8#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa7ac#64,  0x6e0640d8#32),   -- ext  v24.16b, v6.16b, v6.16b, #8
    (0x7aa7b0#64,  0x6e0540b7#32),   -- ext  v23.16b, v5.16b, v5.16b, #8
    (0x7aa7b4#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa7b8#64,  0x0ef8e29d#32),   -- pmull  v29.1q, v20.1d, v24.1d
    (0x7aa7bc#64,  0x6e381cc6#32),   -- eor  v6.16b, v6.16b, v24.16b
    (0x7aa7c0#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa7c4#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa7c8#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa7cc#64,  0x4ef8e29f#32),   -- pmull2  v31.1q, v20.2d, v24.2d
    (0x7aa7d0#64,  0x0ee6e2be#32),   -- pmull  v30.1q, v21.1d, v6.1d
    (0x7aa7d4#64,  0x6e321c00#32),   -- eor  v0.16b, v0.16b, v18.16b
    (0x7aa7d8#64,  0x0ef7e2c7#32),   -- pmull  v7.1q, v22.1d, v23.1d
    (0x7aa7dc#64,  0x6e371ca5#32),   -- eor  v5.16b, v5.16b, v23.16b
    (0x7aa7e0#64,  0x6e004000#32),   -- ext  v0.16b, v0.16b, v0.16b, #8
    (0x7aa7e4#64,  0x4ef7e2d7#32),   -- pmull2  v23.1q, v22.2d, v23.2d
    (0x7aa7e8#64,  0x6e201c90#32),   -- eor  v16.16b, v4.16b, v0.16b
    (0x7aa7ec#64,  0x4ee5e2a5#32),   -- pmull2  v5.1q, v21.2d, v5.2d
    (0x7aa7f0#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa7f4#64,  0x6e271fbd#32),   -- eor  v29.16b, v29.16b, v7.16b
    (0x7aa7f8#64,  0x6e371fff#32),   -- eor  v31.16b, v31.16b, v23.16b
    (0x7aa7fc#64,  0x6e251fde#32),   -- eor  v30.16b, v30.16b, v5.16b
    (0x7aa800#64,  0x0ee3e340#32),   -- pmull  v0.1q, v26.1d, v3.1d
    (0x7aa804#64,  0x6e231e10#32),   -- eor  v16.16b, v16.16b, v3.16b
    (0x7aa808#64,  0x4ee3e342#32),   -- pmull2  v2.1q, v26.2d, v3.2d
    (0x7aa80c#64,  0x0ef0e361#32),   -- pmull  v1.1q, v27.1d, v16.1d
    (0x7aa810#64,  0x6e3d1c00#32),   -- eor  v0.16b, v0.16b, v29.16b
    (0x7aa814#64,  0x6e3f1c42#32),   -- eor  v2.16b, v2.16b, v31.16b
    (0x7aa818#64,  0x6e3e1c21#32),   -- eor  v1.16b, v1.16b, v30.16b
    (0x7aa81c#64,  0x14000036#32),   -- b  7aa8f4 <.Ldone4x>

    -- 00000000007aa820 <.Ltwo>:
    (0x7aa820#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa824#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa828#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa82c#64,  0x4c40ac44#32),   -- ld1  {v4.2d, v5.2d}, [x2]
    (0x7aa830#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa834#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7aa838#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7aa83c#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa840#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa844#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa848#64,  0x6e0540b7#32),   -- ext  v23.16b, v5.16b, v5.16b, #8
    (0x7aa84c#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa850#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa854#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa858#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa85c#64,  0x6e321c00#32),   -- eor  v0.16b, v0.16b, v18.16b
    (0x7aa860#64,  0x6e004000#32),   -- ext  v0.16b, v0.16b, v0.16b, #8
    (0x7aa864#64,  0x0ef7e29d#32),   -- pmull  v29.1q, v20.1d, v23.1d
    (0x7aa868#64,  0x6e371ca5#32),   -- eor  v5.16b, v5.16b, v23.16b
    (0x7aa86c#64,  0x6e201c90#32),   -- eor  v16.16b, v4.16b, v0.16b
    (0x7aa870#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa874#64,  0x4ef7e29f#32),   -- pmull2  v31.1q, v20.2d, v23.2d
    (0x7aa878#64,  0x0ee5e2be#32),   -- pmull  v30.1q, v21.1d, v5.1d
    (0x7aa87c#64,  0x0ee3e2c0#32),   -- pmull  v0.1q, v22.1d, v3.1d
    (0x7aa880#64,  0x6e231e10#32),   -- eor  v16.16b, v16.16b, v3.16b
    (0x7aa884#64,  0x4ee3e2c2#32),   -- pmull2  v2.1q, v22.2d, v3.2d
    (0x7aa888#64,  0x4ef0e2a1#32),   -- pmull2  v1.1q, v21.2d, v16.2d
    (0x7aa88c#64,  0x6e3d1c00#32),   -- eor  v0.16b, v0.16b, v29.16b
    (0x7aa890#64,  0x6e3f1c42#32),   -- eor  v2.16b, v2.16b, v31.16b
    (0x7aa894#64,  0x6e3e1c21#32),   -- eor  v1.16b, v1.16b, v30.16b
    (0x7aa898#64,  0x14000017#32),   -- b  7aa8f4 <.Ldone4x>
    (0x7aa89c#64,  0xd503201f#32),   -- nop

    -- 00000000007aa8a0 <.Lone>:
    (0x7aa8a0#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa8a4#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa8a8#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa8ac#64,  0x4c407c44#32),   -- ld1  {v4.2d}, [x2]
    (0x7aa8b0#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa8b4#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7aa8b8#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa8bc#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa8c0#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa8c4#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa8c8#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa8cc#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa8d0#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa8d4#64,  0x6e321c00#32),   -- eor  v0.16b, v0.16b, v18.16b
    (0x7aa8d8#64,  0x6e004000#32),   -- ext  v0.16b, v0.16b, v0.16b, #8
    (0x7aa8dc#64,  0x6e201c90#32),   -- eor  v16.16b, v4.16b, v0.16b
    (0x7aa8e0#64,  0x6e104203#32),   -- ext  v3.16b, v16.16b, v16.16b, #8
    (0x7aa8e4#64,  0x0ee3e280#32),   -- pmull  v0.1q, v20.1d, v3.1d
    (0x7aa8e8#64,  0x6e231e10#32),   -- eor  v16.16b, v16.16b, v3.16b
    (0x7aa8ec#64,  0x4ee3e282#32),   -- pmull2  v2.1q, v20.2d, v3.2d
    (0x7aa8f0#64,  0x0ef0e2a1#32),   -- pmull  v1.1q, v21.1d, v16.1d

    -- 00000000007aa8f4 <.Ldone4x>:
    (0x7aa8f4#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa8f8#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa8fc#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa900#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa904#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa908#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa90c#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa910#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa914#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa918#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa91c#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa920#64,  0x6e321c00#32),   -- eor  v0.16b, v0.16b, v18.16b
    (0x7aa924#64,  0x6e004000#32),   -- ext  v0.16b, v0.16b, v0.16b, #8
    (0x7aa928#64,  0x4e200800#32),   -- rev64  v0.16b, v0.16b
    (0x7aa92c#64,  0x4c007c00#32),   -- st1  {v0.2d}, [x0]
    (0x7aa930#64,  0xd65f03c0#32),   -- ret
  ]

end GCMGhashV8Program
