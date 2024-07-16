/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec

namespace AESGCMEncKernelProgram

open BitVec

/-

  void aes_gcm_enc_kernel(const uint8_t *in, uint64_t in_bits, void *out,
                          void *Xi, uint8_t *ivec, const AES_KEY *key,
                          const u128 Htable[16]);

  input: in -- input message blocks (x0)
         in_bits -- input message length in bits (x1)
         Xi -- current hash/tag value (x3)
         ivec -- counter (x4)
         key -- AES key schedule and rounds (x5)
         Htable -- powers of H precomputed up to H^12 (x6)
  output: out -- ciphertext (x2)
          Xi -- current hash/tag value (x3)

-/

def aes_gcm_enc_kernel_program : Program :=
  def_program
  [ -- 00000000007a0cf0 <aes_gcm_enc_kernel>:
    (0x7a0cf0#64,  0xa9b87bfd#32),   -- stp  x29, x30, [sp, #-128]!
    (0x7a0cf4#64,  0x910003fd#32),   -- mov  x29, sp
    (0x7a0cf8#64,  0xa90153f3#32),   -- stp  x19, x20, [sp, #16]
    (0x7a0cfc#64,  0xaa0403f0#32),   -- mov  x16, x4
    (0x7a0d00#64,  0xaa0503e8#32),   -- mov  x8, x5
    (0x7a0d04#64,  0xa9025bf5#32),   -- stp  x21, x22, [sp, #32]
    (0x7a0d08#64,  0xa90363f7#32),   -- stp  x23, x24, [sp, #48]
    (0x7a0d0c#64,  0x6d0427e8#32),   -- stp  d8, d9, [sp, #64]
    (0x7a0d10#64,  0x6d052fea#32),   -- stp  d10, d11, [sp, #80]
    (0x7a0d14#64,  0x6d0637ec#32),   -- stp  d12, d13, [sp, #96]
    (0x7a0d18#64,  0x6d073fee#32),   -- stp  d14, d15, [sp, #112]
    (0x7a0d1c#64,  0xb940f111#32),   -- ldr  w17, [x8, #240]
    (0x7a0d20#64,  0x8b111113#32),   -- add  x19, x8, x17, lsl #4
    (0x7a0d24#64,  0xa9403a6d#32),   -- ldp  x13, x14, [x19]
    (0x7a0d28#64,  0x3cdf027f#32),   -- ldur  q31, [x19, #-16]
    (0x7a0d2c#64,  0x8b410c04#32),   -- add  x4, x0, x1, lsr #3
    (0x7a0d30#64,  0xd343fc25#32),   -- lsr  x5, x1, #3
    (0x7a0d34#64,  0xaa0503ef#32),   -- mov  x15, x5
    (0x7a0d38#64,  0xa9402e0a#32),   -- ldp  x10, x11, [x16]
    (0x7a0d3c#64,  0x4c407200#32),   -- ld1  {v0.16b}, [x16]
    (0x7a0d40#64,  0xd10004a5#32),   -- sub  x5, x5, #0x1
    (0x7a0d44#64,  0x3dc00112#32),   -- ldr  q18, [x8]
    (0x7a0d48#64,  0x927ae4a5#32),   -- and  x5, x5, #0xffffffffffffffc0
    (0x7a0d4c#64,  0x3dc01d19#32),   -- ldr  q25, [x8, #112]
    (0x7a0d50#64,  0x8b0000a5#32),   -- add  x5, x5, x0
    (0x7a0d54#64,  0xd360fd6c#32),   -- lsr  x12, x11, #32
    (0x7a0d58#64,  0x9e670142#32),   -- fmov  d2, x10
    (0x7a0d5c#64,  0x2a0b016b#32),   -- orr  w11, w11, w11
    (0x7a0d60#64,  0x5ac0098c#32),   -- rev  w12, w12
    (0x7a0d64#64,  0x9e670141#32),   -- fmov  d1, x10
    (0x7a0d68#64,  0x4e284a40#32),   -- aese  v0.16b, v18.16b
    (0x7a0d6c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0d70#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a0d74#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a0d78#64,  0x9e670143#32),   -- fmov  d3, x10
    (0x7a0d7c#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a0d80#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a0d84#64,  0x3dc00513#32),   -- ldr  q19, [x8, #16]
    (0x7a0d88#64,  0x9eaf0121#32),   -- fmov  v1.d[1], x9
    (0x7a0d8c#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a0d90#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a0d94#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a0d98#64,  0x3dc00914#32),   -- ldr  q20, [x8, #32]
    (0x7a0d9c#64,  0x9eaf0122#32),   -- fmov  v2.d[1], x9
    (0x7a0da0#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a0da4#64,  0x4e284a60#32),   -- aese  v0.16b, v19.16b
    (0x7a0da8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0dac#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a0db0#64,  0x9eaf0123#32),   -- fmov  v3.d[1], x9
    (0x7a0db4#64,  0x4e284a41#32),   -- aese  v1.16b, v18.16b
    (0x7a0db8#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0dbc#64,  0x3dc00d15#32),   -- ldr  q21, [x8, #48]
    (0x7a0dc0#64,  0x4e284a80#32),   -- aese  v0.16b, v20.16b
    (0x7a0dc4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0dc8#64,  0x3dc01918#32),   -- ldr  q24, [x8, #96]
    (0x7a0dcc#64,  0x4e284a42#32),   -- aese  v2.16b, v18.16b
    (0x7a0dd0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0dd4#64,  0x3dc01517#32),   -- ldr  q23, [x8, #80]
    (0x7a0dd8#64,  0x4e284a61#32),   -- aese  v1.16b, v19.16b
    (0x7a0ddc#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0de0#64,  0x3dc00cce#32),   -- ldr  q14, [x6, #48]
    (0x7a0de4#64,  0x6e0e41ce#32),   -- ext  v14.16b, v14.16b, v14.16b, #8
    (0x7a0de8#64,  0x4e284a43#32),   -- aese  v3.16b, v18.16b
    (0x7a0dec#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0df0#64,  0x4e284a62#32),   -- aese  v2.16b, v19.16b
    (0x7a0df4#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0df8#64,  0x3dc01116#32),   -- ldr  q22, [x8, #64]
    (0x7a0dfc#64,  0x4e284a81#32),   -- aese  v1.16b, v20.16b
    (0x7a0e00#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0e04#64,  0x3dc008cd#32),   -- ldr  q13, [x6, #32]
    (0x7a0e08#64,  0x6e0d41ad#32),   -- ext  v13.16b, v13.16b, v13.16b, #8
    (0x7a0e0c#64,  0x4e284a63#32),   -- aese  v3.16b, v19.16b
    (0x7a0e10#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0e14#64,  0x3dc0311e#32),   -- ldr  q30, [x8, #192]
    (0x7a0e18#64,  0x4e284a82#32),   -- aese  v2.16b, v20.16b
    (0x7a0e1c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0e20#64,  0x3dc014cf#32),   -- ldr  q15, [x6, #80]
    (0x7a0e24#64,  0x6e0f41ef#32),   -- ext  v15.16b, v15.16b, v15.16b, #8
    (0x7a0e28#64,  0x4e284aa1#32),   -- aese  v1.16b, v21.16b
    (0x7a0e2c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0e30#64,  0x3dc02d1d#32),   -- ldr  q29, [x8, #176]
    (0x7a0e34#64,  0x4e284a83#32),   -- aese  v3.16b, v20.16b
    (0x7a0e38#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0e3c#64,  0x3dc0211a#32),   -- ldr  q26, [x8, #128]
    (0x7a0e40#64,  0x4e284aa2#32),   -- aese  v2.16b, v21.16b
    (0x7a0e44#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0e48#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a0e4c#64,  0x4e284aa0#32),   -- aese  v0.16b, v21.16b
    (0x7a0e50#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0e54#64,  0x4e284aa3#32),   -- aese  v3.16b, v21.16b
    (0x7a0e58#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0e5c#64,  0x4c40706b#32),   -- ld1  {v11.16b}, [x3]
    (0x7a0e60#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a0e64#64,  0x4e20096b#32),   -- rev64  v11.16b, v11.16b
    (0x7a0e68#64,  0x4e284ac2#32),   -- aese  v2.16b, v22.16b
    (0x7a0e6c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0e70#64,  0x4e284ac0#32),   -- aese  v0.16b, v22.16b
    (0x7a0e74#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0e78#64,  0x4e284ac1#32),   -- aese  v1.16b, v22.16b
    (0x7a0e7c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0e80#64,  0x4e284ac3#32),   -- aese  v3.16b, v22.16b
    (0x7a0e84#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0e88#64,  0xf100323f#32),   -- cmp  x17, #0xc
    (0x7a0e8c#64,  0x4e284ae0#32),   -- aese  v0.16b, v23.16b
    (0x7a0e90#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0e94#64,  0x4e284ae1#32),   -- aese  v1.16b, v23.16b
    (0x7a0e98#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0e9c#64,  0x4e284ae3#32),   -- aese  v3.16b, v23.16b
    (0x7a0ea0#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0ea4#64,  0x4e284ae2#32),   -- aese  v2.16b, v23.16b
    (0x7a0ea8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0eac#64,  0x4e284b01#32),   -- aese  v1.16b, v24.16b
    (0x7a0eb0#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0eb4#64,  0x4ecf69d1#32),   -- trn2  v17.2d, v14.2d, v15.2d
    (0x7a0eb8#64,  0x4e284b03#32),   -- aese  v3.16b, v24.16b
    (0x7a0ebc#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0ec0#64,  0x3dc0251b#32),   -- ldr  q27, [x8, #144]
    (0x7a0ec4#64,  0x4e284b00#32),   -- aese  v0.16b, v24.16b
    (0x7a0ec8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0ecc#64,  0x3dc000cc#32),   -- ldr  q12, [x6]
    (0x7a0ed0#64,  0x6e0c418c#32),   -- ext  v12.16b, v12.16b, v12.16b, #8
    (0x7a0ed4#64,  0x4e284b02#32),   -- aese  v2.16b, v24.16b
    (0x7a0ed8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0edc#64,  0x3dc0291c#32),   -- ldr  q28, [x8, #160]
    (0x7a0ee0#64,  0x4e284b21#32),   -- aese  v1.16b, v25.16b
    (0x7a0ee4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0ee8#64,  0x4ecf29c9#32),   -- trn1  v9.2d, v14.2d, v15.2d
    (0x7a0eec#64,  0x4e284b20#32),   -- aese  v0.16b, v25.16b
    (0x7a0ef0#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0ef4#64,  0x4e284b22#32),   -- aese  v2.16b, v25.16b
    (0x7a0ef8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0efc#64,  0x4e284b23#32),   -- aese  v3.16b, v25.16b
    (0x7a0f00#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0f04#64,  0x4ecd6990#32),   -- trn2  v16.2d, v12.2d, v13.2d
    (0x7a0f08#64,  0x4e284b41#32),   -- aese  v1.16b, v26.16b
    (0x7a0f0c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0f10#64,  0x4e284b42#32),   -- aese  v2.16b, v26.16b
    (0x7a0f14#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0f18#64,  0x4e284b43#32),   -- aese  v3.16b, v26.16b
    (0x7a0f1c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0f20#64,  0x4e284b40#32),   -- aese  v0.16b, v26.16b
    (0x7a0f24#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0f28#64,  0x5400044b#32),   -- b.lt  7a0fb0 <.Lenc_finish_first_blocks>  // b.tstop
    (0x7a0f2c#64,  0x4e284b61#32),   -- aese  v1.16b, v27.16b
    (0x7a0f30#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0f34#64,  0x4e284b62#32),   -- aese  v2.16b, v27.16b
    (0x7a0f38#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0f3c#64,  0x4e284b63#32),   -- aese  v3.16b, v27.16b
    (0x7a0f40#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0f44#64,  0x4e284b60#32),   -- aese  v0.16b, v27.16b
    (0x7a0f48#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0f4c#64,  0x4e284b81#32),   -- aese  v1.16b, v28.16b
    (0x7a0f50#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0f54#64,  0x4e284b82#32),   -- aese  v2.16b, v28.16b
    (0x7a0f58#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0f5c#64,  0x4e284b83#32),   -- aese  v3.16b, v28.16b
    (0x7a0f60#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0f64#64,  0x4e284b80#32),   -- aese  v0.16b, v28.16b
    (0x7a0f68#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0f6c#64,  0x54000220#32),   -- b.eq  7a0fb0 <.Lenc_finish_first_blocks>  // b.none
    (0x7a0f70#64,  0x4e284ba1#32),   -- aese  v1.16b, v29.16b
    (0x7a0f74#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0f78#64,  0x4e284ba2#32),   -- aese  v2.16b, v29.16b
    (0x7a0f7c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0f80#64,  0x4e284ba0#32),   -- aese  v0.16b, v29.16b
    (0x7a0f84#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0f88#64,  0x4e284ba3#32),   -- aese  v3.16b, v29.16b
    (0x7a0f8c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a0f90#64,  0x4e284bc1#32),   -- aese  v1.16b, v30.16b
    (0x7a0f94#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a0f98#64,  0x4e284bc2#32),   -- aese  v2.16b, v30.16b
    (0x7a0f9c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a0fa0#64,  0x4e284bc0#32),   -- aese  v0.16b, v30.16b
    (0x7a0fa4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a0fa8#64,  0x4e284bc3#32),   -- aese  v3.16b, v30.16b
    (0x7a0fac#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b

    -- 00000000007a0fb0 <.Lenc_finish_first_blocks>:
    (0x7a0fb0#64,  0xeb05001f#32),   -- cmp  x0, x5
    (0x7a0fb4#64,  0x6e291e31#32),   -- eor  v17.16b, v17.16b, v9.16b
    (0x7a0fb8#64,  0x4e284be2#32),   -- aese  v2.16b, v31.16b
    (0x7a0fbc#64,  0x4ecd2988#32),   -- trn1  v8.2d, v12.2d, v13.2d
    (0x7a0fc0#64,  0x4e284be1#32),   -- aese  v1.16b, v31.16b
    (0x7a0fc4#64,  0x4e284be0#32),   -- aese  v0.16b, v31.16b
    (0x7a0fc8#64,  0x4e284be3#32),   -- aese  v3.16b, v31.16b
    (0x7a0fcc#64,  0x6e281e10#32),   -- eor  v16.16b, v16.16b, v8.16b
    (0x7a0fd0#64,  0x540034ea#32),   -- b.ge  7a166c <.Lenc_tail>  // b.tcont
    (0x7a0fd4#64,  0xa9415013#32),   -- ldp  x19, x20, [x0, #16]
    (0x7a0fd8#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a0fdc#64,  0xa9401c06#32),   -- ldp  x6, x7, [x0]
    (0x7a0fe0#64,  0xa9436017#32),   -- ldp  x23, x24, [x0, #48]
    (0x7a0fe4#64,  0xa9425815#32),   -- ldp  x21, x22, [x0, #32]
    (0x7a0fe8#64,  0x91010000#32),   -- add  x0, x0, #0x40
    (0x7a0fec#64,  0xca0d0273#32),   -- eor  x19, x19, x13
    (0x7a0ff0#64,  0xca0e0294#32),   -- eor  x20, x20, x14
    (0x7a0ff4#64,  0x9e670265#32),   -- fmov  d5, x19
    (0x7a0ff8#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a0ffc#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a1000#64,  0xca0e0318#32),   -- eor  x24, x24, x14
    (0x7a1004#64,  0x9e6700c4#32),   -- fmov  d4, x6
    (0x7a1008#64,  0xeb05001f#32),   -- cmp  x0, x5
    (0x7a100c#64,  0x9eaf00e4#32),   -- fmov  v4.d[1], x7
    (0x7a1010#64,  0xca0d02f7#32),   -- eor  x23, x23, x13
    (0x7a1014#64,  0xca0d02b5#32),   -- eor  x21, x21, x13
    (0x7a1018#64,  0x9eaf0285#32),   -- fmov  v5.d[1], x20
    (0x7a101c#64,  0x9e6702a6#32),   -- fmov  d6, x21
    (0x7a1020#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1024#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1028#64,  0x9e6702e7#32),   -- fmov  d7, x23
    (0x7a102c#64,  0xca0e02d6#32),   -- eor  x22, x22, x14
    (0x7a1030#64,  0x9eaf02c6#32),   -- fmov  v6.d[1], x22
    (0x7a1034#64,  0x6e201c84#32),   -- eor  v4.16b, v4.16b, v0.16b
    (0x7a1038#64,  0x9e670140#32),   -- fmov  d0, x10
    (0x7a103c#64,  0x9eaf0120#32),   -- fmov  v0.d[1], x9
    (0x7a1040#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1044#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1048#64,  0x6e211ca5#32),   -- eor  v5.16b, v5.16b, v1.16b
    (0x7a104c#64,  0x9e670141#32),   -- fmov  d1, x10
    (0x7a1050#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1054#64,  0x9eaf0121#32),   -- fmov  v1.d[1], x9
    (0x7a1058#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a105c#64,  0x4c9f7044#32),   -- st1  {v4.16b}, [x2], #16
    (0x7a1060#64,  0x9eaf0307#32),   -- fmov  v7.d[1], x24
    (0x7a1064#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1068#64,  0x6e221cc6#32),   -- eor  v6.16b, v6.16b, v2.16b
    (0x7a106c#64,  0x4c9f7045#32),   -- st1  {v5.16b}, [x2], #16
    (0x7a1070#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1074#64,  0x9e670142#32),   -- fmov  d2, x10
    (0x7a1078#64,  0x9eaf0122#32),   -- fmov  v2.d[1], x9
    (0x7a107c#64,  0x4c9f7046#32),   -- st1  {v6.16b}, [x2], #16
    (0x7a1080#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1084#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1088#64,  0x6e231ce7#32),   -- eor  v7.16b, v7.16b, v3.16b
    (0x7a108c#64,  0x4c9f7047#32),   -- st1  {v7.16b}, [x2], #16
    (0x7a1090#64,  0x54001a8a#32),   -- b.ge  7a13e0 <.Lenc_prepretail>  // b.tcont

    -- 00000000007a1094 <.Lenc_main_loop>:
    (0x7a1094#64,  0x4e284a40#32),   -- aese  v0.16b, v18.16b
    (0x7a1098#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a109c#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7a10a0#64,  0x4e284a41#32),   -- aese  v1.16b, v18.16b
    (0x7a10a4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a10a8#64,  0x9e670143#32),   -- fmov  d3, x10
    (0x7a10ac#64,  0x4e284a42#32),   -- aese  v2.16b, v18.16b
    (0x7a10b0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a10b4#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a10b8#64,  0x4e284a60#32),   -- aese  v0.16b, v19.16b
    (0x7a10bc#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a10c0#64,  0x9eaf0123#32),   -- fmov  v3.d[1], x9
    (0x7a10c4#64,  0x4e284a61#32),   -- aese  v1.16b, v19.16b
    (0x7a10c8#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a10cc#64,  0xa9436017#32),   -- ldp  x23, x24, [x0, #48]
    (0x7a10d0#64,  0x4e284a62#32),   -- aese  v2.16b, v19.16b
    (0x7a10d4#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a10d8#64,  0xa9425815#32),   -- ldp  x21, x22, [x0, #32]
    (0x7a10dc#64,  0x4e284a80#32),   -- aese  v0.16b, v20.16b
    (0x7a10e0#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a10e4#64,  0x6e2b1c84#32),   -- eor  v4.16b, v4.16b, v11.16b
    (0x7a10e8#64,  0x4e284a81#32),   -- aese  v1.16b, v20.16b
    (0x7a10ec#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a10f0#64,  0x4e284a43#32),   -- aese  v3.16b, v18.16b
    (0x7a10f4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a10f8#64,  0xca0d02f7#32),   -- eor  x23, x23, x13
    (0x7a10fc#64,  0x4e284aa0#32),   -- aese  v0.16b, v21.16b
    (0x7a1100#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1104#64,  0x5e18062a#32),   -- mov  d10, v17.d[1]
    (0x7a1108#64,  0x4eefe089#32),   -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7a110c#64,  0xca0e02d6#32),   -- eor  x22, x22, x14
    (0x7a1110#64,  0x5e180488#32),   -- mov  d8, v4.d[1]
    (0x7a1114#64,  0x4e284a63#32),   -- aese  v3.16b, v19.16b
    (0x7a1118#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a111c#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7a1120#64,  0x4e284ac0#32),   -- aese  v0.16b, v22.16b
    (0x7a1124#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1128#64,  0x0eefe08b#32),   -- pmull  v11.1q, v4.1d, v15.1d
    (0x7a112c#64,  0x2e241d08#32),   -- eor  v8.8b, v8.8b, v4.8b
    (0x7a1130#64,  0x4e284a82#32),   -- aese  v2.16b, v20.16b
    (0x7a1134#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1138#64,  0x4e284ae0#32),   -- aese  v0.16b, v23.16b
    (0x7a113c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1140#64,  0x4e2008e7#32),   -- rev64  v7.16b, v7.16b
    (0x7a1144#64,  0x4eeee0a4#32),   -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7a1148#64,  0x0eeae10a#32),   -- pmull  v10.1q, v8.1d, v10.1d
    (0x7a114c#64,  0x4e2008c6#32),   -- rev64  v6.16b, v6.16b
    (0x7a1150#64,  0x0eeee0a8#32),   -- pmull  v8.1q, v5.1d, v14.1d
    (0x7a1154#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a1158#64,  0x5e1804a4#32),   -- mov  d4, v5.d[1]
    (0x7a115c#64,  0x4e284aa1#32),   -- aese  v1.16b, v21.16b
    (0x7a1160#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1164#64,  0x4e284a83#32),   -- aese  v3.16b, v20.16b
    (0x7a1168#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a116c#64,  0x6e281d6b#32),   -- eor  v11.16b, v11.16b, v8.16b
    (0x7a1170#64,  0x4e284aa2#32),   -- aese  v2.16b, v21.16b
    (0x7a1174#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1178#64,  0x4e284ac1#32),   -- aese  v1.16b, v22.16b
    (0x7a117c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1180#64,  0x5e1804c8#32),   -- mov  d8, v6.d[1]
    (0x7a1184#64,  0x4e284aa3#32),   -- aese  v3.16b, v21.16b
    (0x7a1188#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a118c#64,  0x2e251c84#32),   -- eor  v4.8b, v4.8b, v5.8b
    (0x7a1190#64,  0x4e284ac2#32),   -- aese  v2.16b, v22.16b
    (0x7a1194#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1198#64,  0x4e284b00#32),   -- aese  v0.16b, v24.16b
    (0x7a119c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a11a0#64,  0x2e261d08#32),   -- eor  v8.8b, v8.8b, v6.8b
    (0x7a11a4#64,  0x4e284ac3#32),   -- aese  v3.16b, v22.16b
    (0x7a11a8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a11ac#64,  0x0ef1e084#32),   -- pmull  v4.1q, v4.1d, v17.1d
    (0x7a11b0#64,  0x4e284b20#32),   -- aese  v0.16b, v25.16b
    (0x7a11b4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a11b8#64,  0x4e284ae3#32),   -- aese  v3.16b, v23.16b
    (0x7a11bc#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a11c0#64,  0x6e180508#32),   -- mov  v8.d[1], v8.d[0]
    (0x7a11c4#64,  0x4e284ae1#32),   -- aese  v1.16b, v23.16b
    (0x7a11c8#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a11cc#64,  0x4e284b40#32),   -- aese  v0.16b, v26.16b
    (0x7a11d0#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a11d4#64,  0x4e284ae2#32),   -- aese  v2.16b, v23.16b
    (0x7a11d8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a11dc#64,  0x4e284b01#32),   -- aese  v1.16b, v24.16b
    (0x7a11e0#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a11e4#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a11e8#64,  0x4eede0c4#32),   -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7a11ec#64,  0x0eede0c5#32),   -- pmull  v5.1q, v6.1d, v13.1d
    (0x7a11f0#64,  0x4e284b21#32),   -- aese  v1.16b, v25.16b
    (0x7a11f4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a11f8#64,  0x0eece0e6#32),   -- pmull  v6.1q, v7.1d, v12.1d
    (0x7a11fc#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a1200#64,  0x4e284b03#32),   -- aese  v3.16b, v24.16b
    (0x7a1204#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1208#64,  0xa9415013#32),   -- ldp  x19, x20, [x0, #16]
    (0x7a120c#64,  0x4e284b41#32),   -- aese  v1.16b, v26.16b
    (0x7a1210#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1214#64,  0x5e1804e4#32),   -- mov  d4, v7.d[1]
    (0x7a1218#64,  0x4e284b02#32),   -- aese  v2.16b, v24.16b
    (0x7a121c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1220#64,  0x6e251d6b#32),   -- eor  v11.16b, v11.16b, v5.16b
    (0x7a1224#64,  0x4ef0e108#32),   -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7a1228#64,  0x4eece0e5#32),   -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7a122c#64,  0x2e271c84#32),   -- eor  v4.8b, v4.8b, v7.8b
    (0x7a1230#64,  0x4e284b22#32),   -- aese  v2.16b, v25.16b
    (0x7a1234#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1238#64,  0xca0d0273#32),   -- eor  x19, x19, x13
    (0x7a123c#64,  0x4e284b42#32),   -- aese  v2.16b, v26.16b
    (0x7a1240#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1244#64,  0x6e281d4a#32),   -- eor  v10.16b, v10.16b, v8.16b
    (0x7a1248#64,  0x4e284b23#32),   -- aese  v3.16b, v25.16b
    (0x7a124c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1250#64,  0xca0d02b5#32),   -- eor  x21, x21, x13
    (0x7a1254#64,  0x4e284b43#32),   -- aese  v3.16b, v26.16b
    (0x7a1258#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a125c#64,  0x0f06e448#32),   -- movi  v8.8b, #0xc2
    (0x7a1260#64,  0x0ef0e084#32),   -- pmull  v4.1q, v4.1d, v16.1d
    (0x7a1264#64,  0x6e251d29#32),   -- eor  v9.16b, v9.16b, v5.16b
    (0x7a1268#64,  0xf100323f#32),   -- cmp  x17, #0xc
    (0x7a126c#64,  0x9e670265#32),   -- fmov  d5, x19
    (0x7a1270#64,  0xa9401c06#32),   -- ldp  x6, x7, [x0]
    (0x7a1274#64,  0x5400044b#32),   -- b.lt  7a12fc <.Lenc_main_loop_continue>  // b.tstop
    (0x7a1278#64,  0x4e284b61#32),   -- aese  v1.16b, v27.16b
    (0x7a127c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1280#64,  0x4e284b60#32),   -- aese  v0.16b, v27.16b
    (0x7a1284#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1288#64,  0x4e284b62#32),   -- aese  v2.16b, v27.16b
    (0x7a128c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1290#64,  0x4e284b63#32),   -- aese  v3.16b, v27.16b
    (0x7a1294#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1298#64,  0x4e284b80#32),   -- aese  v0.16b, v28.16b
    (0x7a129c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a12a0#64,  0x4e284b81#32),   -- aese  v1.16b, v28.16b
    (0x7a12a4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a12a8#64,  0x4e284b82#32),   -- aese  v2.16b, v28.16b
    (0x7a12ac#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a12b0#64,  0x4e284b83#32),   -- aese  v3.16b, v28.16b
    (0x7a12b4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a12b8#64,  0x54000220#32),   -- b.eq  7a12fc <.Lenc_main_loop_continue>  // b.none
    (0x7a12bc#64,  0x4e284ba0#32),   -- aese  v0.16b, v29.16b
    (0x7a12c0#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a12c4#64,  0x4e284ba1#32),   -- aese  v1.16b, v29.16b
    (0x7a12c8#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a12cc#64,  0x4e284ba2#32),   -- aese  v2.16b, v29.16b
    (0x7a12d0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a12d4#64,  0x4e284ba3#32),   -- aese  v3.16b, v29.16b
    (0x7a12d8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a12dc#64,  0x4e284bc1#32),   -- aese  v1.16b, v30.16b
    (0x7a12e0#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a12e4#64,  0x4e284bc0#32),   -- aese  v0.16b, v30.16b
    (0x7a12e8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a12ec#64,  0x4e284bc2#32),   -- aese  v2.16b, v30.16b
    (0x7a12f0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a12f4#64,  0x4e284bc3#32),   -- aese  v3.16b, v30.16b
    (0x7a12f8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b

    -- 00000000007a12fc <.Lenc_main_loop_continue>:
    (0x7a12fc#64,  0x5f785508#32),   -- shl  d8, d8, #56
    (0x7a1300#64,  0x6e261d6b#32),   -- eor  v11.16b, v11.16b, v6.16b
    (0x7a1304#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a1308#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a130c#64,  0x6e291d64#32),   -- eor  v4.16b, v11.16b, v9.16b
    (0x7a1310#64,  0x91010000#32),   -- add  x0, x0, #0x40
    (0x7a1314#64,  0x0ee8e127#32),   -- pmull  v7.1q, v9.1d, v8.1d
    (0x7a1318#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a131c#64,  0x6e094129#32),   -- ext  v9.16b, v9.16b, v9.16b, #8
    (0x7a1320#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a1324#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a1328#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a132c#64,  0x9e6700c4#32),   -- fmov  d4, x6
    (0x7a1330#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1334#64,  0x6e271d27#32),   -- eor  v7.16b, v9.16b, v7.16b
    (0x7a1338#64,  0xca0e0294#32),   -- eor  x20, x20, x14
    (0x7a133c#64,  0xca0e0318#32),   -- eor  x24, x24, x14
    (0x7a1340#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1344#64,  0x4e284be0#32),   -- aese  v0.16b, v31.16b
    (0x7a1348#64,  0x9eaf00e4#32),   -- fmov  v4.d[1], x7
    (0x7a134c#64,  0x6e271d4a#32),   -- eor  v10.16b, v10.16b, v7.16b
    (0x7a1350#64,  0x9e6702e7#32),   -- fmov  d7, x23
    (0x7a1354#64,  0x4e284be1#32),   -- aese  v1.16b, v31.16b
    (0x7a1358#64,  0x9eaf0285#32),   -- fmov  v5.d[1], x20
    (0x7a135c#64,  0x9e6702a6#32),   -- fmov  d6, x21
    (0x7a1360#64,  0xeb05001f#32),   -- cmp  x0, x5
    (0x7a1364#64,  0x9eaf02c6#32),   -- fmov  v6.d[1], x22
    (0x7a1368#64,  0x0ee8e149#32),   -- pmull  v9.1q, v10.1d, v8.1d
    (0x7a136c#64,  0x6e201c84#32),   -- eor  v4.16b, v4.16b, v0.16b
    (0x7a1370#64,  0x9e670140#32),   -- fmov  d0, x10
    (0x7a1374#64,  0x9eaf0120#32),   -- fmov  v0.d[1], x9
    (0x7a1378#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a137c#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1380#64,  0x6e211ca5#32),   -- eor  v5.16b, v5.16b, v1.16b
    (0x7a1384#64,  0x9e670141#32),   -- fmov  d1, x10
    (0x7a1388#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a138c#64,  0x9eaf0121#32),   -- fmov  v1.d[1], x9
    (0x7a1390#64,  0x4e284be2#32),   -- aese  v2.16b, v31.16b
    (0x7a1394#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1398#64,  0x4c9f7044#32),   -- st1  {v4.16b}, [x2], #16
    (0x7a139c#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a13a0#64,  0x6e291d6b#32),   -- eor  v11.16b, v11.16b, v9.16b
    (0x7a13a4#64,  0x9eaf0307#32),   -- fmov  v7.d[1], x24
    (0x7a13a8#64,  0x6e0a414a#32),   -- ext  v10.16b, v10.16b, v10.16b, #8
    (0x7a13ac#64,  0x4c9f7045#32),   -- st1  {v5.16b}, [x2], #16
    (0x7a13b0#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a13b4#64,  0x4e284be3#32),   -- aese  v3.16b, v31.16b
    (0x7a13b8#64,  0x6e221cc6#32),   -- eor  v6.16b, v6.16b, v2.16b
    (0x7a13bc#64,  0x9e670142#32),   -- fmov  d2, x10
    (0x7a13c0#64,  0x4c9f7046#32),   -- st1  {v6.16b}, [x2], #16
    (0x7a13c4#64,  0x9eaf0122#32),   -- fmov  v2.d[1], x9
    (0x7a13c8#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a13cc#64,  0x6e2a1d6b#32),   -- eor  v11.16b, v11.16b, v10.16b
    (0x7a13d0#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a13d4#64,  0x6e231ce7#32),   -- eor  v7.16b, v7.16b, v3.16b
    (0x7a13d8#64,  0x4c9f7047#32),   -- st1  {v7.16b}, [x2], #16
    (0x7a13dc#64,  0x54ffe5cb#32),   -- b.lt  7a1094 <.Lenc_main_loop>  // b.tstop

    -- 00000000007a13e0 <.Lenc_prepretail>:
    (0x7a13e0#64,  0x4e284a41#32),   -- aese  v1.16b, v18.16b
    (0x7a13e4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a13e8#64,  0x4e2008c6#32),   -- rev64  v6.16b, v6.16b
    (0x7a13ec#64,  0x4e284a42#32),   -- aese  v2.16b, v18.16b
    (0x7a13f0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a13f4#64,  0x9e670143#32),   -- fmov  d3, x10
    (0x7a13f8#64,  0x4e284a40#32),   -- aese  v0.16b, v18.16b
    (0x7a13fc#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1400#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7a1404#64,  0x9eaf0123#32),   -- fmov  v3.d[1], x9
    (0x7a1408#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a140c#64,  0x4e284a62#32),   -- aese  v2.16b, v19.16b
    (0x7a1410#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1414#64,  0x4e284a60#32),   -- aese  v0.16b, v19.16b
    (0x7a1418#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a141c#64,  0x6e2b1c84#32),   -- eor  v4.16b, v4.16b, v11.16b
    (0x7a1420#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7a1424#64,  0x4e284a82#32),   -- aese  v2.16b, v20.16b
    (0x7a1428#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a142c#64,  0x4e284a43#32),   -- aese  v3.16b, v18.16b
    (0x7a1430#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1434#64,  0x5e18062a#32),   -- mov  d10, v17.d[1]
    (0x7a1438#64,  0x4e284a61#32),   -- aese  v1.16b, v19.16b
    (0x7a143c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1440#64,  0x0eefe08b#32),   -- pmull  v11.1q, v4.1d, v15.1d
    (0x7a1444#64,  0x5e180488#32),   -- mov  d8, v4.d[1]
    (0x7a1448#64,  0x4eefe089#32),   -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7a144c#64,  0x4e284aa2#32),   -- aese  v2.16b, v21.16b
    (0x7a1450#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1454#64,  0x4e284a81#32),   -- aese  v1.16b, v20.16b
    (0x7a1458#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a145c#64,  0x2e241d08#32),   -- eor  v8.8b, v8.8b, v4.8b
    (0x7a1460#64,  0x4e284a80#32),   -- aese  v0.16b, v20.16b
    (0x7a1464#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1468#64,  0x4e284a63#32),   -- aese  v3.16b, v19.16b
    (0x7a146c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1470#64,  0x4e284aa1#32),   -- aese  v1.16b, v21.16b
    (0x7a1474#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1478#64,  0x0eeae10a#32),   -- pmull  v10.1q, v8.1d, v10.1d
    (0x7a147c#64,  0x4eeee0a4#32),   -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7a1480#64,  0x0eeee0a8#32),   -- pmull  v8.1q, v5.1d, v14.1d
    (0x7a1484#64,  0x4e284a83#32),   -- aese  v3.16b, v20.16b
    (0x7a1488#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a148c#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a1490#64,  0x5e1804a4#32),   -- mov  d4, v5.d[1]
    (0x7a1494#64,  0x4e284aa0#32),   -- aese  v0.16b, v21.16b
    (0x7a1498#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a149c#64,  0x6e281d6b#32),   -- eor  v11.16b, v11.16b, v8.16b
    (0x7a14a0#64,  0x4e284aa3#32),   -- aese  v3.16b, v21.16b
    (0x7a14a4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a14a8#64,  0x2e251c84#32),   -- eor  v4.8b, v4.8b, v5.8b
    (0x7a14ac#64,  0x5e1804c8#32),   -- mov  d8, v6.d[1]
    (0x7a14b0#64,  0x4e284ac0#32),   -- aese  v0.16b, v22.16b
    (0x7a14b4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a14b8#64,  0x4e2008e7#32),   -- rev64  v7.16b, v7.16b
    (0x7a14bc#64,  0x4e284ac3#32),   -- aese  v3.16b, v22.16b
    (0x7a14c0#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a14c4#64,  0x0ef1e084#32),   -- pmull  v4.1q, v4.1d, v17.1d
    (0x7a14c8#64,  0x2e261d08#32),   -- eor  v8.8b, v8.8b, v6.8b
    (0x7a14cc#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a14d0#64,  0x0eede0c5#32),   -- pmull  v5.1q, v6.1d, v13.1d
    (0x7a14d4#64,  0x4e284ae3#32),   -- aese  v3.16b, v23.16b
    (0x7a14d8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a14dc#64,  0x4e284ac2#32),   -- aese  v2.16b, v22.16b
    (0x7a14e0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a14e4#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a14e8#64,  0x4eede0c4#32),   -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7a14ec#64,  0x6e251d6b#32),   -- eor  v11.16b, v11.16b, v5.16b
    (0x7a14f0#64,  0x6e180508#32),   -- mov  v8.d[1], v8.d[0]
    (0x7a14f4#64,  0x4e284ae2#32),   -- aese  v2.16b, v23.16b
    (0x7a14f8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a14fc#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a1500#64,  0x5e1804e4#32),   -- mov  d4, v7.d[1]
    (0x7a1504#64,  0x4e284ac1#32),   -- aese  v1.16b, v22.16b
    (0x7a1508#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a150c#64,  0x4ef0e108#32),   -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7a1510#64,  0x2e271c84#32),   -- eor  v4.8b, v4.8b, v7.8b
    (0x7a1514#64,  0x4eece0e5#32),   -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7a1518#64,  0x4e284ae1#32),   -- aese  v1.16b, v23.16b
    (0x7a151c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1520#64,  0x0ef0e084#32),   -- pmull  v4.1q, v4.1d, v16.1d
    (0x7a1524#64,  0x6e281d4a#32),   -- eor  v10.16b, v10.16b, v8.16b
    (0x7a1528#64,  0x4e284ae0#32),   -- aese  v0.16b, v23.16b
    (0x7a152c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1530#64,  0x4e284b01#32),   -- aese  v1.16b, v24.16b
    (0x7a1534#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1538#64,  0x4e284b02#32),   -- aese  v2.16b, v24.16b
    (0x7a153c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1540#64,  0x4e284b00#32),   -- aese  v0.16b, v24.16b
    (0x7a1544#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1548#64,  0x0f06e448#32),   -- movi  v8.8b, #0xc2
    (0x7a154c#64,  0x4e284b03#32),   -- aese  v3.16b, v24.16b
    (0x7a1550#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1554#64,  0x4e284b21#32),   -- aese  v1.16b, v25.16b
    (0x7a1558#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a155c#64,  0x6e251d29#32),   -- eor  v9.16b, v9.16b, v5.16b
    (0x7a1560#64,  0x4e284b20#32),   -- aese  v0.16b, v25.16b
    (0x7a1564#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1568#64,  0x4e284b23#32),   -- aese  v3.16b, v25.16b
    (0x7a156c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1570#64,  0x5f785508#32),   -- shl  d8, d8, #56
    (0x7a1574#64,  0x4e284b41#32),   -- aese  v1.16b, v26.16b
    (0x7a1578#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a157c#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a1580#64,  0x0eece0e6#32),   -- pmull  v6.1q, v7.1d, v12.1d
    (0x7a1584#64,  0x4e284b43#32),   -- aese  v3.16b, v26.16b
    (0x7a1588#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a158c#64,  0xf100323f#32),   -- cmp  x17, #0xc
    (0x7a1590#64,  0x4e284b40#32),   -- aese  v0.16b, v26.16b
    (0x7a1594#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1598#64,  0x6e261d6b#32),   -- eor  v11.16b, v11.16b, v6.16b
    (0x7a159c#64,  0x4e284b22#32),   -- aese  v2.16b, v25.16b
    (0x7a15a0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a15a4#64,  0x6e291d4a#32),   -- eor  v10.16b, v10.16b, v9.16b
    (0x7a15a8#64,  0x4e284b42#32),   -- aese  v2.16b, v26.16b
    (0x7a15ac#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a15b0#64,  0x0ee8e124#32),   -- pmull  v4.1q, v9.1d, v8.1d
    (0x7a15b4#64,  0x6e094129#32),   -- ext  v9.16b, v9.16b, v9.16b, #8
    (0x7a15b8#64,  0x6e2b1d4a#32),   -- eor  v10.16b, v10.16b, v11.16b
    (0x7a15bc#64,  0x5400044b#32),   -- b.lt  7a1644 <.Lenc_finish_prepretail>  // b.tstop
    (0x7a15c0#64,  0x4e284b61#32),   -- aese  v1.16b, v27.16b
    (0x7a15c4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a15c8#64,  0x4e284b63#32),   -- aese  v3.16b, v27.16b
    (0x7a15cc#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a15d0#64,  0x4e284b60#32),   -- aese  v0.16b, v27.16b
    (0x7a15d4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a15d8#64,  0x4e284b62#32),   -- aese  v2.16b, v27.16b
    (0x7a15dc#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a15e0#64,  0x4e284b83#32),   -- aese  v3.16b, v28.16b
    (0x7a15e4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a15e8#64,  0x4e284b81#32),   -- aese  v1.16b, v28.16b
    (0x7a15ec#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a15f0#64,  0x4e284b80#32),   -- aese  v0.16b, v28.16b
    (0x7a15f4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a15f8#64,  0x4e284b82#32),   -- aese  v2.16b, v28.16b
    (0x7a15fc#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1600#64,  0x54000220#32),   -- b.eq  7a1644 <.Lenc_finish_prepretail>  // b.none
    (0x7a1604#64,  0x4e284ba1#32),   -- aese  v1.16b, v29.16b
    (0x7a1608#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a160c#64,  0x4e284ba0#32),   -- aese  v0.16b, v29.16b
    (0x7a1610#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1614#64,  0x4e284ba3#32),   -- aese  v3.16b, v29.16b
    (0x7a1618#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a161c#64,  0x4e284ba2#32),   -- aese  v2.16b, v29.16b
    (0x7a1620#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1624#64,  0x4e284bc1#32),   -- aese  v1.16b, v30.16b
    (0x7a1628#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a162c#64,  0x4e284bc0#32),   -- aese  v0.16b, v30.16b
    (0x7a1630#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1634#64,  0x4e284bc3#32),   -- aese  v3.16b, v30.16b
    (0x7a1638#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a163c#64,  0x4e284bc2#32),   -- aese  v2.16b, v30.16b
    (0x7a1640#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b

    -- 00000000007a1644 <.Lenc_finish_prepretail>:
    (0x7a1644#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a1648#64,  0x6e291d4a#32),   -- eor  v10.16b, v10.16b, v9.16b
    (0x7a164c#64,  0x0ee8e144#32),   -- pmull  v4.1q, v10.1d, v8.1d
    (0x7a1650#64,  0x6e0a414a#32),   -- ext  v10.16b, v10.16b, v10.16b, #8
    (0x7a1654#64,  0x4e284be1#32),   -- aese  v1.16b, v31.16b
    (0x7a1658#64,  0x6e241d6b#32),   -- eor  v11.16b, v11.16b, v4.16b
    (0x7a165c#64,  0x4e284be3#32),   -- aese  v3.16b, v31.16b
    (0x7a1660#64,  0x4e284be0#32),   -- aese  v0.16b, v31.16b
    (0x7a1664#64,  0x4e284be2#32),   -- aese  v2.16b, v31.16b
    (0x7a1668#64,  0x6e2a1d6b#32),   -- eor  v11.16b, v11.16b, v10.16b

    -- 00000000007a166c <.Lenc_tail>:
    (0x7a166c#64,  0x6e0b4168#32),   -- ext  v8.16b, v11.16b, v11.16b, #8
    (0x7a1670#64,  0xcb000085#32),   -- sub  x5, x4, x0
    (0x7a1674#64,  0xa8c11c06#32),   -- ldp  x6, x7, [x0], #16
    (0x7a1678#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a167c#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a1680#64,  0xf100c0bf#32),   -- cmp  x5, #0x30
    (0x7a1684#64,  0x9e6700c4#32),   -- fmov  d4, x6
    (0x7a1688#64,  0x9eaf00e4#32),   -- fmov  v4.d[1], x7
    (0x7a168c#64,  0x6e201c85#32),   -- eor  v5.16b, v4.16b, v0.16b
    (0x7a1690#64,  0x540001ec#32),   -- b.gt  7a16cc <.Lenc_blocks_more_than_3>
    (0x7a1694#64,  0xf10080bf#32),   -- cmp  x5, #0x20
    (0x7a1698#64,  0x4ea21c43#32),   -- mov  v3.16b, v2.16b
    (0x7a169c#64,  0x0f00e40b#32),   -- movi  v11.8b, #0x0
    (0x7a16a0#64,  0x0f00e409#32),   -- movi  v9.8b, #0x0
    (0x7a16a4#64,  0x5100058c#32),   -- sub  w12, w12, #0x1
    (0x7a16a8#64,  0x4ea11c22#32),   -- mov  v2.16b, v1.16b
    (0x7a16ac#64,  0x0f00e40a#32),   -- movi  v10.8b, #0x0
    (0x7a16b0#64,  0x540002ec#32),   -- b.gt  7a170c <.Lenc_blocks_more_than_2>
    (0x7a16b4#64,  0x4ea11c23#32),   -- mov  v3.16b, v1.16b
    (0x7a16b8#64,  0x5100058c#32),   -- sub  w12, w12, #0x1
    (0x7a16bc#64,  0xf10040bf#32),   -- cmp  x5, #0x10
    (0x7a16c0#64,  0x540004ac#32),   -- b.gt  7a1754 <.Lenc_blocks_more_than_1>
    (0x7a16c4#64,  0x5100058c#32),   -- sub  w12, w12, #0x1
    (0x7a16c8#64,  0x14000036#32),   -- b  7a17a0 <.Lenc_blocks_less_than_1>

    -- 00000000007a16cc <.Lenc_blocks_more_than_3>:
    (0x7a16cc#64,  0x4c9f7045#32),   -- st1  {v5.16b}, [x2], #16
    (0x7a16d0#64,  0xa8c11c06#32),   -- ldp  x6, x7, [x0], #16
    (0x7a16d4#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a16d8#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a16dc#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a16e0#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a16e4#64,  0x5e180496#32),   -- mov  d22, v4.d[1]
    (0x7a16e8#64,  0x9e6700c5#32),   -- fmov  d5, x6
    (0x7a16ec#64,  0x9eaf00e5#32),   -- fmov  v5.d[1], x7
    (0x7a16f0#64,  0x2e241ed6#32),   -- eor  v22.8b, v22.8b, v4.8b
    (0x7a16f4#64,  0x0f00e408#32),   -- movi  v8.8b, #0x0
    (0x7a16f8#64,  0x5e18062a#32),   -- mov  d10, v17.d[1]
    (0x7a16fc#64,  0x0eefe08b#32),   -- pmull  v11.1q, v4.1d, v15.1d
    (0x7a1700#64,  0x4eefe089#32),   -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7a1704#64,  0x0eeae2ca#32),   -- pmull  v10.1q, v22.1d, v10.1d
    (0x7a1708#64,  0x6e211ca5#32),   -- eor  v5.16b, v5.16b, v1.16b

    -- 00000000007a170c <.Lenc_blocks_more_than_2>:
    (0x7a170c#64,  0x4c9f7045#32),   -- st1  {v5.16b}, [x2], #16
    (0x7a1710#64,  0xa8c11c06#32),   -- ldp  x6, x7, [x0], #16
    (0x7a1714#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a1718#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a171c#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a1720#64,  0x9e6700c5#32),   -- fmov  d5, x6
    (0x7a1724#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a1728#64,  0x9eaf00e5#32),   -- fmov  v5.d[1], x7
    (0x7a172c#64,  0x0f00e408#32),   -- movi  v8.8b, #0x0
    (0x7a1730#64,  0x4eeee094#32),   -- pmull2  v20.1q, v4.2d, v14.2d
    (0x7a1734#64,  0x5e180496#32),   -- mov  d22, v4.d[1]
    (0x7a1738#64,  0x0eeee095#32),   -- pmull  v21.1q, v4.1d, v14.1d
    (0x7a173c#64,  0x2e241ed6#32),   -- eor  v22.8b, v22.8b, v4.8b
    (0x7a1740#64,  0x6e221ca5#32),   -- eor  v5.16b, v5.16b, v2.16b
    (0x7a1744#64,  0x6e341d29#32),   -- eor  v9.16b, v9.16b, v20.16b
    (0x7a1748#64,  0x0ef1e2d6#32),   -- pmull  v22.1q, v22.1d, v17.1d
    (0x7a174c#64,  0x6e351d6b#32),   -- eor  v11.16b, v11.16b, v21.16b
    (0x7a1750#64,  0x6e361d4a#32),   -- eor  v10.16b, v10.16b, v22.16b

    -- 00000000007a1754 <.Lenc_blocks_more_than_1>:
    (0x7a1754#64,  0x4c9f7045#32),   -- st1  {v5.16b}, [x2], #16
    (0x7a1758#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a175c#64,  0xa8c11c06#32),   -- ldp  x6, x7, [x0], #16
    (0x7a1760#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a1764#64,  0x0f00e408#32),   -- movi  v8.8b, #0x0
    (0x7a1768#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a176c#64,  0x5e180496#32),   -- mov  d22, v4.d[1]
    (0x7a1770#64,  0x4eede094#32),   -- pmull2  v20.1q, v4.2d, v13.2d
    (0x7a1774#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a1778#64,  0x2e241ed6#32),   -- eor  v22.8b, v22.8b, v4.8b
    (0x7a177c#64,  0x6e341d29#32),   -- eor  v9.16b, v9.16b, v20.16b
    (0x7a1780#64,  0x6e1806d6#32),   -- mov  v22.d[1], v22.d[0]
    (0x7a1784#64,  0x9e6700c5#32),   -- fmov  d5, x6
    (0x7a1788#64,  0x9eaf00e5#32),   -- fmov  v5.d[1], x7
    (0x7a178c#64,  0x4ef0e2d6#32),   -- pmull2  v22.1q, v22.2d, v16.2d
    (0x7a1790#64,  0x0eede095#32),   -- pmull  v21.1q, v4.1d, v13.1d
    (0x7a1794#64,  0x6e231ca5#32),   -- eor  v5.16b, v5.16b, v3.16b
    (0x7a1798#64,  0x6e361d4a#32),   -- eor  v10.16b, v10.16b, v22.16b
    (0x7a179c#64,  0x6e351d6b#32),   -- eor  v11.16b, v11.16b, v21.16b

    -- 00000000007a17a0 <.Lenc_blocks_less_than_1>:
    (0x7a17a0#64,  0x92401821#32),   -- and  x1, x1, #0x7f
    (0x7a17a4#64,  0xaa3f03ed#32),   -- mvn  x13, xzr
    (0x7a17a8#64,  0xd1020021#32),   -- sub  x1, x1, #0x80
    (0x7a17ac#64,  0xcb0103e1#32),   -- neg  x1, x1
    (0x7a17b0#64,  0x4c407052#32),   -- ld1  {v18.16b}, [x2]
    (0x7a17b4#64,  0xaa3f03ee#32),   -- mvn  x14, xzr
    (0x7a17b8#64,  0x92401821#32),   -- and  x1, x1, #0x7f
    (0x7a17bc#64,  0x9ac125ce#32),   -- lsr  x14, x14, x1
    (0x7a17c0#64,  0xf101003f#32),   -- cmp  x1, #0x40
    (0x7a17c4#64,  0x9a8eb1a6#32),   -- csel  x6, x13, x14, lt  // lt = tstop
    (0x7a17c8#64,  0x9a9fb1c7#32),   -- csel  x7, x14, xzr, lt  // lt = tstop
    (0x7a17cc#64,  0x9e6700c0#32),   -- fmov  d0, x6
    (0x7a17d0#64,  0x9eaf00e0#32),   -- fmov  v0.d[1], x7
    (0x7a17d4#64,  0x4e201ca5#32),   -- and  v5.16b, v5.16b, v0.16b
    (0x7a17d8#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a17dc#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a17e0#64,  0x6ee01e45#32),   -- bif  v5.16b, v18.16b, v0.16b
    (0x7a17e4#64,  0x4eece094#32),   -- pmull2  v20.1q, v4.2d, v12.2d
    (0x7a17e8#64,  0x5e180488#32),   -- mov  d8, v4.d[1]
    (0x7a17ec#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a17f0#64,  0x0eece095#32),   -- pmull  v21.1q, v4.1d, v12.1d
    (0x7a17f4#64,  0x6e341d29#32),   -- eor  v9.16b, v9.16b, v20.16b
    (0x7a17f8#64,  0x2e241d08#32),   -- eor  v8.8b, v8.8b, v4.8b
    (0x7a17fc#64,  0x0ef0e108#32),   -- pmull  v8.1q, v8.1d, v16.1d
    (0x7a1800#64,  0x6e351d6b#32),   -- eor  v11.16b, v11.16b, v21.16b
    (0x7a1804#64,  0x6e281d4a#32),   -- eor  v10.16b, v10.16b, v8.16b
    (0x7a1808#64,  0x0f06e448#32),   -- movi  v8.8b, #0xc2
    (0x7a180c#64,  0x6e291d64#32),   -- eor  v4.16b, v11.16b, v9.16b
    (0x7a1810#64,  0x5f785508#32),   -- shl  d8, d8, #56
    (0x7a1814#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a1818#64,  0x0ee8e127#32),   -- pmull  v7.1q, v9.1d, v8.1d
    (0x7a181c#64,  0x6e094129#32),   -- ext  v9.16b, v9.16b, v9.16b, #8
    (0x7a1820#64,  0x6e271d4a#32),   -- eor  v10.16b, v10.16b, v7.16b
    (0x7a1824#64,  0x6e291d4a#32),   -- eor  v10.16b, v10.16b, v9.16b
    (0x7a1828#64,  0x0ee8e149#32),   -- pmull  v9.1q, v10.1d, v8.1d
    (0x7a182c#64,  0x6e0a414a#32),   -- ext  v10.16b, v10.16b, v10.16b, #8
    (0x7a1830#64,  0xb9000e09#32),   -- str  w9, [x16, #12]
    (0x7a1834#64,  0x4c007045#32),   -- st1  {v5.16b}, [x2]
    (0x7a1838#64,  0x6e291d6b#32),   -- eor  v11.16b, v11.16b, v9.16b
    (0x7a183c#64,  0x6e2a1d6b#32),   -- eor  v11.16b, v11.16b, v10.16b
    (0x7a1840#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a1844#64,  0x4e20096b#32),   -- rev64  v11.16b, v11.16b
    (0x7a1848#64,  0xaa0f03e0#32),   -- mov  x0, x15
    (0x7a184c#64,  0x4c00706b#32),   -- st1  {v11.16b}, [x3]
    (0x7a1850#64,  0xa94153f3#32),   -- ldp  x19, x20, [sp, #16]
    (0x7a1854#64,  0xa9425bf5#32),   -- ldp  x21, x22, [sp, #32]
    (0x7a1858#64,  0xa94363f7#32),   -- ldp  x23, x24, [sp, #48]
    (0x7a185c#64,  0x6d4427e8#32),   -- ldp  d8, d9, [sp, #64]
    (0x7a1860#64,  0x6d452fea#32),   -- ldp  d10, d11, [sp, #80]
    (0x7a1864#64,  0x6d4637ec#32),   -- ldp  d12, d13, [sp, #96]
    (0x7a1868#64,  0x6d473fee#32),   -- ldp  d14, d15, [sp, #112]
    (0x7a186c#64,  0xa8c87bfd#32),   -- ldp  x29, x30, [sp], #128
    (0x7a1870#64,  0xd65f03c0#32),   -- ret
  ]

end AESGCMEncKernelProgram
