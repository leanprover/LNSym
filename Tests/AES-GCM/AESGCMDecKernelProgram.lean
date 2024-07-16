/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec

namespace AESGCMDecKernelProgram

open BitVec

/-

  void aes_gcm_dec_kernel(const uint8_t *in, uint64_t in_bits, void *out,
                          void *Xi, uint8_t *ivec, const AES_KEY *key,
                          const u128 Htable[16]);

  input: in -- input ciphertext (x0)
         in_bits -- input ciphertext length in bits (x1)
         Xi -- current hash/tag value, should match with input to aes_gcm_enc_kernel (x3)
         ivec -- counter, should match with input to aes_gcm_enc_kernel (x4)
         key -- AES key schedule and rounds (x5)
         Htable -- powers of H precomputed up to H^12 (x6)
  output: out -- plaintext (x2)
          Xi -- current hash/tag value, decryption function will recalculate
                the hash based on the ciphertext, the top-level c function
                CRYPTO_gcm128_finish will compare the recalculated hash with
                hash produced from encryption (x3)

-/

def aes_gcm_dec_kernel_program : Program :=
  def_program
  [ -- 00000000007a1880 <aes_gcm_dec_kernel>:
    (0x7a1880#64,  0xa9b87bfd#32),   -- stp  x29, x30, [sp, #-128]!
    (0x7a1884#64,  0x910003fd#32),   -- mov  x29, sp
    (0x7a1888#64,  0xa90153f3#32),   -- stp  x19, x20, [sp, #16]
    (0x7a188c#64,  0xaa0403f0#32),   -- mov  x16, x4
    (0x7a1890#64,  0xaa0503e8#32),   -- mov  x8, x5
    (0x7a1894#64,  0xa9025bf5#32),   -- stp  x21, x22, [sp, #32]
    (0x7a1898#64,  0xa90363f7#32),   -- stp  x23, x24, [sp, #48]
    (0x7a189c#64,  0x6d0427e8#32),   -- stp  d8, d9, [sp, #64]
    (0x7a18a0#64,  0x6d052fea#32),   -- stp  d10, d11, [sp, #80]
    (0x7a18a4#64,  0x6d0637ec#32),   -- stp  d12, d13, [sp, #96]
    (0x7a18a8#64,  0x6d073fee#32),   -- stp  d14, d15, [sp, #112]
    (0x7a18ac#64,  0xb940f111#32),   -- ldr  w17, [x8, #240]
    (0x7a18b0#64,  0x8b111113#32),   -- add  x19, x8, x17, lsl #4
    (0x7a18b4#64,  0xa9403a6d#32),   -- ldp  x13, x14, [x19]
    (0x7a18b8#64,  0x3cdf027f#32),   -- ldur  q31, [x19, #-16]
    (0x7a18bc#64,  0xd343fc25#32),   -- lsr  x5, x1, #3
    (0x7a18c0#64,  0xaa0503ef#32),   -- mov  x15, x5
    (0x7a18c4#64,  0xa9402e0a#32),   -- ldp  x10, x11, [x16]
    (0x7a18c8#64,  0x3dc0211a#32),   -- ldr  q26, [x8, #128]
    (0x7a18cc#64,  0xd10004a5#32),   -- sub  x5, x5, #0x1
    (0x7a18d0#64,  0x3dc01d19#32),   -- ldr  q25, [x8, #112]
    (0x7a18d4#64,  0x927ae4a5#32),   -- and  x5, x5, #0xffffffffffffffc0
    (0x7a18d8#64,  0x8b410c04#32),   -- add  x4, x0, x1, lsr #3
    (0x7a18dc#64,  0x3dc01918#32),   -- ldr  q24, [x8, #96]
    (0x7a18e0#64,  0xd360fd6c#32),   -- lsr  x12, x11, #32
    (0x7a18e4#64,  0x3dc01517#32),   -- ldr  q23, [x8, #80]
    (0x7a18e8#64,  0x2a0b016b#32),   -- orr  w11, w11, w11
    (0x7a18ec#64,  0x3dc00d15#32),   -- ldr  q21, [x8, #48]
    (0x7a18f0#64,  0x8b0000a5#32),   -- add  x5, x5, x0
    (0x7a18f4#64,  0x5ac0098c#32),   -- rev  w12, w12
    (0x7a18f8#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a18fc#64,  0x9e670143#32),   -- fmov  d3, x10
    (0x7a1900#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1904#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1908#64,  0x9e670141#32),   -- fmov  d1, x10
    (0x7a190c#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1910#64,  0x4c407200#32),   -- ld1  {v0.16b}, [x16]
    (0x7a1914#64,  0x9eaf0121#32),   -- fmov  v1.d[1], x9
    (0x7a1918#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a191c#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1920#64,  0x9e670142#32),   -- fmov  d2, x10
    (0x7a1924#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1928#64,  0x9eaf0122#32),   -- fmov  v2.d[1], x9
    (0x7a192c#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1930#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1934#64,  0x3dc00112#32),   -- ldr  q18, [x8]
    (0x7a1938#64,  0x9eaf0123#32),   -- fmov  v3.d[1], x9
    (0x7a193c#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1940#64,  0x3dc01116#32),   -- ldr  q22, [x8, #64]
    (0x7a1944#64,  0x3dc00513#32),   -- ldr  q19, [x8, #16]
    (0x7a1948#64,  0x4e284a40#32),   -- aese  v0.16b, v18.16b
    (0x7a194c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1950#64,  0x3dc00cce#32),   -- ldr  q14, [x6, #48]
    (0x7a1954#64,  0x6e0e41ce#32),   -- ext  v14.16b, v14.16b, v14.16b, #8
    (0x7a1958#64,  0x4e284a43#32),   -- aese  v3.16b, v18.16b
    (0x7a195c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1960#64,  0x3dc014cf#32),   -- ldr  q15, [x6, #80]
    (0x7a1964#64,  0x6e0f41ef#32),   -- ext  v15.16b, v15.16b, v15.16b, #8
    (0x7a1968#64,  0x4e284a41#32),   -- aese  v1.16b, v18.16b
    (0x7a196c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1970#64,  0x3dc008cd#32),   -- ldr  q13, [x6, #32]
    (0x7a1974#64,  0x6e0d41ad#32),   -- ext  v13.16b, v13.16b, v13.16b, #8
    (0x7a1978#64,  0x4e284a42#32),   -- aese  v2.16b, v18.16b
    (0x7a197c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1980#64,  0x3dc00914#32),   -- ldr  q20, [x8, #32]
    (0x7a1984#64,  0x4e284a60#32),   -- aese  v0.16b, v19.16b
    (0x7a1988#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a198c#64,  0x4e284a61#32),   -- aese  v1.16b, v19.16b
    (0x7a1990#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1994#64,  0x4c40706b#32),   -- ld1  {v11.16b}, [x3]
    (0x7a1998#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a199c#64,  0x4e20096b#32),   -- rev64  v11.16b, v11.16b
    (0x7a19a0#64,  0x4e284a62#32),   -- aese  v2.16b, v19.16b
    (0x7a19a4#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a19a8#64,  0x3dc0251b#32),   -- ldr  q27, [x8, #144]
    (0x7a19ac#64,  0x4e284a63#32),   -- aese  v3.16b, v19.16b
    (0x7a19b0#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a19b4#64,  0x3dc0311e#32),   -- ldr  q30, [x8, #192]
    (0x7a19b8#64,  0x4e284a80#32),   -- aese  v0.16b, v20.16b
    (0x7a19bc#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a19c0#64,  0x3dc000cc#32),   -- ldr  q12, [x6]
    (0x7a19c4#64,  0x6e0c418c#32),   -- ext  v12.16b, v12.16b, v12.16b, #8
    (0x7a19c8#64,  0x4e284a82#32),   -- aese  v2.16b, v20.16b
    (0x7a19cc#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a19d0#64,  0x3dc0291c#32),   -- ldr  q28, [x8, #160]
    (0x7a19d4#64,  0x4e284a83#32),   -- aese  v3.16b, v20.16b
    (0x7a19d8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a19dc#64,  0x4e284aa0#32),   -- aese  v0.16b, v21.16b
    (0x7a19e0#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a19e4#64,  0x4e284a81#32),   -- aese  v1.16b, v20.16b
    (0x7a19e8#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a19ec#64,  0x4e284aa3#32),   -- aese  v3.16b, v21.16b
    (0x7a19f0#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a19f4#64,  0x4e284ac0#32),   -- aese  v0.16b, v22.16b
    (0x7a19f8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a19fc#64,  0x4e284aa2#32),   -- aese  v2.16b, v21.16b
    (0x7a1a00#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1a04#64,  0x4e284aa1#32),   -- aese  v1.16b, v21.16b
    (0x7a1a08#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1a0c#64,  0x4e284ac3#32),   -- aese  v3.16b, v22.16b
    (0x7a1a10#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1a14#64,  0x4e284ac2#32),   -- aese  v2.16b, v22.16b
    (0x7a1a18#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1a1c#64,  0x4e284ac1#32),   -- aese  v1.16b, v22.16b
    (0x7a1a20#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1a24#64,  0x4e284ae3#32),   -- aese  v3.16b, v23.16b
    (0x7a1a28#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1a2c#64,  0x4e284ae0#32),   -- aese  v0.16b, v23.16b
    (0x7a1a30#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1a34#64,  0x4e284ae1#32),   -- aese  v1.16b, v23.16b
    (0x7a1a38#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1a3c#64,  0x4e284ae2#32),   -- aese  v2.16b, v23.16b
    (0x7a1a40#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1a44#64,  0x4e284b00#32),   -- aese  v0.16b, v24.16b
    (0x7a1a48#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1a4c#64,  0x4e284b03#32),   -- aese  v3.16b, v24.16b
    (0x7a1a50#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1a54#64,  0xf100323f#32),   -- cmp  x17, #0xc
    (0x7a1a58#64,  0x4e284b01#32),   -- aese  v1.16b, v24.16b
    (0x7a1a5c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1a60#64,  0x4e284b02#32),   -- aese  v2.16b, v24.16b
    (0x7a1a64#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1a68#64,  0x4e284b20#32),   -- aese  v0.16b, v25.16b
    (0x7a1a6c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1a70#64,  0x4e284b21#32),   -- aese  v1.16b, v25.16b
    (0x7a1a74#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1a78#64,  0x4e284b23#32),   -- aese  v3.16b, v25.16b
    (0x7a1a7c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1a80#64,  0x4e284b40#32),   -- aese  v0.16b, v26.16b
    (0x7a1a84#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1a88#64,  0x4e284b22#32),   -- aese  v2.16b, v25.16b
    (0x7a1a8c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1a90#64,  0x4e284b43#32),   -- aese  v3.16b, v26.16b
    (0x7a1a94#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1a98#64,  0x4e284b41#32),   -- aese  v1.16b, v26.16b
    (0x7a1a9c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1aa0#64,  0x3dc02d1d#32),   -- ldr  q29, [x8, #176]
    (0x7a1aa4#64,  0x4e284b42#32),   -- aese  v2.16b, v26.16b
    (0x7a1aa8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1aac#64,  0x5400044b#32),   -- b.lt  7a1b34 <.Ldec_finish_first_blocks>  // b.tstop
    (0x7a1ab0#64,  0x4e284b60#32),   -- aese  v0.16b, v27.16b
    (0x7a1ab4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1ab8#64,  0x4e284b61#32),   -- aese  v1.16b, v27.16b
    (0x7a1abc#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1ac0#64,  0x4e284b63#32),   -- aese  v3.16b, v27.16b
    (0x7a1ac4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1ac8#64,  0x4e284b62#32),   -- aese  v2.16b, v27.16b
    (0x7a1acc#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1ad0#64,  0x4e284b80#32),   -- aese  v0.16b, v28.16b
    (0x7a1ad4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1ad8#64,  0x4e284b81#32),   -- aese  v1.16b, v28.16b
    (0x7a1adc#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1ae0#64,  0x4e284b83#32),   -- aese  v3.16b, v28.16b
    (0x7a1ae4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1ae8#64,  0x4e284b82#32),   -- aese  v2.16b, v28.16b
    (0x7a1aec#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1af0#64,  0x54000220#32),   -- b.eq  7a1b34 <.Ldec_finish_first_blocks>  // b.none
    (0x7a1af4#64,  0x4e284ba0#32),   -- aese  v0.16b, v29.16b
    (0x7a1af8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1afc#64,  0x4e284ba3#32),   -- aese  v3.16b, v29.16b
    (0x7a1b00#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1b04#64,  0x4e284ba1#32),   -- aese  v1.16b, v29.16b
    (0x7a1b08#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1b0c#64,  0x4e284ba2#32),   -- aese  v2.16b, v29.16b
    (0x7a1b10#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1b14#64,  0x4e284bc1#32),   -- aese  v1.16b, v30.16b
    (0x7a1b18#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1b1c#64,  0x4e284bc0#32),   -- aese  v0.16b, v30.16b
    (0x7a1b20#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1b24#64,  0x4e284bc2#32),   -- aese  v2.16b, v30.16b
    (0x7a1b28#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1b2c#64,  0x4e284bc3#32),   -- aese  v3.16b, v30.16b
    (0x7a1b30#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b

    -- 00000000007a1b34 <.Ldec_finish_first_blocks>:
    (0x7a1b34#64,  0xeb05001f#32),   -- cmp  x0, x5
    (0x7a1b38#64,  0x4ecf29c9#32),   -- trn1  v9.2d, v14.2d, v15.2d
    (0x7a1b3c#64,  0x4ecf69d1#32),   -- trn2  v17.2d, v14.2d, v15.2d
    (0x7a1b40#64,  0x4ecd2988#32),   -- trn1  v8.2d, v12.2d, v13.2d
    (0x7a1b44#64,  0x4ecd6990#32),   -- trn2  v16.2d, v12.2d, v13.2d
    (0x7a1b48#64,  0x6e291e31#32),   -- eor  v17.16b, v17.16b, v9.16b
    (0x7a1b4c#64,  0x4e284be1#32),   -- aese  v1.16b, v31.16b
    (0x7a1b50#64,  0x4e284be2#32),   -- aese  v2.16b, v31.16b
    (0x7a1b54#64,  0x6e281e10#32),   -- eor  v16.16b, v16.16b, v8.16b
    (0x7a1b58#64,  0x4e284be3#32),   -- aese  v3.16b, v31.16b
    (0x7a1b5c#64,  0x4e284be0#32),   -- aese  v0.16b, v31.16b
    (0x7a1b60#64,  0x540034ea#32),   -- b.ge  7a21fc <.Ldec_tail>  // b.tcont
    (0x7a1b64#64,  0x3dc00004#32),   -- ldr  q4, [x0]
    (0x7a1b68#64,  0x3dc00405#32),   -- ldr  q5, [x0, #16]
    (0x7a1b6c#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1b70#64,  0x6e201c80#32),   -- eor  v0.16b, v4.16b, v0.16b
    (0x7a1b74#64,  0x6e211ca1#32),   -- eor  v1.16b, v5.16b, v1.16b
    (0x7a1b78#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7a1b7c#64,  0x3dc00c07#32),   -- ldr  q7, [x0, #48]
    (0x7a1b80#64,  0x4e183c07#32),   -- mov  x7, v0.d[1]
    (0x7a1b84#64,  0x4e083c06#32),   -- mov  x6, v0.d[0]
    (0x7a1b88#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7a1b8c#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1b90#64,  0x9e670140#32),   -- fmov  d0, x10
    (0x7a1b94#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1b98#64,  0x9eaf0120#32),   -- fmov  v0.d[1], x9
    (0x7a1b9c#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1ba0#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1ba4#64,  0x4e083c33#32),   -- mov  x19, v1.d[0]
    (0x7a1ba8#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1bac#64,  0x4e183c34#32),   -- mov  x20, v1.d[1]
    (0x7a1bb0#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a1bb4#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a1bb8#64,  0xa8811c46#32),   -- stp  x6, x7, [x2], #16
    (0x7a1bbc#64,  0x9e670141#32),   -- fmov  d1, x10
    (0x7a1bc0#64,  0x3dc00806#32),   -- ldr  q6, [x0, #32]
    (0x7a1bc4#64,  0x91010000#32),   -- add  x0, x0, #0x40
    (0x7a1bc8#64,  0x9eaf0121#32),   -- fmov  v1.d[1], x9
    (0x7a1bcc#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1bd0#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1bd4#64,  0xca0d0273#32),   -- eor  x19, x19, x13
    (0x7a1bd8#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1bdc#64,  0xca0e0294#32),   -- eor  x20, x20, x14
    (0x7a1be0#64,  0xa8815053#32),   -- stp  x19, x20, [x2], #16
    (0x7a1be4#64,  0x6e221cc2#32),   -- eor  v2.16b, v6.16b, v2.16b
    (0x7a1be8#64,  0xeb05001f#32),   -- cmp  x0, x5
    (0x7a1bec#64,  0x54001a8a#32),   -- b.ge  7a1f3c <.Ldec_prepretail>  // b.tcont

    -- 00000000007a1bf0 <.Ldec_main_loop>:
    (0x7a1bf0#64,  0x4e083c55#32),   -- mov  x21, v2.d[0]
    (0x7a1bf4#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a1bf8#64,  0x6e231ce3#32),   -- eor  v3.16b, v7.16b, v3.16b
    (0x7a1bfc#64,  0x4e284a40#32),   -- aese  v0.16b, v18.16b
    (0x7a1c00#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1c04#64,  0x4e183c56#32),   -- mov  x22, v2.d[1]
    (0x7a1c08#64,  0x4e284a41#32),   -- aese  v1.16b, v18.16b
    (0x7a1c0c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1c10#64,  0x9e670142#32),   -- fmov  d2, x10
    (0x7a1c14#64,  0x9eaf0122#32),   -- fmov  v2.d[1], x9
    (0x7a1c18#64,  0x6e2b1c84#32),   -- eor  v4.16b, v4.16b, v11.16b
    (0x7a1c1c#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1c20#64,  0x4e284a60#32),   -- aese  v0.16b, v19.16b
    (0x7a1c24#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1c28#64,  0x4e183c78#32),   -- mov  x24, v3.d[1]
    (0x7a1c2c#64,  0x4e284a61#32),   -- aese  v1.16b, v19.16b
    (0x7a1c30#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1c34#64,  0x4e083c77#32),   -- mov  x23, v3.d[0]
    (0x7a1c38#64,  0x4eefe089#32),   -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7a1c3c#64,  0x5e180488#32),   -- mov  d8, v4.d[1]
    (0x7a1c40#64,  0x9e670143#32),   -- fmov  d3, x10
    (0x7a1c44#64,  0x4e284a80#32),   -- aese  v0.16b, v20.16b
    (0x7a1c48#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1c4c#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1c50#64,  0x4e284a42#32),   -- aese  v2.16b, v18.16b
    (0x7a1c54#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1c58#64,  0x9eaf0123#32),   -- fmov  v3.d[1], x9
    (0x7a1c5c#64,  0x4e284a81#32),   -- aese  v1.16b, v20.16b
    (0x7a1c60#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1c64#64,  0x2e241d08#32),   -- eor  v8.8b, v8.8b, v4.8b
    (0x7a1c68#64,  0x4e284aa0#32),   -- aese  v0.16b, v21.16b
    (0x7a1c6c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1c70#64,  0xca0e02d6#32),   -- eor  x22, x22, x14
    (0x7a1c74#64,  0x4e284a62#32),   -- aese  v2.16b, v19.16b
    (0x7a1c78#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1c7c#64,  0x5e18062a#32),   -- mov  d10, v17.d[1]
    (0x7a1c80#64,  0x4e284aa1#32),   -- aese  v1.16b, v21.16b
    (0x7a1c84#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1c88#64,  0x4e2008c6#32),   -- rev64  v6.16b, v6.16b
    (0x7a1c8c#64,  0x4e284a43#32),   -- aese  v3.16b, v18.16b
    (0x7a1c90#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1c94#64,  0xca0d02b5#32),   -- eor  x21, x21, x13
    (0x7a1c98#64,  0x4e284a82#32),   -- aese  v2.16b, v20.16b
    (0x7a1c9c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1ca0#64,  0xa8815855#32),   -- stp  x21, x22, [x2], #16
    (0x7a1ca4#64,  0x0eefe08b#32),   -- pmull  v11.1q, v4.1d, v15.1d
    (0x7a1ca8#64,  0x4eeee0a4#32),   -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7a1cac#64,  0x4e284aa2#32),   -- aese  v2.16b, v21.16b
    (0x7a1cb0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1cb4#64,  0x4e2008e7#32),   -- rev64  v7.16b, v7.16b
    (0x7a1cb8#64,  0x0eeae10a#32),   -- pmull  v10.1q, v8.1d, v10.1d
    (0x7a1cbc#64,  0xca0d02f7#32),   -- eor  x23, x23, x13
    (0x7a1cc0#64,  0x0eeee0a8#32),   -- pmull  v8.1q, v5.1d, v14.1d
    (0x7a1cc4#64,  0xca0e0318#32),   -- eor  x24, x24, x14
    (0x7a1cc8#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a1ccc#64,  0x4e284ac2#32),   -- aese  v2.16b, v22.16b
    (0x7a1cd0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1cd4#64,  0x4e284a63#32),   -- aese  v3.16b, v19.16b
    (0x7a1cd8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1cdc#64,  0x5e1804a4#32),   -- mov  d4, v5.d[1]
    (0x7a1ce0#64,  0x4e284ac0#32),   -- aese  v0.16b, v22.16b
    (0x7a1ce4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1ce8#64,  0x6e281d6b#32),   -- eor  v11.16b, v11.16b, v8.16b
    (0x7a1cec#64,  0x4e284ae2#32),   -- aese  v2.16b, v23.16b
    (0x7a1cf0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1cf4#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1cf8#64,  0x4e284a83#32),   -- aese  v3.16b, v20.16b
    (0x7a1cfc#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1d00#64,  0x5e1804c8#32),   -- mov  d8, v6.d[1]
    (0x7a1d04#64,  0x4e284ac1#32),   -- aese  v1.16b, v22.16b
    (0x7a1d08#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1d0c#64,  0x2e251c84#32),   -- eor  v4.8b, v4.8b, v5.8b
    (0x7a1d10#64,  0x0eede0c5#32),   -- pmull  v5.1q, v6.1d, v13.1d
    (0x7a1d14#64,  0x4e284aa3#32),   -- aese  v3.16b, v21.16b
    (0x7a1d18#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1d1c#64,  0x2e261d08#32),   -- eor  v8.8b, v8.8b, v6.8b
    (0x7a1d20#64,  0x4e284ae1#32),   -- aese  v1.16b, v23.16b
    (0x7a1d24#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1d28#64,  0x4e284ae0#32),   -- aese  v0.16b, v23.16b
    (0x7a1d2c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1d30#64,  0x6e251d6b#32),   -- eor  v11.16b, v11.16b, v5.16b
    (0x7a1d34#64,  0x0ef1e084#32),   -- pmull  v4.1q, v4.1d, v17.1d
    (0x7a1d38#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1d3c#64,  0x4e284b01#32),   -- aese  v1.16b, v24.16b
    (0x7a1d40#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1d44#64,  0x6e180508#32),   -- mov  v8.d[1], v8.d[0]
    (0x7a1d48#64,  0x4e284b00#32),   -- aese  v0.16b, v24.16b
    (0x7a1d4c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1d50#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1d54#64,  0x4e284ac3#32),   -- aese  v3.16b, v22.16b
    (0x7a1d58#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1d5c#64,  0x4e284b21#32),   -- aese  v1.16b, v25.16b
    (0x7a1d60#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1d64#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a1d68#64,  0x4e284b20#32),   -- aese  v0.16b, v25.16b
    (0x7a1d6c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1d70#64,  0x4eede0c4#32),   -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7a1d74#64,  0x5e1804e6#32),   -- mov  d6, v7.d[1]
    (0x7a1d78#64,  0x4e284ae3#32),   -- aese  v3.16b, v23.16b
    (0x7a1d7c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1d80#64,  0x4ef0e108#32),   -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7a1d84#64,  0x4e284b40#32),   -- aese  v0.16b, v26.16b
    (0x7a1d88#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1d8c#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a1d90#64,  0x4e284b03#32),   -- aese  v3.16b, v24.16b
    (0x7a1d94#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1d98#64,  0x0eece0e4#32),   -- pmull  v4.1q, v7.1d, v12.1d
    (0x7a1d9c#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1da0#64,  0x6e281d4a#32),   -- eor  v10.16b, v10.16b, v8.16b
    (0x7a1da4#64,  0x4eece0e5#32),   -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7a1da8#64,  0xf100323f#32),   -- cmp  x17, #0xc
    (0x7a1dac#64,  0x2e271cc6#32),   -- eor  v6.8b, v6.8b, v7.8b
    (0x7a1db0#64,  0x4e284b41#32),   -- aese  v1.16b, v26.16b
    (0x7a1db4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1db8#64,  0x4e284b02#32),   -- aese  v2.16b, v24.16b
    (0x7a1dbc#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1dc0#64,  0x6e251d29#32),   -- eor  v9.16b, v9.16b, v5.16b
    (0x7a1dc4#64,  0x0ef0e0c6#32),   -- pmull  v6.1q, v6.1d, v16.1d
    (0x7a1dc8#64,  0x0f06e448#32),   -- movi  v8.8b, #0xc2
    (0x7a1dcc#64,  0x4e284b22#32),   -- aese  v2.16b, v25.16b
    (0x7a1dd0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1dd4#64,  0x6e241d6b#32),   -- eor  v11.16b, v11.16b, v4.16b
    (0x7a1dd8#64,  0x4e284b23#32),   -- aese  v3.16b, v25.16b
    (0x7a1ddc#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1de0#64,  0x5f785508#32),   -- shl  d8, d8, #56
    (0x7a1de4#64,  0x4e284b42#32),   -- aese  v2.16b, v26.16b
    (0x7a1de8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1dec#64,  0x6e261d4a#32),   -- eor  v10.16b, v10.16b, v6.16b
    (0x7a1df0#64,  0x4e284b43#32),   -- aese  v3.16b, v26.16b
    (0x7a1df4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1df8#64,  0x5400044b#32),   -- b.lt  7a1e80 <.Ldec_main_loop_continue>  // b.tstop
    (0x7a1dfc#64,  0x4e284b60#32),   -- aese  v0.16b, v27.16b
    (0x7a1e00#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1e04#64,  0x4e284b62#32),   -- aese  v2.16b, v27.16b
    (0x7a1e08#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1e0c#64,  0x4e284b61#32),   -- aese  v1.16b, v27.16b
    (0x7a1e10#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1e14#64,  0x4e284b63#32),   -- aese  v3.16b, v27.16b
    (0x7a1e18#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1e1c#64,  0x4e284b80#32),   -- aese  v0.16b, v28.16b
    (0x7a1e20#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1e24#64,  0x4e284b81#32),   -- aese  v1.16b, v28.16b
    (0x7a1e28#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1e2c#64,  0x4e284b82#32),   -- aese  v2.16b, v28.16b
    (0x7a1e30#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1e34#64,  0x4e284b83#32),   -- aese  v3.16b, v28.16b
    (0x7a1e38#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1e3c#64,  0x54000220#32),   -- b.eq  7a1e80 <.Ldec_main_loop_continue>  // b.none
    (0x7a1e40#64,  0x4e284ba0#32),   -- aese  v0.16b, v29.16b
    (0x7a1e44#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1e48#64,  0x4e284ba1#32),   -- aese  v1.16b, v29.16b
    (0x7a1e4c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1e50#64,  0x4e284ba2#32),   -- aese  v2.16b, v29.16b
    (0x7a1e54#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1e58#64,  0x4e284ba3#32),   -- aese  v3.16b, v29.16b
    (0x7a1e5c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1e60#64,  0x4e284bc0#32),   -- aese  v0.16b, v30.16b
    (0x7a1e64#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1e68#64,  0x4e284bc1#32),   -- aese  v1.16b, v30.16b
    (0x7a1e6c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1e70#64,  0x4e284bc2#32),   -- aese  v2.16b, v30.16b
    (0x7a1e74#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1e78#64,  0x4e284bc3#32),   -- aese  v3.16b, v30.16b
    (0x7a1e7c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b

    -- 00000000007a1e80 <.Ldec_main_loop_continue>:
    (0x7a1e80#64,  0x0ee8e127#32),   -- pmull  v7.1q, v9.1d, v8.1d
    (0x7a1e84#64,  0x6e291d66#32),   -- eor  v6.16b, v11.16b, v9.16b
    (0x7a1e88#64,  0x3dc00004#32),   -- ldr  q4, [x0]
    (0x7a1e8c#64,  0x4e284be0#32),   -- aese  v0.16b, v31.16b
    (0x7a1e90#64,  0x6e094129#32),   -- ext  v9.16b, v9.16b, v9.16b, #8
    (0x7a1e94#64,  0x6e261d4a#32),   -- eor  v10.16b, v10.16b, v6.16b
    (0x7a1e98#64,  0x3dc00405#32),   -- ldr  q5, [x0, #16]
    (0x7a1e9c#64,  0x6e201c80#32),   -- eor  v0.16b, v4.16b, v0.16b
    (0x7a1ea0#64,  0xa8816057#32),   -- stp  x23, x24, [x2], #16
    (0x7a1ea4#64,  0x6e271d4a#32),   -- eor  v10.16b, v10.16b, v7.16b
    (0x7a1ea8#64,  0x3dc00c07#32),   -- ldr  q7, [x0, #48]
    (0x7a1eac#64,  0x3dc00806#32),   -- ldr  q6, [x0, #32]
    (0x7a1eb0#64,  0x4e183c07#32),   -- mov  x7, v0.d[1]
    (0x7a1eb4#64,  0x6e291d4a#32),   -- eor  v10.16b, v10.16b, v9.16b
    (0x7a1eb8#64,  0x4e284be1#32),   -- aese  v1.16b, v31.16b
    (0x7a1ebc#64,  0x91010000#32),   -- add  x0, x0, #0x40
    (0x7a1ec0#64,  0x4e083c06#32),   -- mov  x6, v0.d[0]
    (0x7a1ec4#64,  0x9e670140#32),   -- fmov  d0, x10
    (0x7a1ec8#64,  0x9eaf0120#32),   -- fmov  v0.d[1], x9
    (0x7a1ecc#64,  0x0ee8e148#32),   -- pmull  v8.1q, v10.1d, v8.1d
    (0x7a1ed0#64,  0x6e211ca1#32),   -- eor  v1.16b, v5.16b, v1.16b
    (0x7a1ed4#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1ed8#64,  0x4e284be2#32),   -- aese  v2.16b, v31.16b
    (0x7a1edc#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1ee0#64,  0xeb05001f#32),   -- cmp  x0, x5
    (0x7a1ee4#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1ee8#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a1eec#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a1ef0#64,  0x4e183c34#32),   -- mov  x20, v1.d[1]
    (0x7a1ef4#64,  0x6e221cc2#32),   -- eor  v2.16b, v6.16b, v2.16b
    (0x7a1ef8#64,  0x6e281d6b#32),   -- eor  v11.16b, v11.16b, v8.16b
    (0x7a1efc#64,  0x4e083c33#32),   -- mov  x19, v1.d[0]
    (0x7a1f00#64,  0x9e670141#32),   -- fmov  d1, x10
    (0x7a1f04#64,  0x6e0a414a#32),   -- ext  v10.16b, v10.16b, v10.16b, #8
    (0x7a1f08#64,  0x9eaf0121#32),   -- fmov  v1.d[1], x9
    (0x7a1f0c#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1f10#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a1f14#64,  0x4e284be3#32),   -- aese  v3.16b, v31.16b
    (0x7a1f18#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1f1c#64,  0x4e2008a5#32),   -- rev64  v5.16b, v5.16b
    (0x7a1f20#64,  0xca0e0294#32),   -- eor  x20, x20, x14
    (0x7a1f24#64,  0xa8811c46#32),   -- stp  x6, x7, [x2], #16
    (0x7a1f28#64,  0xca0d0273#32),   -- eor  x19, x19, x13
    (0x7a1f2c#64,  0xa8815053#32),   -- stp  x19, x20, [x2], #16
    (0x7a1f30#64,  0x4e200884#32),   -- rev64  v4.16b, v4.16b
    (0x7a1f34#64,  0x6e2a1d6b#32),   -- eor  v11.16b, v11.16b, v10.16b
    (0x7a1f38#64,  0x54ffe5cb#32),   -- b.lt  7a1bf0 <.Ldec_main_loop>  // b.tstop

    -- 00000000007a1f3c <.Ldec_prepretail>:
    (0x7a1f3c#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a1f40#64,  0x4e083c55#32),   -- mov  x21, v2.d[0]
    (0x7a1f44#64,  0x6e231ce3#32),   -- eor  v3.16b, v7.16b, v3.16b
    (0x7a1f48#64,  0x4e284a40#32),   -- aese  v0.16b, v18.16b
    (0x7a1f4c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1f50#64,  0x4e183c56#32),   -- mov  x22, v2.d[1]
    (0x7a1f54#64,  0x4e284a41#32),   -- aese  v1.16b, v18.16b
    (0x7a1f58#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1f5c#64,  0x9e670142#32),   -- fmov  d2, x10
    (0x7a1f60#64,  0x9eaf0122#32),   -- fmov  v2.d[1], x9
    (0x7a1f64#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a1f68#64,  0x6e2b1c84#32),   -- eor  v4.16b, v4.16b, v11.16b
    (0x7a1f6c#64,  0x4e2008c6#32),   -- rev64  v6.16b, v6.16b
    (0x7a1f70#64,  0xaa098169#32),   -- orr  x9, x11, x9, lsl #32
    (0x7a1f74#64,  0x4e083c77#32),   -- mov  x23, v3.d[0]
    (0x7a1f78#64,  0x4e284a61#32),   -- aese  v1.16b, v19.16b
    (0x7a1f7c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1f80#64,  0x4e183c78#32),   -- mov  x24, v3.d[1]
    (0x7a1f84#64,  0x0eefe08b#32),   -- pmull  v11.1q, v4.1d, v15.1d
    (0x7a1f88#64,  0x5e180488#32),   -- mov  d8, v4.d[1]
    (0x7a1f8c#64,  0x9e670143#32),   -- fmov  d3, x10
    (0x7a1f90#64,  0x4eefe089#32),   -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7a1f94#64,  0x9eaf0123#32),   -- fmov  v3.d[1], x9
    (0x7a1f98#64,  0x4e284a42#32),   -- aese  v2.16b, v18.16b
    (0x7a1f9c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1fa0#64,  0x5e18062a#32),   -- mov  d10, v17.d[1]
    (0x7a1fa4#64,  0x4e284a60#32),   -- aese  v0.16b, v19.16b
    (0x7a1fa8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1fac#64,  0x2e241d08#32),   -- eor  v8.8b, v8.8b, v4.8b
    (0x7a1fb0#64,  0x4eeee0a4#32),   -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7a1fb4#64,  0x4e284a62#32),   -- aese  v2.16b, v19.16b
    (0x7a1fb8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1fbc#64,  0x4e2008e7#32),   -- rev64  v7.16b, v7.16b
    (0x7a1fc0#64,  0x4e284a43#32),   -- aese  v3.16b, v18.16b
    (0x7a1fc4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1fc8#64,  0x0eeae10a#32),   -- pmull  v10.1q, v8.1d, v10.1d
    (0x7a1fcc#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a1fd0#64,  0x0eeee0a8#32),   -- pmull  v8.1q, v5.1d, v14.1d
    (0x7a1fd4#64,  0x4e284a63#32),   -- aese  v3.16b, v19.16b
    (0x7a1fd8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a1fdc#64,  0x5e1804a4#32),   -- mov  d4, v5.d[1]
    (0x7a1fe0#64,  0x4e284a80#32),   -- aese  v0.16b, v20.16b
    (0x7a1fe4#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a1fe8#64,  0x4e284a81#32),   -- aese  v1.16b, v20.16b
    (0x7a1fec#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a1ff0#64,  0x6e281d6b#32),   -- eor  v11.16b, v11.16b, v8.16b
    (0x7a1ff4#64,  0x4e284a82#32),   -- aese  v2.16b, v20.16b
    (0x7a1ff8#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a1ffc#64,  0x4e284aa0#32),   -- aese  v0.16b, v21.16b
    (0x7a2000#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a2004#64,  0x5e1804c8#32),   -- mov  d8, v6.d[1]
    (0x7a2008#64,  0x4e284a83#32),   -- aese  v3.16b, v20.16b
    (0x7a200c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a2010#64,  0x2e251c84#32),   -- eor  v4.8b, v4.8b, v5.8b
    (0x7a2014#64,  0x0eede0c5#32),   -- pmull  v5.1q, v6.1d, v13.1d
    (0x7a2018#64,  0x4e284ac0#32),   -- aese  v0.16b, v22.16b
    (0x7a201c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a2020#64,  0x4e284aa3#32),   -- aese  v3.16b, v21.16b
    (0x7a2024#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a2028#64,  0x2e261d08#32),   -- eor  v8.8b, v8.8b, v6.8b
    (0x7a202c#64,  0x0ef1e084#32),   -- pmull  v4.1q, v4.1d, v17.1d
    (0x7a2030#64,  0x4e284ae0#32),   -- aese  v0.16b, v23.16b
    (0x7a2034#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a2038#64,  0x6e251d6b#32),   -- eor  v11.16b, v11.16b, v5.16b
    (0x7a203c#64,  0x4e284ac3#32),   -- aese  v3.16b, v22.16b
    (0x7a2040#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a2044#64,  0x4eece0e5#32),   -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7a2048#64,  0x6e241d4a#32),   -- eor  v10.16b, v10.16b, v4.16b
    (0x7a204c#64,  0x4eede0c4#32),   -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7a2050#64,  0x4e284ae3#32),   -- aese  v3.16b, v23.16b
    (0x7a2054#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a2058#64,  0x6e180508#32),   -- mov  v8.d[1], v8.d[0]
    (0x7a205c#64,  0x4e284aa2#32),   -- aese  v2.16b, v21.16b
    (0x7a2060#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a2064#64,  0x4e284aa1#32),   -- aese  v1.16b, v21.16b
    (0x7a2068#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a206c#64,  0x6e241d29#32),   -- eor  v9.16b, v9.16b, v4.16b
    (0x7a2070#64,  0x0eece0e4#32),   -- pmull  v4.1q, v7.1d, v12.1d
    (0x7a2074#64,  0x4e284ac2#32),   -- aese  v2.16b, v22.16b
    (0x7a2078#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a207c#64,  0x5e1804e6#32),   -- mov  d6, v7.d[1]
    (0x7a2080#64,  0x4e284ac1#32),   -- aese  v1.16b, v22.16b
    (0x7a2084#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a2088#64,  0x4ef0e108#32),   -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7a208c#64,  0x4e284ae2#32),   -- aese  v2.16b, v23.16b
    (0x7a2090#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a2094#64,  0x2e271cc6#32),   -- eor  v6.8b, v6.8b, v7.8b
    (0x7a2098#64,  0x4e284ae1#32),   -- aese  v1.16b, v23.16b
    (0x7a209c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a20a0#64,  0x4e284b03#32),   -- aese  v3.16b, v24.16b
    (0x7a20a4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a20a8#64,  0x6e281d4a#32),   -- eor  v10.16b, v10.16b, v8.16b
    (0x7a20ac#64,  0x4e284b02#32),   -- aese  v2.16b, v24.16b
    (0x7a20b0#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a20b4#64,  0x4e284b00#32),   -- aese  v0.16b, v24.16b
    (0x7a20b8#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a20bc#64,  0x0f06e448#32),   -- movi  v8.8b, #0xc2
    (0x7a20c0#64,  0x4e284b01#32),   -- aese  v1.16b, v24.16b
    (0x7a20c4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a20c8#64,  0x6e241d6b#32),   -- eor  v11.16b, v11.16b, v4.16b
    (0x7a20cc#64,  0x0ef0e0c6#32),   -- pmull  v6.1q, v6.1d, v16.1d
    (0x7a20d0#64,  0x4e284b23#32),   -- aese  v3.16b, v25.16b
    (0x7a20d4#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a20d8#64,  0xf100323f#32),   -- cmp  x17, #0xc
    (0x7a20dc#64,  0x6e251d29#32),   -- eor  v9.16b, v9.16b, v5.16b
    (0x7a20e0#64,  0x4e284b21#32),   -- aese  v1.16b, v25.16b
    (0x7a20e4#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a20e8#64,  0x4e284b20#32),   -- aese  v0.16b, v25.16b
    (0x7a20ec#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a20f0#64,  0x6e261d4a#32),   -- eor  v10.16b, v10.16b, v6.16b
    (0x7a20f4#64,  0x4e284b43#32),   -- aese  v3.16b, v26.16b
    (0x7a20f8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a20fc#64,  0x4e284b22#32),   -- aese  v2.16b, v25.16b
    (0x7a2100#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a2104#64,  0x6e291d66#32),   -- eor  v6.16b, v11.16b, v9.16b
    (0x7a2108#64,  0x4e284b41#32),   -- aese  v1.16b, v26.16b
    (0x7a210c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a2110#64,  0x4e284b40#32),   -- aese  v0.16b, v26.16b
    (0x7a2114#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a2118#64,  0x5f785508#32),   -- shl  d8, d8, #56
    (0x7a211c#64,  0x4e284b42#32),   -- aese  v2.16b, v26.16b
    (0x7a2120#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a2124#64,  0x5400044b#32),   -- b.lt  7a21ac <.Ldec_finish_prepretail>  // b.tstop
    (0x7a2128#64,  0x4e284b61#32),   -- aese  v1.16b, v27.16b
    (0x7a212c#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a2130#64,  0x4e284b62#32),   -- aese  v2.16b, v27.16b
    (0x7a2134#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a2138#64,  0x4e284b63#32),   -- aese  v3.16b, v27.16b
    (0x7a213c#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a2140#64,  0x4e284b60#32),   -- aese  v0.16b, v27.16b
    (0x7a2144#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a2148#64,  0x4e284b82#32),   -- aese  v2.16b, v28.16b
    (0x7a214c#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a2150#64,  0x4e284b83#32),   -- aese  v3.16b, v28.16b
    (0x7a2154#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a2158#64,  0x4e284b80#32),   -- aese  v0.16b, v28.16b
    (0x7a215c#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a2160#64,  0x4e284b81#32),   -- aese  v1.16b, v28.16b
    (0x7a2164#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a2168#64,  0x54000220#32),   -- b.eq  7a21ac <.Ldec_finish_prepretail>  // b.none
    (0x7a216c#64,  0x4e284ba2#32),   -- aese  v2.16b, v29.16b
    (0x7a2170#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a2174#64,  0x4e284ba0#32),   -- aese  v0.16b, v29.16b
    (0x7a2178#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a217c#64,  0x4e284ba1#32),   -- aese  v1.16b, v29.16b
    (0x7a2180#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a2184#64,  0x4e284bc2#32),   -- aese  v2.16b, v30.16b
    (0x7a2188#64,  0x4e286842#32),   -- aesmc  v2.16b, v2.16b
    (0x7a218c#64,  0x4e284ba3#32),   -- aese  v3.16b, v29.16b
    (0x7a2190#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b
    (0x7a2194#64,  0x4e284bc1#32),   -- aese  v1.16b, v30.16b
    (0x7a2198#64,  0x4e286821#32),   -- aesmc  v1.16b, v1.16b
    (0x7a219c#64,  0x4e284bc0#32),   -- aese  v0.16b, v30.16b
    (0x7a21a0#64,  0x4e286800#32),   -- aesmc  v0.16b, v0.16b
    (0x7a21a4#64,  0x4e284bc3#32),   -- aese  v3.16b, v30.16b
    (0x7a21a8#64,  0x4e286863#32),   -- aesmc  v3.16b, v3.16b

    -- 00000000007a21ac <.Ldec_finish_prepretail>:
    (0x7a21ac#64,  0x6e261d4a#32),   -- eor  v10.16b, v10.16b, v6.16b
    (0x7a21b0#64,  0x0ee8e127#32),   -- pmull  v7.1q, v9.1d, v8.1d
    (0x7a21b4#64,  0x6e094129#32),   -- ext  v9.16b, v9.16b, v9.16b, #8
    (0x7a21b8#64,  0x6e271d4a#32),   -- eor  v10.16b, v10.16b, v7.16b
    (0x7a21bc#64,  0xca0e02d6#32),   -- eor  x22, x22, x14
    (0x7a21c0#64,  0xca0d02f7#32),   -- eor  x23, x23, x13
    (0x7a21c4#64,  0x6e291d4a#32),   -- eor  v10.16b, v10.16b, v9.16b
    (0x7a21c8#64,  0x1100058c#32),   -- add  w12, w12, #0x1
    (0x7a21cc#64,  0xca0d02b5#32),   -- eor  x21, x21, x13
    (0x7a21d0#64,  0x0ee8e148#32),   -- pmull  v8.1q, v10.1d, v8.1d
    (0x7a21d4#64,  0xca0e0318#32),   -- eor  x24, x24, x14
    (0x7a21d8#64,  0xa8815855#32),   -- stp  x21, x22, [x2], #16
    (0x7a21dc#64,  0x6e0a414a#32),   -- ext  v10.16b, v10.16b, v10.16b, #8
    (0x7a21e0#64,  0xa8816057#32),   -- stp  x23, x24, [x2], #16
    (0x7a21e4#64,  0x6e281d6b#32),   -- eor  v11.16b, v11.16b, v8.16b
    (0x7a21e8#64,  0x4e284be1#32),   -- aese  v1.16b, v31.16b
    (0x7a21ec#64,  0x4e284be0#32),   -- aese  v0.16b, v31.16b
    (0x7a21f0#64,  0x4e284be3#32),   -- aese  v3.16b, v31.16b
    (0x7a21f4#64,  0x4e284be2#32),   -- aese  v2.16b, v31.16b
    (0x7a21f8#64,  0x6e2a1d6b#32),   -- eor  v11.16b, v11.16b, v10.16b

    -- 00000000007a21fc <.Ldec_tail>:
    (0x7a21fc#64,  0xcb000085#32),   -- sub  x5, x4, x0
    (0x7a2200#64,  0x4cdf7005#32),   -- ld1  {v5.16b}, [x0], #16
    (0x7a2204#64,  0x6e201ca0#32),   -- eor  v0.16b, v5.16b, v0.16b
    (0x7a2208#64,  0x4e083c06#32),   -- mov  x6, v0.d[0]
    (0x7a220c#64,  0x4e183c07#32),   -- mov  x7, v0.d[1]
    (0x7a2210#64,  0x6e0b4168#32),   -- ext  v8.16b, v11.16b, v11.16b, #8
    (0x7a2214#64,  0xf100c0bf#32),   -- cmp  x5, #0x30
    (0x7a2218#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a221c#64,  0xca0e00e7#32),   -- eor  x7, x7, x14
    (0x7a2220#64,  0x540001ec#32),   -- b.gt  7a225c <.Ldec_blocks_more_than_3>
    (0x7a2224#64,  0x5100058c#32),   -- sub  w12, w12, #0x1
    (0x7a2228#64,  0x4ea21c43#32),   -- mov  v3.16b, v2.16b
    (0x7a222c#64,  0x0f00e40a#32),   -- movi  v10.8b, #0x0
    (0x7a2230#64,  0x0f00e40b#32),   -- movi  v11.8b, #0x0
    (0x7a2234#64,  0xf10080bf#32),   -- cmp  x5, #0x20
    (0x7a2238#64,  0x0f00e409#32),   -- movi  v9.8b, #0x0
    (0x7a223c#64,  0x4ea11c22#32),   -- mov  v2.16b, v1.16b
    (0x7a2240#64,  0x540002ec#32),   -- b.gt  7a229c <.Ldec_blocks_more_than_2>
    (0x7a2244#64,  0x5100058c#32),   -- sub  w12, w12, #0x1
    (0x7a2248#64,  0x4ea11c23#32),   -- mov  v3.16b, v1.16b
    (0x7a224c#64,  0xf10040bf#32),   -- cmp  x5, #0x10
    (0x7a2250#64,  0x540004ac#32),   -- b.gt  7a22e4 <.Ldec_blocks_more_than_1>
    (0x7a2254#64,  0x5100058c#32),   -- sub  w12, w12, #0x1
    (0x7a2258#64,  0x14000036#32),   -- b  7a2330 <.Ldec_blocks_less_than_1>

    -- 00000000007a225c <.Ldec_blocks_more_than_3>:
    (0x7a225c#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a2260#64,  0x4cdf7005#32),   -- ld1  {v5.16b}, [x0], #16
    (0x7a2264#64,  0xa8811c46#32),   -- stp  x6, x7, [x2], #16
    (0x7a2268#64,  0x5e18062a#32),   -- mov  d10, v17.d[1]
    (0x7a226c#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a2270#64,  0x6e211ca0#32),   -- eor  v0.16b, v5.16b, v1.16b
    (0x7a2274#64,  0x5e180496#32),   -- mov  d22, v4.d[1]
    (0x7a2278#64,  0x4e083c06#32),   -- mov  x6, v0.d[0]
    (0x7a227c#64,  0x4e183c07#32),   -- mov  x7, v0.d[1]
    (0x7a2280#64,  0x2e241ed6#32),   -- eor  v22.8b, v22.8b, v4.8b
    (0x7a2284#64,  0x0f00e408#32),   -- movi  v8.8b, #0x0
    (0x7a2288#64,  0x4eefe089#32),   -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7a228c#64,  0x0eeae2ca#32),   -- pmull  v10.1q, v22.1d, v10.1d
    (0x7a2290#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a2294#64,  0x0eefe08b#32),   -- pmull  v11.1q, v4.1d, v15.1d
    (0x7a2298#64,  0xca0e00e7#32),   -- eor  x7, x7, x14

    -- 00000000007a229c <.Ldec_blocks_more_than_2>:
    (0x7a229c#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a22a0#64,  0x4cdf7005#32),   -- ld1  {v5.16b}, [x0], #16
    (0x7a22a4#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a22a8#64,  0xa8811c46#32),   -- stp  x6, x7, [x2], #16
    (0x7a22ac#64,  0x6e221ca0#32),   -- eor  v0.16b, v5.16b, v2.16b
    (0x7a22b0#64,  0x5e180496#32),   -- mov  d22, v4.d[1]
    (0x7a22b4#64,  0x0eeee095#32),   -- pmull  v21.1q, v4.1d, v14.1d
    (0x7a22b8#64,  0x4eeee094#32),   -- pmull2  v20.1q, v4.2d, v14.2d
    (0x7a22bc#64,  0x2e241ed6#32),   -- eor  v22.8b, v22.8b, v4.8b
    (0x7a22c0#64,  0x4e083c06#32),   -- mov  x6, v0.d[0]
    (0x7a22c4#64,  0x4e183c07#32),   -- mov  x7, v0.d[1]
    (0x7a22c8#64,  0x6e351d6b#32),   -- eor  v11.16b, v11.16b, v21.16b
    (0x7a22cc#64,  0x0f00e408#32),   -- movi  v8.8b, #0x0
    (0x7a22d0#64,  0x0ef1e2d6#32),   -- pmull  v22.1q, v22.1d, v17.1d
    (0x7a22d4#64,  0x6e341d29#32),   -- eor  v9.16b, v9.16b, v20.16b
    (0x7a22d8#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a22dc#64,  0x6e361d4a#32),   -- eor  v10.16b, v10.16b, v22.16b
    (0x7a22e0#64,  0xca0e00e7#32),   -- eor  x7, x7, x14

    -- 00000000007a22e4 <.Ldec_blocks_more_than_1>:
    (0x7a22e4#64,  0xa8811c46#32),   -- stp  x6, x7, [x2], #16
    (0x7a22e8#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a22ec#64,  0x4cdf7005#32),   -- ld1  {v5.16b}, [x0], #16
    (0x7a22f0#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a22f4#64,  0x0f00e408#32),   -- movi  v8.8b, #0x0
    (0x7a22f8#64,  0x5e180496#32),   -- mov  d22, v4.d[1]
    (0x7a22fc#64,  0x6e231ca0#32),   -- eor  v0.16b, v5.16b, v3.16b
    (0x7a2300#64,  0x4eede094#32),   -- pmull2  v20.1q, v4.2d, v13.2d
    (0x7a2304#64,  0x2e241ed6#32),   -- eor  v22.8b, v22.8b, v4.8b
    (0x7a2308#64,  0x0eede095#32),   -- pmull  v21.1q, v4.1d, v13.1d
    (0x7a230c#64,  0x4e083c06#32),   -- mov  x6, v0.d[0]
    (0x7a2310#64,  0x6e1806d6#32),   -- mov  v22.d[1], v22.d[0]
    (0x7a2314#64,  0x4e183c07#32),   -- mov  x7, v0.d[1]
    (0x7a2318#64,  0x4ef0e2d6#32),   -- pmull2  v22.1q, v22.2d, v16.2d
    (0x7a231c#64,  0xca0d00c6#32),   -- eor  x6, x6, x13
    (0x7a2320#64,  0x6e351d6b#32),   -- eor  v11.16b, v11.16b, v21.16b
    (0x7a2324#64,  0x6e341d29#32),   -- eor  v9.16b, v9.16b, v20.16b
    (0x7a2328#64,  0x6e361d4a#32),   -- eor  v10.16b, v10.16b, v22.16b
    (0x7a232c#64,  0xca0e00e7#32),   -- eor  x7, x7, x14

    -- 00000000007a2330 <.Ldec_blocks_less_than_1>:
    (0x7a2330#64,  0x92401821#32),   -- and  x1, x1, #0x7f
    (0x7a2334#64,  0xaa3f03ee#32),   -- mvn  x14, xzr
    (0x7a2338#64,  0xd1020021#32),   -- sub  x1, x1, #0x80
    (0x7a233c#64,  0xaa3f03ed#32),   -- mvn  x13, xzr
    (0x7a2340#64,  0xa9401444#32),   -- ldp  x4, x5, [x2]
    (0x7a2344#64,  0xcb0103e1#32),   -- neg  x1, x1
    (0x7a2348#64,  0x92401821#32),   -- and  x1, x1, #0x7f
    (0x7a234c#64,  0x9ac125ce#32),   -- lsr  x14, x14, x1
    (0x7a2350#64,  0xf101003f#32),   -- cmp  x1, #0x40
    (0x7a2354#64,  0x9a8eb1a9#32),   -- csel  x9, x13, x14, lt  // lt = tstop
    (0x7a2358#64,  0x9a9fb1ca#32),   -- csel  x10, x14, xzr, lt  // lt = tstop
    (0x7a235c#64,  0x9e670120#32),   -- fmov  d0, x9
    (0x7a2360#64,  0x8a0900c6#32),   -- and  x6, x6, x9
    (0x7a2364#64,  0x4e181d40#32),   -- mov  v0.d[1], x10
    (0x7a2368#64,  0x8a290084#32),   -- bic  x4, x4, x9
    (0x7a236c#64,  0x5ac00989#32),   -- rev  w9, w12
    (0x7a2370#64,  0x8a2a00a5#32),   -- bic  x5, x5, x10
    (0x7a2374#64,  0xaa0400c6#32),   -- orr  x6, x6, x4
    (0x7a2378#64,  0x8a0a00e7#32),   -- and  x7, x7, x10
    (0x7a237c#64,  0xaa0500e7#32),   -- orr  x7, x7, x5
    (0x7a2380#64,  0x4e201ca5#32),   -- and  v5.16b, v5.16b, v0.16b
    (0x7a2384#64,  0x4e2008a4#32),   -- rev64  v4.16b, v5.16b
    (0x7a2388#64,  0x6e281c84#32),   -- eor  v4.16b, v4.16b, v8.16b
    (0x7a238c#64,  0x0eece095#32),   -- pmull  v21.1q, v4.1d, v12.1d
    (0x7a2390#64,  0x5e180488#32),   -- mov  d8, v4.d[1]
    (0x7a2394#64,  0x2e241d08#32),   -- eor  v8.8b, v8.8b, v4.8b
    (0x7a2398#64,  0x4eece094#32),   -- pmull2  v20.1q, v4.2d, v12.2d
    (0x7a239c#64,  0x0ef0e108#32),   -- pmull  v8.1q, v8.1d, v16.1d
    (0x7a23a0#64,  0x6e341d29#32),   -- eor  v9.16b, v9.16b, v20.16b
    (0x7a23a4#64,  0x6e351d6b#32),   -- eor  v11.16b, v11.16b, v21.16b
    (0x7a23a8#64,  0x6e281d4a#32),   -- eor  v10.16b, v10.16b, v8.16b
    (0x7a23ac#64,  0x0f06e448#32),   -- movi  v8.8b, #0xc2
    (0x7a23b0#64,  0x6e291d66#32),   -- eor  v6.16b, v11.16b, v9.16b
    (0x7a23b4#64,  0x5f785508#32),   -- shl  d8, d8, #56
    (0x7a23b8#64,  0x6e261d4a#32),   -- eor  v10.16b, v10.16b, v6.16b
    (0x7a23bc#64,  0x0ee8e127#32),   -- pmull  v7.1q, v9.1d, v8.1d
    (0x7a23c0#64,  0x6e094129#32),   -- ext  v9.16b, v9.16b, v9.16b, #8
    (0x7a23c4#64,  0x6e271d4a#32),   -- eor  v10.16b, v10.16b, v7.16b
    (0x7a23c8#64,  0x6e291d4a#32),   -- eor  v10.16b, v10.16b, v9.16b
    (0x7a23cc#64,  0x0ee8e148#32),   -- pmull  v8.1q, v10.1d, v8.1d
    (0x7a23d0#64,  0x6e0a414a#32),   -- ext  v10.16b, v10.16b, v10.16b, #8
    (0x7a23d4#64,  0x6e281d6b#32),   -- eor  v11.16b, v11.16b, v8.16b
    (0x7a23d8#64,  0xa9001c46#32),   -- stp  x6, x7, [x2]
    (0x7a23dc#64,  0xb9000e09#32),   -- str  w9, [x16, #12]
    (0x7a23e0#64,  0x6e2a1d6b#32),   -- eor  v11.16b, v11.16b, v10.16b
    (0x7a23e4#64,  0x6e0b416b#32),   -- ext  v11.16b, v11.16b, v11.16b, #8
    (0x7a23e8#64,  0x4e20096b#32),   -- rev64  v11.16b, v11.16b
    (0x7a23ec#64,  0xaa0f03e0#32),   -- mov  x0, x15
    (0x7a23f0#64,  0x4c00706b#32),   -- st1  {v11.16b}, [x3]
    (0x7a23f4#64,  0xa94153f3#32),   -- ldp  x19, x20, [sp, #16]
    (0x7a23f8#64,  0xa9425bf5#32),   -- ldp  x21, x22, [sp, #32]
    (0x7a23fc#64,  0xa94363f7#32),   -- ldp  x23, x24, [sp, #48]
    (0x7a2400#64,  0x6d4427e8#32),   -- ldp  d8, d9, [sp, #64]
    (0x7a2404#64,  0x6d452fea#32),   -- ldp  d10, d11, [sp, #80]
    (0x7a2408#64,  0x6d4637ec#32),   -- ldp  d12, d13, [sp, #96]
    (0x7a240c#64,  0x6d473fee#32),   -- ldp  d14, d15, [sp, #112]
    (0x7a2410#64,  0xa8c87bfd#32),   -- ldp  x29, x30, [sp], #128
    (0x7a2414#64,  0xd65f03c0#32),   -- ret
  ]

end AESGCMDecKernelProgram
