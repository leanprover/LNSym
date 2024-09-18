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
         Htable -- powers of H precomputed up to H^8 (x6)
  output: out -- plaintext (x2)
          Xi -- current hash/tag value, decryption function will recalculate
                the hash based on the ciphertext, the top-level c function
                CRYPTO_gcm128_finish will compare the recalculated hash with
                hash produced from encryption (x3)

-/

def aes_gcm_dec_kernel_program : Program :=
  def_program
  [ -- 00000000007d0150 <aes_gcm_dec_kernel>:
    (0x7d0150#64, 0xa9b87bfd#32),        -- stp     x29, x30, [sp, #-128]!
    (0x7d0154#64, 0x910003fd#32),        -- mov     x29, sp
    (0x7d0158#64, 0xa90153f3#32),        -- stp     x19, x20, [sp, #16]
    (0x7d015c#64, 0xaa0403f0#32),        -- mov     x16, x4
    (0x7d0160#64, 0xaa0503e8#32),        -- mov     x8, x5
    (0x7d0164#64, 0xa9025bf5#32),        -- stp     x21, x22, [sp, #32]
    (0x7d0168#64, 0xa90363f7#32),        -- stp     x23, x24, [sp, #48]
    (0x7d016c#64, 0x6d0427e8#32),        -- stp     d8, d9, [sp, #64]
    (0x7d0170#64, 0x6d052fea#32),        -- stp     d10, d11, [sp, #80]
    (0x7d0174#64, 0x6d0637ec#32),        -- stp     d12, d13, [sp, #96]
    (0x7d0178#64, 0x6d073fee#32),        -- stp     d14, d15, [sp, #112]
    (0x7d017c#64, 0xb940f111#32),        -- ldr     w17, [x8, #240]
    (0x7d0180#64, 0x8b111113#32),        -- add     x19, x8, x17, lsl #4
    (0x7d0184#64, 0xa9403a6d#32),        -- ldp     x13, x14, [x19]
    (0x7d0188#64, 0x3cdf027f#32),        -- ldur    q31, [x19, #-16]
    (0x7d018c#64, 0xd343fc25#32),        -- lsr     x5, x1, #3
    (0x7d0190#64, 0xaa0503ef#32),        -- mov     x15, x5
    (0x7d0194#64, 0xa9402e0a#32),        -- ldp     x10, x11, [x16]
    (0x7d0198#64, 0x3dc0211a#32),        -- ldr     q26, [x8, #128]
    (0x7d019c#64, 0xd10004a5#32),        -- sub     x5, x5, #0x1
    (0x7d01a0#64, 0x3dc01d19#32),        -- ldr     q25, [x8, #112]
    (0x7d01a4#64, 0x927ae4a5#32),        -- and     x5, x5, #0xffffffffffffffc0
    (0x7d01a8#64, 0x8b410c04#32),        -- add     x4, x0, x1, lsr #3
    (0x7d01ac#64, 0x3dc01918#32),        -- ldr     q24, [x8, #96]
    (0x7d01b0#64, 0xd360fd6c#32),        -- lsr     x12, x11, #32
    (0x7d01b4#64, 0x3dc01517#32),        -- ldr     q23, [x8, #80]
    (0x7d01b8#64, 0x2a0b016b#32),        -- orr     w11, w11, w11
    (0x7d01bc#64, 0x3dc00d15#32),        -- ldr     q21, [x8, #48]
    (0x7d01c0#64, 0x8b0000a5#32),        -- add     x5, x5, x0
    (0x7d01c4#64, 0x5ac0098c#32),        -- rev     w12, w12
    (0x7d01c8#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d01cc#64, 0x9e670143#32),        -- fmov    d3, x10
    (0x7d01d0#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d01d4#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d01d8#64, 0x9e670141#32),        -- fmov    d1, x10
    (0x7d01dc#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d01e0#64, 0x4c407200#32),        -- ld1     {v0.16b}, [x16]
    (0x7d01e4#64, 0x9eaf0121#32),        -- fmov    v1.d[1], x9
    (0x7d01e8#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d01ec#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d01f0#64, 0x9e670142#32),        -- fmov    d2, x10
    (0x7d01f4#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d01f8#64, 0x9eaf0122#32),        -- fmov    v2.d[1], x9
    (0x7d01fc#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d0200#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d0204#64, 0x3dc00112#32),        -- ldr     q18, [x8]
    (0x7d0208#64, 0x9eaf0123#32),        -- fmov    v3.d[1], x9
    (0x7d020c#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d0210#64, 0x3dc01116#32),        -- ldr     q22, [x8, #64]
    (0x7d0214#64, 0x3dc00513#32),        -- ldr     q19, [x8, #16]
    (0x7d0218#64, 0x4e284a40#32),        -- aese    v0.16b, v18.16b
    (0x7d021c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0220#64, 0x3dc00cce#32),        -- ldr     q14, [x6, #48]
    (0x7d0224#64, 0x4e284a43#32),        -- aese    v3.16b, v18.16b
    (0x7d0228#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d022c#64, 0x3dc014cf#32),        -- ldr     q15, [x6, #80]
    (0x7d0230#64, 0x4e284a41#32),        -- aese    v1.16b, v18.16b
    (0x7d0234#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0238#64, 0x3dc008cd#32),        -- ldr     q13, [x6, #32]
    (0x7d023c#64, 0x4e284a42#32),        -- aese    v2.16b, v18.16b
    (0x7d0240#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0244#64, 0x3dc00914#32),        -- ldr     q20, [x8, #32]
    (0x7d0248#64, 0x4e284a60#32),        -- aese    v0.16b, v19.16b
    (0x7d024c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0250#64, 0x4e284a61#32),        -- aese    v1.16b, v19.16b
    (0x7d0254#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0258#64, 0x4c40706b#32),        -- ld1     {v11.16b}, [x3]
    (0x7d025c#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7d0260#64, 0x4e20096b#32),        -- rev64   v11.16b, v11.16b
    (0x7d0264#64, 0x4e284a62#32),        -- aese    v2.16b, v19.16b
    (0x7d0268#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d026c#64, 0x3dc0251b#32),        -- ldr     q27, [x8, #144]
    (0x7d0270#64, 0x4e284a63#32),        -- aese    v3.16b, v19.16b
    (0x7d0274#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0278#64, 0x3dc0311e#32),        -- ldr     q30, [x8, #192]
    (0x7d027c#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7d0280#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0284#64, 0x3dc000cc#32),        -- ldr     q12, [x6]
    (0x7d0288#64, 0x4e284a82#32),        -- aese    v2.16b, v20.16b
    (0x7d028c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0290#64, 0x3dc0291c#32),        -- ldr     q28, [x8, #160]
    (0x7d0294#64, 0x4e284a83#32),        -- aese    v3.16b, v20.16b
    (0x7d0298#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d029c#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7d02a0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d02a4#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7d02a8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d02ac#64, 0x4e284aa3#32),        -- aese    v3.16b, v21.16b
    (0x7d02b0#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d02b4#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7d02b8#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d02bc#64, 0x4e284aa2#32),        -- aese    v2.16b, v21.16b
    (0x7d02c0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d02c4#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7d02c8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d02cc#64, 0x4e284ac3#32),        -- aese    v3.16b, v22.16b
    (0x7d02d0#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d02d4#64, 0x4e284ac2#32),        -- aese    v2.16b, v22.16b
    (0x7d02d8#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d02dc#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7d02e0#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d02e4#64, 0x4e284ae3#32),        -- aese    v3.16b, v23.16b
    (0x7d02e8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d02ec#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7d02f0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d02f4#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7d02f8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d02fc#64, 0x4e284ae2#32),        -- aese    v2.16b, v23.16b
    (0x7d0300#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0304#64, 0x4e284b00#32),        -- aese    v0.16b, v24.16b
    (0x7d0308#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d030c#64, 0x4e284b03#32),        -- aese    v3.16b, v24.16b
    (0x7d0310#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0314#64, 0xf100323f#32),        -- cmp     x17, #0xc
    (0x7d0318#64, 0x4e284b01#32),        -- aese    v1.16b, v24.16b
    (0x7d031c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0320#64, 0x4e284b02#32),        -- aese    v2.16b, v24.16b
    (0x7d0324#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0328#64, 0x4e284b20#32),        -- aese    v0.16b, v25.16b
    (0x7d032c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0330#64, 0x4e284b21#32),        -- aese    v1.16b, v25.16b
    (0x7d0334#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0338#64, 0x4e284b23#32),        -- aese    v3.16b, v25.16b
    (0x7d033c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0340#64, 0x4e284b40#32),        -- aese    v0.16b, v26.16b
    (0x7d0344#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0348#64, 0x4e284b22#32),        -- aese    v2.16b, v25.16b
    (0x7d034c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0350#64, 0x4e284b43#32),        -- aese    v3.16b, v26.16b
    (0x7d0354#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0358#64, 0x4e284b41#32),        -- aese    v1.16b, v26.16b
    (0x7d035c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0360#64, 0x3dc02d1d#32),        -- ldr     q29, [x8, #176]
    (0x7d0364#64, 0x4e284b42#32),        -- aese    v2.16b, v26.16b
    (0x7d0368#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d036c#64, 0x5400044b#32),        -- b.lt    7d03f4 <.Ldec_finish_first_blocks>  // b.tstop
    (0x7d0370#64, 0x4e284b60#32),        -- aese    v0.16b, v27.16b
    (0x7d0374#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0378#64, 0x4e284b61#32),        -- aese    v1.16b, v27.16b
    (0x7d037c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0380#64, 0x4e284b63#32),        -- aese    v3.16b, v27.16b
    (0x7d0384#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0388#64, 0x4e284b62#32),        -- aese    v2.16b, v27.16b
    (0x7d038c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0390#64, 0x4e284b80#32),        -- aese    v0.16b, v28.16b
    (0x7d0394#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0398#64, 0x4e284b81#32),        -- aese    v1.16b, v28.16b
    (0x7d039c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d03a0#64, 0x4e284b83#32),        -- aese    v3.16b, v28.16b
    (0x7d03a4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d03a8#64, 0x4e284b82#32),        -- aese    v2.16b, v28.16b
    (0x7d03ac#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d03b0#64, 0x54000220#32),        -- b.eq    7d03f4 <.Ldec_finish_first_blocks>  // b.none
    (0x7d03b4#64, 0x4e284ba0#32),        -- aese    v0.16b, v29.16b
    (0x7d03b8#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d03bc#64, 0x4e284ba3#32),        -- aese    v3.16b, v29.16b
    (0x7d03c0#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d03c4#64, 0x4e284ba1#32),        -- aese    v1.16b, v29.16b
    (0x7d03c8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d03cc#64, 0x4e284ba2#32),        -- aese    v2.16b, v29.16b
    (0x7d03d0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d03d4#64, 0x4e284bc1#32),        -- aese    v1.16b, v30.16b
    (0x7d03d8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d03dc#64, 0x4e284bc0#32),        -- aese    v0.16b, v30.16b
    (0x7d03e0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d03e4#64, 0x4e284bc2#32),        -- aese    v2.16b, v30.16b
    (0x7d03e8#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d03ec#64, 0x4e284bc3#32),        -- aese    v3.16b, v30.16b
    (0x7d03f0#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b

    -- 00000000007d03f4 <.Ldec_finish_first_blocks>:
    (0x7d03f4#64, 0xeb05001f#32),        -- cmp     x0, x5
    (0x7d03f8#64, 0x4ecf29c9#32),        -- trn1    v9.2d, v14.2d, v15.2d
    (0x7d03fc#64, 0x4ecf69d1#32),        -- trn2    v17.2d, v14.2d, v15.2d
    (0x7d0400#64, 0x4ecd2988#32),        -- trn1    v8.2d, v12.2d, v13.2d
    (0x7d0404#64, 0x4ecd6990#32),        -- trn2    v16.2d, v12.2d, v13.2d
    (0x7d0408#64, 0x6e291e31#32),        -- eor     v17.16b, v17.16b, v9.16b
    (0x7d040c#64, 0x4e284be1#32),        -- aese    v1.16b, v31.16b
    (0x7d0410#64, 0x4e284be2#32),        -- aese    v2.16b, v31.16b
    (0x7d0414#64, 0x6e281e10#32),        -- eor     v16.16b, v16.16b, v8.16b
    (0x7d0418#64, 0x4e284be3#32),        -- aese    v3.16b, v31.16b
    (0x7d041c#64, 0x4e284be0#32),        -- aese    v0.16b, v31.16b
    (0x7d0420#64, 0x540034ea#32),        -- b.ge    7d0abc <.Ldec_tail>  // b.tcont
    (0x7d0424#64, 0x3dc00004#32),        -- ldr     q4, [x0]
    (0x7d0428#64, 0x3dc00405#32),        -- ldr     q5, [x0, #16]
    (0x7d042c#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d0430#64, 0x6e201c80#32),        -- eor     v0.16b, v4.16b, v0.16b
    (0x7d0434#64, 0x6e211ca1#32),        -- eor     v1.16b, v5.16b, v1.16b
    (0x7d0438#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7d043c#64, 0x3dc00c07#32),        -- ldr     q7, [x0, #48]
    (0x7d0440#64, 0x4e183c07#32),        -- mov     x7, v0.d[1]
    (0x7d0444#64, 0x4e083c06#32),        -- mov     x6, v0.d[0]
    (0x7d0448#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7d044c#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d0450#64, 0x9e670140#32),        -- fmov    d0, x10
    (0x7d0454#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d0458#64, 0x9eaf0120#32),        -- fmov    v0.d[1], x9
    (0x7d045c#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d0460#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d0464#64, 0x4e083c33#32),        -- mov     x19, v1.d[0]
    (0x7d0468#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d046c#64, 0x4e183c34#32),        -- mov     x20, v1.d[1]
    (0x7d0470#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7d0474#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d0478#64, 0xa8811c46#32),        -- stp     x6, x7, [x2], #16
    (0x7d047c#64, 0x9e670141#32),        -- fmov    d1, x10
    (0x7d0480#64, 0x3dc00806#32),        -- ldr     q6, [x0, #32]
    (0x7d0484#64, 0x91010000#32),        -- add     x0, x0, #0x40
    (0x7d0488#64, 0x9eaf0121#32),        -- fmov    v1.d[1], x9
    (0x7d048c#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d0490#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d0494#64, 0xca0d0273#32),        -- eor     x19, x19, x13
    (0x7d0498#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d049c#64, 0xca0e0294#32),        -- eor     x20, x20, x14
    (0x7d04a0#64, 0xa8815053#32),        -- stp     x19, x20, [x2], #16
    (0x7d04a4#64, 0x6e221cc2#32),        -- eor     v2.16b, v6.16b, v2.16b
    (0x7d04a8#64, 0xeb05001f#32),        -- cmp     x0, x5
    (0x7d04ac#64, 0x54001a8a#32),        -- b.ge    7d07fc <.Ldec_prepretail>  // b.tcont

    -- 00000000007d04b0 <.Ldec_main_loop>:
    (0x7d04b0#64, 0x4e083c55#32),        -- mov     x21, v2.d[0]
    (0x7d04b4#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7d04b8#64, 0x6e231ce3#32),        -- eor     v3.16b, v7.16b, v3.16b
    (0x7d04bc#64, 0x4e284a40#32),        -- aese    v0.16b, v18.16b
    (0x7d04c0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d04c4#64, 0x4e183c56#32),        -- mov     x22, v2.d[1]
    (0x7d04c8#64, 0x4e284a41#32),        -- aese    v1.16b, v18.16b
    (0x7d04cc#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d04d0#64, 0x9e670142#32),        -- fmov    d2, x10
    (0x7d04d4#64, 0x9eaf0122#32),        -- fmov    v2.d[1], x9
    (0x7d04d8#64, 0x6e2b1c84#32),        -- eor     v4.16b, v4.16b, v11.16b
    (0x7d04dc#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d04e0#64, 0x4e284a60#32),        -- aese    v0.16b, v19.16b
    (0x7d04e4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d04e8#64, 0x4e183c78#32),        -- mov     x24, v3.d[1]
    (0x7d04ec#64, 0x4e284a61#32),        -- aese    v1.16b, v19.16b
    (0x7d04f0#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d04f4#64, 0x4e083c77#32),        -- mov     x23, v3.d[0]
    (0x7d04f8#64, 0x4eefe089#32),        -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7d04fc#64, 0x5e180488#32),        -- mov     d8, v4.d[1]
    (0x7d0500#64, 0x9e670143#32),        -- fmov    d3, x10
    (0x7d0504#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7d0508#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d050c#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d0510#64, 0x4e284a42#32),        -- aese    v2.16b, v18.16b
    (0x7d0514#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0518#64, 0x9eaf0123#32),        -- fmov    v3.d[1], x9
    (0x7d051c#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7d0520#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0524#64, 0x2e241d08#32),        -- eor     v8.8b, v8.8b, v4.8b
    (0x7d0528#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7d052c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0530#64, 0xca0e02d6#32),        -- eor     x22, x22, x14
    (0x7d0534#64, 0x4e284a62#32),        -- aese    v2.16b, v19.16b
    (0x7d0538#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d053c#64, 0x5e18062a#32),        -- mov     d10, v17.d[1]
    (0x7d0540#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7d0544#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0548#64, 0x4e2008c6#32),        -- rev64   v6.16b, v6.16b
    (0x7d054c#64, 0x4e284a43#32),        -- aese    v3.16b, v18.16b
    (0x7d0550#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0554#64, 0xca0d02b5#32),        -- eor     x21, x21, x13
    (0x7d0558#64, 0x4e284a82#32),        -- aese    v2.16b, v20.16b
    (0x7d055c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0560#64, 0xa8815855#32),        -- stp     x21, x22, [x2], #16
    (0x7d0564#64, 0x0eefe08b#32),        -- pmull   v11.1q, v4.1d, v15.1d
    (0x7d0568#64, 0x4eeee0a4#32),        -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7d056c#64, 0x4e284aa2#32),        -- aese    v2.16b, v21.16b
    (0x7d0570#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0574#64, 0x4e2008e7#32),        -- rev64   v7.16b, v7.16b
    (0x7d0578#64, 0x0eeae10a#32),        -- pmull   v10.1q, v8.1d, v10.1d
    (0x7d057c#64, 0xca0d02f7#32),        -- eor     x23, x23, x13
    (0x7d0580#64, 0x0eeee0a8#32),        -- pmull   v8.1q, v5.1d, v14.1d
    (0x7d0584#64, 0xca0e0318#32),        -- eor     x24, x24, x14
    (0x7d0588#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7d058c#64, 0x4e284ac2#32),        -- aese    v2.16b, v22.16b
    (0x7d0590#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0594#64, 0x4e284a63#32),        -- aese    v3.16b, v19.16b
    (0x7d0598#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d059c#64, 0x5e1804a4#32),        -- mov     d4, v5.d[1]
    (0x7d05a0#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7d05a4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d05a8#64, 0x6e281d6b#32),        -- eor     v11.16b, v11.16b, v8.16b
    (0x7d05ac#64, 0x4e284ae2#32),        -- aese    v2.16b, v23.16b
    (0x7d05b0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d05b4#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d05b8#64, 0x4e284a83#32),        -- aese    v3.16b, v20.16b
    (0x7d05bc#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d05c0#64, 0x5e1804c8#32),        -- mov     d8, v6.d[1]
    (0x7d05c4#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7d05c8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d05cc#64, 0x2e251c84#32),        -- eor     v4.8b, v4.8b, v5.8b
    (0x7d05d0#64, 0x0eede0c5#32),        -- pmull   v5.1q, v6.1d, v13.1d
    (0x7d05d4#64, 0x4e284aa3#32),        -- aese    v3.16b, v21.16b
    (0x7d05d8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d05dc#64, 0x2e261d08#32),        -- eor     v8.8b, v8.8b, v6.8b
    (0x7d05e0#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7d05e4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d05e8#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7d05ec#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d05f0#64, 0x6e251d6b#32),        -- eor     v11.16b, v11.16b, v5.16b
    (0x7d05f4#64, 0x0ef1e084#32),        -- pmull   v4.1q, v4.1d, v17.1d
    (0x7d05f8#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d05fc#64, 0x4e284b01#32),        -- aese    v1.16b, v24.16b
    (0x7d0600#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0604#64, 0x6e180508#32),        -- mov     v8.d[1], v8.d[0]
    (0x7d0608#64, 0x4e284b00#32),        -- aese    v0.16b, v24.16b
    (0x7d060c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0610#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d0614#64, 0x4e284ac3#32),        -- aese    v3.16b, v22.16b
    (0x7d0618#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d061c#64, 0x4e284b21#32),        -- aese    v1.16b, v25.16b
    (0x7d0620#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0624#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7d0628#64, 0x4e284b20#32),        -- aese    v0.16b, v25.16b
    (0x7d062c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0630#64, 0x4eede0c4#32),        -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7d0634#64, 0x5e1804e6#32),        -- mov     d6, v7.d[1]
    (0x7d0638#64, 0x4e284ae3#32),        -- aese    v3.16b, v23.16b
    (0x7d063c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0640#64, 0x4ef0e108#32),        -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7d0644#64, 0x4e284b40#32),        -- aese    v0.16b, v26.16b
    (0x7d0648#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d064c#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7d0650#64, 0x4e284b03#32),        -- aese    v3.16b, v24.16b
    (0x7d0654#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0658#64, 0x0eece0e4#32),        -- pmull   v4.1q, v7.1d, v12.1d
    (0x7d065c#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d0660#64, 0x6e281d4a#32),        -- eor     v10.16b, v10.16b, v8.16b
    (0x7d0664#64, 0x4eece0e5#32),        -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7d0668#64, 0xf100323f#32),        -- cmp     x17, #0xc
    (0x7d066c#64, 0x2e271cc6#32),        -- eor     v6.8b, v6.8b, v7.8b
    (0x7d0670#64, 0x4e284b41#32),        -- aese    v1.16b, v26.16b
    (0x7d0674#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0678#64, 0x4e284b02#32),        -- aese    v2.16b, v24.16b
    (0x7d067c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0680#64, 0x6e251d29#32),        -- eor     v9.16b, v9.16b, v5.16b
    (0x7d0684#64, 0x0ef0e0c6#32),        -- pmull   v6.1q, v6.1d, v16.1d
    (0x7d0688#64, 0x0f06e448#32),        -- movi    v8.8b, #0xc2
    (0x7d068c#64, 0x4e284b22#32),        -- aese    v2.16b, v25.16b
    (0x7d0690#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0694#64, 0x6e241d6b#32),        -- eor     v11.16b, v11.16b, v4.16b
    (0x7d0698#64, 0x4e284b23#32),        -- aese    v3.16b, v25.16b
    (0x7d069c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d06a0#64, 0x5f785508#32),        -- shl     d8, d8, #56
    (0x7d06a4#64, 0x4e284b42#32),        -- aese    v2.16b, v26.16b
    (0x7d06a8#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d06ac#64, 0x6e261d4a#32),        -- eor     v10.16b, v10.16b, v6.16b
    (0x7d06b0#64, 0x4e284b43#32),        -- aese    v3.16b, v26.16b
    (0x7d06b4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d06b8#64, 0x5400044b#32),        -- b.lt    7d0740 <.Ldec_main_loop_continue>  // b.tstop
    (0x7d06bc#64, 0x4e284b60#32),        -- aese    v0.16b, v27.16b
    (0x7d06c0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d06c4#64, 0x4e284b62#32),        -- aese    v2.16b, v27.16b
    (0x7d06c8#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d06cc#64, 0x4e284b61#32),        -- aese    v1.16b, v27.16b
    (0x7d06d0#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d06d4#64, 0x4e284b63#32),        -- aese    v3.16b, v27.16b
    (0x7d06d8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d06dc#64, 0x4e284b80#32),        -- aese    v0.16b, v28.16b
    (0x7d06e0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d06e4#64, 0x4e284b81#32),        -- aese    v1.16b, v28.16b
    (0x7d06e8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d06ec#64, 0x4e284b82#32),        -- aese    v2.16b, v28.16b
    (0x7d06f0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d06f4#64, 0x4e284b83#32),        -- aese    v3.16b, v28.16b
    (0x7d06f8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d06fc#64, 0x54000220#32),        -- b.eq    7d0740 <.Ldec_main_loop_continue>  // b.none
    (0x7d0700#64, 0x4e284ba0#32),        -- aese    v0.16b, v29.16b
    (0x7d0704#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0708#64, 0x4e284ba1#32),        -- aese    v1.16b, v29.16b
    (0x7d070c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0710#64, 0x4e284ba2#32),        -- aese    v2.16b, v29.16b
    (0x7d0714#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0718#64, 0x4e284ba3#32),        -- aese    v3.16b, v29.16b
    (0x7d071c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0720#64, 0x4e284bc0#32),        -- aese    v0.16b, v30.16b
    (0x7d0724#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0728#64, 0x4e284bc1#32),        -- aese    v1.16b, v30.16b
    (0x7d072c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0730#64, 0x4e284bc2#32),        -- aese    v2.16b, v30.16b
    (0x7d0734#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0738#64, 0x4e284bc3#32),        -- aese    v3.16b, v30.16b
    (0x7d073c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b

    -- 00000000007d0740 <.Ldec_main_loop_continue>:
    (0x7d0740#64, 0x0ee8e127#32),        -- pmull   v7.1q, v9.1d, v8.1d
    (0x7d0744#64, 0x6e291d66#32),        -- eor     v6.16b, v11.16b, v9.16b
    (0x7d0748#64, 0x3dc00004#32),        -- ldr     q4, [x0]
    (0x7d074c#64, 0x4e284be0#32),        -- aese    v0.16b, v31.16b
    (0x7d0750#64, 0x6e094129#32),        -- ext     v9.16b, v9.16b, v9.16b, #8
    (0x7d0754#64, 0x6e261d4a#32),        -- eor     v10.16b, v10.16b, v6.16b
    (0x7d0758#64, 0x3dc00405#32),        -- ldr     q5, [x0, #16]
    (0x7d075c#64, 0x6e201c80#32),        -- eor     v0.16b, v4.16b, v0.16b
    (0x7d0760#64, 0xa8816057#32),        -- stp     x23, x24, [x2], #16
    (0x7d0764#64, 0x6e271d4a#32),        -- eor     v10.16b, v10.16b, v7.16b
    (0x7d0768#64, 0x3dc00c07#32),        -- ldr     q7, [x0, #48]
    (0x7d076c#64, 0x3dc00806#32),        -- ldr     q6, [x0, #32]
    (0x7d0770#64, 0x4e183c07#32),        -- mov     x7, v0.d[1]
    (0x7d0774#64, 0x6e291d4a#32),        -- eor     v10.16b, v10.16b, v9.16b
    (0x7d0778#64, 0x4e284be1#32),        -- aese    v1.16b, v31.16b
    (0x7d077c#64, 0x91010000#32),        -- add     x0, x0, #0x40
    (0x7d0780#64, 0x4e083c06#32),        -- mov     x6, v0.d[0]
    (0x7d0784#64, 0x9e670140#32),        -- fmov    d0, x10
    (0x7d0788#64, 0x9eaf0120#32),        -- fmov    v0.d[1], x9
    (0x7d078c#64, 0x0ee8e148#32),        -- pmull   v8.1q, v10.1d, v8.1d
    (0x7d0790#64, 0x6e211ca1#32),        -- eor     v1.16b, v5.16b, v1.16b
    (0x7d0794#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d0798#64, 0x4e284be2#32),        -- aese    v2.16b, v31.16b
    (0x7d079c#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d07a0#64, 0xeb05001f#32),        -- cmp     x0, x5
    (0x7d07a4#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d07a8#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d07ac#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7d07b0#64, 0x4e183c34#32),        -- mov     x20, v1.d[1]
    (0x7d07b4#64, 0x6e221cc2#32),        -- eor     v2.16b, v6.16b, v2.16b
    (0x7d07b8#64, 0x6e281d6b#32),        -- eor     v11.16b, v11.16b, v8.16b
    (0x7d07bc#64, 0x4e083c33#32),        -- mov     x19, v1.d[0]
    (0x7d07c0#64, 0x9e670141#32),        -- fmov    d1, x10
    (0x7d07c4#64, 0x6e0a414a#32),        -- ext     v10.16b, v10.16b, v10.16b, #8
    (0x7d07c8#64, 0x9eaf0121#32),        -- fmov    v1.d[1], x9
    (0x7d07cc#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d07d0#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d07d4#64, 0x4e284be3#32),        -- aese    v3.16b, v31.16b
    (0x7d07d8#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d07dc#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7d07e0#64, 0xca0e0294#32),        -- eor     x20, x20, x14
    (0x7d07e4#64, 0xa8811c46#32),        -- stp     x6, x7, [x2], #16
    (0x7d07e8#64, 0xca0d0273#32),        -- eor     x19, x19, x13
    (0x7d07ec#64, 0xa8815053#32),        -- stp     x19, x20, [x2], #16
    (0x7d07f0#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7d07f4#64, 0x6e2a1d6b#32),        -- eor     v11.16b, v11.16b, v10.16b
    (0x7d07f8#64, 0x54ffe5cb#32),        -- b.lt    7d04b0 <.Ldec_main_loop>  // b.tstop

    -- 00000000007d07fc <.Ldec_prepretail>:
    (0x7d07fc#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7d0800#64, 0x4e083c55#32),        -- mov     x21, v2.d[0]
    (0x7d0804#64, 0x6e231ce3#32),        -- eor     v3.16b, v7.16b, v3.16b
    (0x7d0808#64, 0x4e284a40#32),        -- aese    v0.16b, v18.16b
    (0x7d080c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0810#64, 0x4e183c56#32),        -- mov     x22, v2.d[1]
    (0x7d0814#64, 0x4e284a41#32),        -- aese    v1.16b, v18.16b
    (0x7d0818#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d081c#64, 0x9e670142#32),        -- fmov    d2, x10
    (0x7d0820#64, 0x9eaf0122#32),        -- fmov    v2.d[1], x9
    (0x7d0824#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d0828#64, 0x6e2b1c84#32),        -- eor     v4.16b, v4.16b, v11.16b
    (0x7d082c#64, 0x4e2008c6#32),        -- rev64   v6.16b, v6.16b
    (0x7d0830#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7d0834#64, 0x4e083c77#32),        -- mov     x23, v3.d[0]
    (0x7d0838#64, 0x4e284a61#32),        -- aese    v1.16b, v19.16b
    (0x7d083c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0840#64, 0x4e183c78#32),        -- mov     x24, v3.d[1]
    (0x7d0844#64, 0x0eefe08b#32),        -- pmull   v11.1q, v4.1d, v15.1d
    (0x7d0848#64, 0x5e180488#32),        -- mov     d8, v4.d[1]
    (0x7d084c#64, 0x9e670143#32),        -- fmov    d3, x10
    (0x7d0850#64, 0x4eefe089#32),        -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7d0854#64, 0x9eaf0123#32),        -- fmov    v3.d[1], x9
    (0x7d0858#64, 0x4e284a42#32),        -- aese    v2.16b, v18.16b
    (0x7d085c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0860#64, 0x5e18062a#32),        -- mov     d10, v17.d[1]
    (0x7d0864#64, 0x4e284a60#32),        -- aese    v0.16b, v19.16b
    (0x7d0868#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d086c#64, 0x2e241d08#32),        -- eor     v8.8b, v8.8b, v4.8b
    (0x7d0870#64, 0x4eeee0a4#32),        -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7d0874#64, 0x4e284a62#32),        -- aese    v2.16b, v19.16b
    (0x7d0878#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d087c#64, 0x4e2008e7#32),        -- rev64   v7.16b, v7.16b
    (0x7d0880#64, 0x4e284a43#32),        -- aese    v3.16b, v18.16b
    (0x7d0884#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0888#64, 0x0eeae10a#32),        -- pmull   v10.1q, v8.1d, v10.1d
    (0x7d088c#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7d0890#64, 0x0eeee0a8#32),        -- pmull   v8.1q, v5.1d, v14.1d
    (0x7d0894#64, 0x4e284a63#32),        -- aese    v3.16b, v19.16b
    (0x7d0898#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d089c#64, 0x5e1804a4#32),        -- mov     d4, v5.d[1]
    (0x7d08a0#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7d08a4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d08a8#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7d08ac#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d08b0#64, 0x6e281d6b#32),        -- eor     v11.16b, v11.16b, v8.16b
    (0x7d08b4#64, 0x4e284a82#32),        -- aese    v2.16b, v20.16b
    (0x7d08b8#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d08bc#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7d08c0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d08c4#64, 0x5e1804c8#32),        -- mov     d8, v6.d[1]
    (0x7d08c8#64, 0x4e284a83#32),        -- aese    v3.16b, v20.16b
    (0x7d08cc#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d08d0#64, 0x2e251c84#32),        -- eor     v4.8b, v4.8b, v5.8b
    (0x7d08d4#64, 0x0eede0c5#32),        -- pmull   v5.1q, v6.1d, v13.1d
    (0x7d08d8#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7d08dc#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d08e0#64, 0x4e284aa3#32),        -- aese    v3.16b, v21.16b
    (0x7d08e4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d08e8#64, 0x2e261d08#32),        -- eor     v8.8b, v8.8b, v6.8b
    (0x7d08ec#64, 0x0ef1e084#32),        -- pmull   v4.1q, v4.1d, v17.1d
    (0x7d08f0#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7d08f4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d08f8#64, 0x6e251d6b#32),        -- eor     v11.16b, v11.16b, v5.16b
    (0x7d08fc#64, 0x4e284ac3#32),        -- aese    v3.16b, v22.16b
    (0x7d0900#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0904#64, 0x4eece0e5#32),        -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7d0908#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7d090c#64, 0x4eede0c4#32),        -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7d0910#64, 0x4e284ae3#32),        -- aese    v3.16b, v23.16b
    (0x7d0914#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0918#64, 0x6e180508#32),        -- mov     v8.d[1], v8.d[0]
    (0x7d091c#64, 0x4e284aa2#32),        -- aese    v2.16b, v21.16b
    (0x7d0920#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0924#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7d0928#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d092c#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7d0930#64, 0x0eece0e4#32),        -- pmull   v4.1q, v7.1d, v12.1d
    (0x7d0934#64, 0x4e284ac2#32),        -- aese    v2.16b, v22.16b
    (0x7d0938#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d093c#64, 0x5e1804e6#32),        -- mov     d6, v7.d[1]
    (0x7d0940#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7d0944#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0948#64, 0x4ef0e108#32),        -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7d094c#64, 0x4e284ae2#32),        -- aese    v2.16b, v23.16b
    (0x7d0950#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0954#64, 0x2e271cc6#32),        -- eor     v6.8b, v6.8b, v7.8b
    (0x7d0958#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7d095c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0960#64, 0x4e284b03#32),        -- aese    v3.16b, v24.16b
    (0x7d0964#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0968#64, 0x6e281d4a#32),        -- eor     v10.16b, v10.16b, v8.16b
    (0x7d096c#64, 0x4e284b02#32),        -- aese    v2.16b, v24.16b
    (0x7d0970#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0974#64, 0x4e284b00#32),        -- aese    v0.16b, v24.16b
    (0x7d0978#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d097c#64, 0x0f06e448#32),        -- movi    v8.8b, #0xc2
    (0x7d0980#64, 0x4e284b01#32),        -- aese    v1.16b, v24.16b
    (0x7d0984#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0988#64, 0x6e241d6b#32),        -- eor     v11.16b, v11.16b, v4.16b
    (0x7d098c#64, 0x0ef0e0c6#32),        -- pmull   v6.1q, v6.1d, v16.1d
    (0x7d0990#64, 0x4e284b23#32),        -- aese    v3.16b, v25.16b
    (0x7d0994#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0998#64, 0xf100323f#32),        -- cmp     x17, #0xc
    (0x7d099c#64, 0x6e251d29#32),        -- eor     v9.16b, v9.16b, v5.16b
    (0x7d09a0#64, 0x4e284b21#32),        -- aese    v1.16b, v25.16b
    (0x7d09a4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d09a8#64, 0x4e284b20#32),        -- aese    v0.16b, v25.16b
    (0x7d09ac#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d09b0#64, 0x6e261d4a#32),        -- eor     v10.16b, v10.16b, v6.16b
    (0x7d09b4#64, 0x4e284b43#32),        -- aese    v3.16b, v26.16b
    (0x7d09b8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d09bc#64, 0x4e284b22#32),        -- aese    v2.16b, v25.16b
    (0x7d09c0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d09c4#64, 0x6e291d66#32),        -- eor     v6.16b, v11.16b, v9.16b
    (0x7d09c8#64, 0x4e284b41#32),        -- aese    v1.16b, v26.16b
    (0x7d09cc#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d09d0#64, 0x4e284b40#32),        -- aese    v0.16b, v26.16b
    (0x7d09d4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d09d8#64, 0x5f785508#32),        -- shl     d8, d8, #56
    (0x7d09dc#64, 0x4e284b42#32),        -- aese    v2.16b, v26.16b
    (0x7d09e0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d09e4#64, 0x5400044b#32),        -- b.lt    7d0a6c <.Ldec_finish_prepretail>  // b.tstop
    (0x7d09e8#64, 0x4e284b61#32),        -- aese    v1.16b, v27.16b
    (0x7d09ec#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d09f0#64, 0x4e284b62#32),        -- aese    v2.16b, v27.16b
    (0x7d09f4#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d09f8#64, 0x4e284b63#32),        -- aese    v3.16b, v27.16b
    (0x7d09fc#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0a00#64, 0x4e284b60#32),        -- aese    v0.16b, v27.16b
    (0x7d0a04#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0a08#64, 0x4e284b82#32),        -- aese    v2.16b, v28.16b
    (0x7d0a0c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0a10#64, 0x4e284b83#32),        -- aese    v3.16b, v28.16b
    (0x7d0a14#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0a18#64, 0x4e284b80#32),        -- aese    v0.16b, v28.16b
    (0x7d0a1c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0a20#64, 0x4e284b81#32),        -- aese    v1.16b, v28.16b
    (0x7d0a24#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0a28#64, 0x54000220#32),        -- b.eq    7d0a6c <.Ldec_finish_prepretail>  // b.none
    (0x7d0a2c#64, 0x4e284ba2#32),        -- aese    v2.16b, v29.16b
    (0x7d0a30#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0a34#64, 0x4e284ba0#32),        -- aese    v0.16b, v29.16b
    (0x7d0a38#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0a3c#64, 0x4e284ba1#32),        -- aese    v1.16b, v29.16b
    (0x7d0a40#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0a44#64, 0x4e284bc2#32),        -- aese    v2.16b, v30.16b
    (0x7d0a48#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7d0a4c#64, 0x4e284ba3#32),        -- aese    v3.16b, v29.16b
    (0x7d0a50#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7d0a54#64, 0x4e284bc1#32),        -- aese    v1.16b, v30.16b
    (0x7d0a58#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7d0a5c#64, 0x4e284bc0#32),        -- aese    v0.16b, v30.16b
    (0x7d0a60#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7d0a64#64, 0x4e284bc3#32),        -- aese    v3.16b, v30.16b
    (0x7d0a68#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b

    -- 00000000007d0a6c <.Ldec_finish_prepretail>:
    (0x7d0a6c#64, 0x6e261d4a#32),        -- eor     v10.16b, v10.16b, v6.16b
    (0x7d0a70#64, 0x0ee8e127#32),        -- pmull   v7.1q, v9.1d, v8.1d
    (0x7d0a74#64, 0x6e094129#32),        -- ext     v9.16b, v9.16b, v9.16b, #8
    (0x7d0a78#64, 0x6e271d4a#32),        -- eor     v10.16b, v10.16b, v7.16b
    (0x7d0a7c#64, 0xca0e02d6#32),        -- eor     x22, x22, x14
    (0x7d0a80#64, 0xca0d02f7#32),        -- eor     x23, x23, x13
    (0x7d0a84#64, 0x6e291d4a#32),        -- eor     v10.16b, v10.16b, v9.16b
    (0x7d0a88#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7d0a8c#64, 0xca0d02b5#32),        -- eor     x21, x21, x13
    (0x7d0a90#64, 0x0ee8e148#32),        -- pmull   v8.1q, v10.1d, v8.1d
    (0x7d0a94#64, 0xca0e0318#32),        -- eor     x24, x24, x14
    (0x7d0a98#64, 0xa8815855#32),        -- stp     x21, x22, [x2], #16
    (0x7d0a9c#64, 0x6e0a414a#32),        -- ext     v10.16b, v10.16b, v10.16b, #8
    (0x7d0aa0#64, 0xa8816057#32),        -- stp     x23, x24, [x2], #16
    (0x7d0aa4#64, 0x6e281d6b#32),        -- eor     v11.16b, v11.16b, v8.16b
    (0x7d0aa8#64, 0x4e284be1#32),        -- aese    v1.16b, v31.16b
    (0x7d0aac#64, 0x4e284be0#32),        -- aese    v0.16b, v31.16b
    (0x7d0ab0#64, 0x4e284be3#32),        -- aese    v3.16b, v31.16b
    (0x7d0ab4#64, 0x4e284be2#32),        -- aese    v2.16b, v31.16b
    (0x7d0ab8#64, 0x6e2a1d6b#32),        -- eor     v11.16b, v11.16b, v10.16b

    -- 00000000007d0abc <.Ldec_tail>:
    (0x7d0abc#64, 0xcb000085#32),        -- sub     x5, x4, x0
    (0x7d0ac0#64, 0x4cdf7005#32),        -- ld1     {v5.16b}, [x0], #16
    (0x7d0ac4#64, 0x6e201ca0#32),        -- eor     v0.16b, v5.16b, v0.16b
    (0x7d0ac8#64, 0x4e083c06#32),        -- mov     x6, v0.d[0]
    (0x7d0acc#64, 0x4e183c07#32),        -- mov     x7, v0.d[1]
    (0x7d0ad0#64, 0x6e0b4168#32),        -- ext     v8.16b, v11.16b, v11.16b, #8
    (0x7d0ad4#64, 0xf100c0bf#32),        -- cmp     x5, #0x30
    (0x7d0ad8#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d0adc#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7d0ae0#64, 0x540001ec#32),        -- b.gt    7d0b1c <.Ldec_blocks_4_remaining>
    (0x7d0ae4#64, 0x5100058c#32),        -- sub     w12, w12, #0x1
    (0x7d0ae8#64, 0x4ea21c43#32),        -- mov     v3.16b, v2.16b
    (0x7d0aec#64, 0x0f00e40a#32),        -- movi    v10.8b, #0x0
    (0x7d0af0#64, 0x0f00e40b#32),        -- movi    v11.8b, #0x0
    (0x7d0af4#64, 0xf10080bf#32),        -- cmp     x5, #0x20
    (0x7d0af8#64, 0x0f00e409#32),        -- movi    v9.8b, #0x0
    (0x7d0afc#64, 0x4ea11c22#32),        -- mov     v2.16b, v1.16b
    (0x7d0b00#64, 0x540002ec#32),        -- b.gt    7d0b5c <.Ldec_blocks_3_remaining>
    (0x7d0b04#64, 0x5100058c#32),        -- sub     w12, w12, #0x1
    (0x7d0b08#64, 0x4ea11c23#32),        -- mov     v3.16b, v1.16b
    (0x7d0b0c#64, 0xf10040bf#32),        -- cmp     x5, #0x10
    (0x7d0b10#64, 0x540004ac#32),        -- b.gt    7d0ba4 <.Ldec_blocks_2_remaining>
    (0x7d0b14#64, 0x5100058c#32),        -- sub     w12, w12, #0x1
    (0x7d0b18#64, 0x14000036#32),        -- b       7d0bf0 <.Ldec_blocks_1_remaining>

    -- 00000000007d0b1c <.Ldec_blocks_4_remaining>:
    (0x7d0b1c#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7d0b20#64, 0x4cdf7005#32),        -- ld1     {v5.16b}, [x0], #16
    (0x7d0b24#64, 0xa8811c46#32),        -- stp     x6, x7, [x2], #16
    (0x7d0b28#64, 0x5e18062a#32),        -- mov     d10, v17.d[1]
    (0x7d0b2c#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7d0b30#64, 0x6e211ca0#32),        -- eor     v0.16b, v5.16b, v1.16b
    (0x7d0b34#64, 0x5e180496#32),        -- mov     d22, v4.d[1]
    (0x7d0b38#64, 0x4e083c06#32),        -- mov     x6, v0.d[0]
    (0x7d0b3c#64, 0x4e183c07#32),        -- mov     x7, v0.d[1]
    (0x7d0b40#64, 0x2e241ed6#32),        -- eor     v22.8b, v22.8b, v4.8b
    (0x7d0b44#64, 0x0f00e408#32),        -- movi    v8.8b, #0x0
    (0x7d0b48#64, 0x4eefe089#32),        -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7d0b4c#64, 0x0eeae2ca#32),        -- pmull   v10.1q, v22.1d, v10.1d
    (0x7d0b50#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d0b54#64, 0x0eefe08b#32),        -- pmull   v11.1q, v4.1d, v15.1d
    (0x7d0b58#64, 0xca0e00e7#32),        -- eor     x7, x7, x14

    -- 00000000007d0b5c <.Ldec_blocks_3_remaining>:
    (0x7d0b5c#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7d0b60#64, 0x4cdf7005#32),        -- ld1     {v5.16b}, [x0], #16
    (0x7d0b64#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7d0b68#64, 0xa8811c46#32),        -- stp     x6, x7, [x2], #16
    (0x7d0b6c#64, 0x6e221ca0#32),        -- eor     v0.16b, v5.16b, v2.16b
    (0x7d0b70#64, 0x5e180496#32),        -- mov     d22, v4.d[1]
    (0x7d0b74#64, 0x0eeee095#32),        -- pmull   v21.1q, v4.1d, v14.1d
    (0x7d0b78#64, 0x4eeee094#32),        -- pmull2  v20.1q, v4.2d, v14.2d
    (0x7d0b7c#64, 0x2e241ed6#32),        -- eor     v22.8b, v22.8b, v4.8b
    (0x7d0b80#64, 0x4e083c06#32),        -- mov     x6, v0.d[0]
    (0x7d0b84#64, 0x4e183c07#32),        -- mov     x7, v0.d[1]
    (0x7d0b88#64, 0x6e351d6b#32),        -- eor     v11.16b, v11.16b, v21.16b
    (0x7d0b8c#64, 0x0f00e408#32),        -- movi    v8.8b, #0x0
    (0x7d0b90#64, 0x0ef1e2d6#32),        -- pmull   v22.1q, v22.1d, v17.1d
    (0x7d0b94#64, 0x6e341d29#32),        -- eor     v9.16b, v9.16b, v20.16b
    (0x7d0b98#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d0b9c#64, 0x6e361d4a#32),        -- eor     v10.16b, v10.16b, v22.16b
    (0x7d0ba0#64, 0xca0e00e7#32),        -- eor     x7, x7, x14

    -- 00000000007d0ba4 <.Ldec_blocks_2_remaining>:
    (0x7d0ba4#64, 0xa8811c46#32),        -- stp     x6, x7, [x2], #16
    (0x7d0ba8#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7d0bac#64, 0x4cdf7005#32),        -- ld1     {v5.16b}, [x0], #16
    (0x7d0bb0#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7d0bb4#64, 0x0f00e408#32),        -- movi    v8.8b, #0x0
    (0x7d0bb8#64, 0x5e180496#32),        -- mov     d22, v4.d[1]
    (0x7d0bbc#64, 0x6e231ca0#32),        -- eor     v0.16b, v5.16b, v3.16b
    (0x7d0bc0#64, 0x4eede094#32),        -- pmull2  v20.1q, v4.2d, v13.2d
    (0x7d0bc4#64, 0x2e241ed6#32),        -- eor     v22.8b, v22.8b, v4.8b
    (0x7d0bc8#64, 0x0eede095#32),        -- pmull   v21.1q, v4.1d, v13.1d
    (0x7d0bcc#64, 0x4e083c06#32),        -- mov     x6, v0.d[0]
    (0x7d0bd0#64, 0x6e1806d6#32),        -- mov     v22.d[1], v22.d[0]
    (0x7d0bd4#64, 0x4e183c07#32),        -- mov     x7, v0.d[1]
    (0x7d0bd8#64, 0x4ef0e2d6#32),        -- pmull2  v22.1q, v22.2d, v16.2d
    (0x7d0bdc#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d0be0#64, 0x6e351d6b#32),        -- eor     v11.16b, v11.16b, v21.16b
    (0x7d0be4#64, 0x6e341d29#32),        -- eor     v9.16b, v9.16b, v20.16b
    (0x7d0be8#64, 0x6e361d4a#32),        -- eor     v10.16b, v10.16b, v22.16b
    (0x7d0bec#64, 0xca0e00e7#32),        -- eor     x7, x7, x14

    -- 00000000007d0bf0 <.Ldec_blocks_1_remaining>:
    (0x7d0bf0#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d0bf4#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7d0bf8#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7d0bfc#64, 0x0eece095#32),        -- pmull   v21.1q, v4.1d, v12.1d
    (0x7d0c00#64, 0x5e180488#32),        -- mov     d8, v4.d[1]
    (0x7d0c04#64, 0x2e241d08#32),        -- eor     v8.8b, v8.8b, v4.8b
    (0x7d0c08#64, 0x4eece094#32),        -- pmull2  v20.1q, v4.2d, v12.2d
    (0x7d0c0c#64, 0x0ef0e108#32),        -- pmull   v8.1q, v8.1d, v16.1d
    (0x7d0c10#64, 0x6e341d29#32),        -- eor     v9.16b, v9.16b, v20.16b
    (0x7d0c14#64, 0x6e351d6b#32),        -- eor     v11.16b, v11.16b, v21.16b
    (0x7d0c18#64, 0x6e281d4a#32),        -- eor     v10.16b, v10.16b, v8.16b
    (0x7d0c1c#64, 0x0f06e448#32),        -- movi    v8.8b, #0xc2
    (0x7d0c20#64, 0x6e291d66#32),        -- eor     v6.16b, v11.16b, v9.16b
    (0x7d0c24#64, 0x5f785508#32),        -- shl     d8, d8, #56
    (0x7d0c28#64, 0x6e261d4a#32),        -- eor     v10.16b, v10.16b, v6.16b
    (0x7d0c2c#64, 0x0ee8e127#32),        -- pmull   v7.1q, v9.1d, v8.1d
    (0x7d0c30#64, 0x6e094129#32),        -- ext     v9.16b, v9.16b, v9.16b, #8
    (0x7d0c34#64, 0x6e271d4a#32),        -- eor     v10.16b, v10.16b, v7.16b
    (0x7d0c38#64, 0x6e291d4a#32),        -- eor     v10.16b, v10.16b, v9.16b
    (0x7d0c3c#64, 0x0ee8e148#32),        -- pmull   v8.1q, v10.1d, v8.1d
    (0x7d0c40#64, 0x6e0a414a#32),        -- ext     v10.16b, v10.16b, v10.16b, #8
    (0x7d0c44#64, 0x6e281d6b#32),        -- eor     v11.16b, v11.16b, v8.16b
    (0x7d0c48#64, 0xa9001c46#32),        -- stp     x6, x7, [x2]
    (0x7d0c4c#64, 0xb9000e09#32),        -- str     w9, [x16, #12]
    (0x7d0c50#64, 0x6e2a1d6b#32),        -- eor     v11.16b, v11.16b, v10.16b
    (0x7d0c54#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7d0c58#64, 0x4e20096b#32),        -- rev64   v11.16b, v11.16b
    (0x7d0c5c#64, 0xaa0f03e0#32),        -- mov     x0, x15
    (0x7d0c60#64, 0x4c00706b#32),        -- st1     {v11.16b}, [x3]
    (0x7d0c64#64, 0xa94153f3#32),        -- ldp     x19, x20, [sp, #16]
    (0x7d0c68#64, 0xa9425bf5#32),        -- ldp     x21, x22, [sp, #32]
    (0x7d0c6c#64, 0xa94363f7#32),        -- ldp     x23, x24, [sp, #48]
    (0x7d0c70#64, 0x6d4427e8#32),        -- ldp     d8, d9, [sp, #64]
    (0x7d0c74#64, 0x6d452fea#32),        -- ldp     d10, d11, [sp, #80]
    (0x7d0c78#64, 0x6d4637ec#32),        -- ldp     d12, d13, [sp, #96]
    (0x7d0c7c#64, 0x6d473fee#32),        -- ldp     d14, d15, [sp, #112]
    (0x7d0c80#64, 0xa8c87bfd#32),        -- ldp     x29, x30, [sp], #128
    (0x7d0c84#64, 0xd65f03c0#32)         -- ret
  ]

end AESGCMDecKernelProgram
