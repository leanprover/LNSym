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
  [ -- 00000000007cf610 <aes_gcm_enc_kernel>:
    (0x7cf610#64, 0xa9b87bfd#32),        -- stp     x29, x30, [sp, #-128]!
    (0x7cf614#64, 0x910003fd#32),        -- mov     x29, sp
    (0x7cf618#64, 0xa90153f3#32),        -- stp     x19, x20, [sp, #16]
    (0x7cf61c#64, 0xaa0403f0#32),        -- mov     x16, x4
    (0x7cf620#64, 0xaa0503e8#32),        -- mov     x8, x5
    (0x7cf624#64, 0xa9025bf5#32),        -- stp     x21, x22, [sp, #32]
    (0x7cf628#64, 0xa90363f7#32),        -- stp     x23, x24, [sp, #48]
    (0x7cf62c#64, 0x6d0427e8#32),        -- stp     d8, d9, [sp, #64]
    (0x7cf630#64, 0x6d052fea#32),        -- stp     d10, d11, [sp, #80]
    (0x7cf634#64, 0x6d0637ec#32),        -- stp     d12, d13, [sp, #96]
    (0x7cf638#64, 0x6d073fee#32),        -- stp     d14, d15, [sp, #112]
    (0x7cf63c#64, 0xb940f111#32),        -- ldr     w17, [x8, #240]
    (0x7cf640#64, 0x8b111113#32),        -- add     x19, x8, x17, lsl #4
    (0x7cf644#64, 0xa9403a6d#32),        -- ldp     x13, x14, [x19]
    (0x7cf648#64, 0x3cdf027f#32),        -- ldur    q31, [x19, #-16]
    (0x7cf64c#64, 0x8b410c04#32),        -- add     x4, x0, x1, lsr #3
    (0x7cf650#64, 0xd343fc25#32),        -- lsr     x5, x1, #3
    (0x7cf654#64, 0xaa0503ef#32),        -- mov     x15, x5
    (0x7cf658#64, 0xa9402e0a#32),        -- ldp     x10, x11, [x16]
    (0x7cf65c#64, 0x4c407200#32),        -- ld1     {v0.16b}, [x16]
    (0x7cf660#64, 0xd10004a5#32),        -- sub     x5, x5, #0x1
    (0x7cf664#64, 0x3dc00112#32),        -- ldr     q18, [x8]
    (0x7cf668#64, 0x927ae4a5#32),        -- and     x5, x5, #0xffffffffffffffc0
    (0x7cf66c#64, 0x3dc01d19#32),        -- ldr     q25, [x8, #112]
    (0x7cf670#64, 0x8b0000a5#32),        -- add     x5, x5, x0
    (0x7cf674#64, 0xd360fd6c#32),        -- lsr     x12, x11, #32
    (0x7cf678#64, 0x9e670142#32),        -- fmov    d2, x10
    (0x7cf67c#64, 0x2a0b016b#32),        -- orr     w11, w11, w11
    (0x7cf680#64, 0x5ac0098c#32),        -- rev     w12, w12
    (0x7cf684#64, 0x9e670141#32),        -- fmov    d1, x10
    (0x7cf688#64, 0x4e284a40#32),        -- aese    v0.16b, v18.16b
    (0x7cf68c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf690#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cf694#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cf698#64, 0x9e670143#32),        -- fmov    d3, x10
    (0x7cf69c#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cf6a0#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cf6a4#64, 0x3dc00513#32),        -- ldr     q19, [x8, #16]
    (0x7cf6a8#64, 0x9eaf0121#32),        -- fmov    v1.d[1], x9
    (0x7cf6ac#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cf6b0#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cf6b4#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cf6b8#64, 0x3dc00914#32),        -- ldr     q20, [x8, #32]
    (0x7cf6bc#64, 0x9eaf0122#32),        -- fmov    v2.d[1], x9
    (0x7cf6c0#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cf6c4#64, 0x4e284a60#32),        -- aese    v0.16b, v19.16b
    (0x7cf6c8#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf6cc#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cf6d0#64, 0x9eaf0123#32),        -- fmov    v3.d[1], x9
    (0x7cf6d4#64, 0x4e284a41#32),        -- aese    v1.16b, v18.16b
    (0x7cf6d8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf6dc#64, 0x3dc00d15#32),        -- ldr     q21, [x8, #48]
    (0x7cf6e0#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7cf6e4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf6e8#64, 0x3dc01918#32),        -- ldr     q24, [x8, #96]
    (0x7cf6ec#64, 0x4e284a42#32),        -- aese    v2.16b, v18.16b
    (0x7cf6f0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf6f4#64, 0x3dc01517#32),        -- ldr     q23, [x8, #80]
    (0x7cf6f8#64, 0x4e284a61#32),        -- aese    v1.16b, v19.16b
    (0x7cf6fc#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf700#64, 0x3dc00cce#32),        -- ldr     q14, [x6, #48]
    (0x7cf704#64, 0x4e284a43#32),        -- aese    v3.16b, v18.16b
    (0x7cf708#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf70c#64, 0x4e284a62#32),        -- aese    v2.16b, v19.16b
    (0x7cf710#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf714#64, 0x3dc01116#32),        -- ldr     q22, [x8, #64]
    (0x7cf718#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7cf71c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf720#64, 0x3dc008cd#32),        -- ldr     q13, [x6, #32]
    (0x7cf724#64, 0x4e284a63#32),        -- aese    v3.16b, v19.16b
    (0x7cf728#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf72c#64, 0x3dc0311e#32),        -- ldr     q30, [x8, #192]
    (0x7cf730#64, 0x4e284a82#32),        -- aese    v2.16b, v20.16b
    (0x7cf734#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf738#64, 0x3dc014cf#32),        -- ldr     q15, [x6, #80]
    (0x7cf73c#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7cf740#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf744#64, 0x3dc02d1d#32),        -- ldr     q29, [x8, #176]
    (0x7cf748#64, 0x4e284a83#32),        -- aese    v3.16b, v20.16b
    (0x7cf74c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf750#64, 0x3dc0211a#32),        -- ldr     q26, [x8, #128]
    (0x7cf754#64, 0x4e284aa2#32),        -- aese    v2.16b, v21.16b
    (0x7cf758#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf75c#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cf760#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7cf764#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf768#64, 0x4e284aa3#32),        -- aese    v3.16b, v21.16b
    (0x7cf76c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf770#64, 0x4c40706b#32),        -- ld1     {v11.16b}, [x3]
    (0x7cf774#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7cf778#64, 0x4e20096b#32),        -- rev64   v11.16b, v11.16b
    (0x7cf77c#64, 0x4e284ac2#32),        -- aese    v2.16b, v22.16b
    (0x7cf780#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf784#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7cf788#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf78c#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7cf790#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf794#64, 0x4e284ac3#32),        -- aese    v3.16b, v22.16b
    (0x7cf798#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf79c#64, 0xf100323f#32),        -- cmp     x17, #0xc
    (0x7cf7a0#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7cf7a4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf7a8#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7cf7ac#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf7b0#64, 0x4e284ae3#32),        -- aese    v3.16b, v23.16b
    (0x7cf7b4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf7b8#64, 0x4e284ae2#32),        -- aese    v2.16b, v23.16b
    (0x7cf7bc#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf7c0#64, 0x4e284b01#32),        -- aese    v1.16b, v24.16b
    (0x7cf7c4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf7c8#64, 0x4ecf69d1#32),        -- trn2    v17.2d, v14.2d, v15.2d
    (0x7cf7cc#64, 0x4e284b03#32),        -- aese    v3.16b, v24.16b
    (0x7cf7d0#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf7d4#64, 0x3dc0251b#32),        -- ldr     q27, [x8, #144]
    (0x7cf7d8#64, 0x4e284b00#32),        -- aese    v0.16b, v24.16b
    (0x7cf7dc#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf7e0#64, 0x3dc000cc#32),        -- ldr     q12, [x6]
    (0x7cf7e4#64, 0x4e284b02#32),        -- aese    v2.16b, v24.16b
    (0x7cf7e8#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf7ec#64, 0x3dc0291c#32),        -- ldr     q28, [x8, #160]
    (0x7cf7f0#64, 0x4e284b21#32),        -- aese    v1.16b, v25.16b
    (0x7cf7f4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf7f8#64, 0x4ecf29c9#32),        -- trn1    v9.2d, v14.2d, v15.2d
    (0x7cf7fc#64, 0x4e284b20#32),        -- aese    v0.16b, v25.16b
    (0x7cf800#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf804#64, 0x4e284b22#32),        -- aese    v2.16b, v25.16b
    (0x7cf808#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf80c#64, 0x4e284b23#32),        -- aese    v3.16b, v25.16b
    (0x7cf810#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf814#64, 0x4ecd6990#32),        -- trn2    v16.2d, v12.2d, v13.2d
    (0x7cf818#64, 0x4e284b41#32),        -- aese    v1.16b, v26.16b
    (0x7cf81c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf820#64, 0x4e284b42#32),        -- aese    v2.16b, v26.16b
    (0x7cf824#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf828#64, 0x4e284b43#32),        -- aese    v3.16b, v26.16b
    (0x7cf82c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf830#64, 0x4e284b40#32),        -- aese    v0.16b, v26.16b
    (0x7cf834#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf838#64, 0x5400044b#32),        -- b.lt    7cf8c0 <.Lenc_finish_first_blocks>  // b.tstop
    (0x7cf83c#64, 0x4e284b61#32),        -- aese    v1.16b, v27.16b
    (0x7cf840#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf844#64, 0x4e284b62#32),        -- aese    v2.16b, v27.16b
    (0x7cf848#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf84c#64, 0x4e284b63#32),        -- aese    v3.16b, v27.16b
    (0x7cf850#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf854#64, 0x4e284b60#32),        -- aese    v0.16b, v27.16b
    (0x7cf858#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf85c#64, 0x4e284b81#32),        -- aese    v1.16b, v28.16b
    (0x7cf860#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf864#64, 0x4e284b82#32),        -- aese    v2.16b, v28.16b
    (0x7cf868#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf86c#64, 0x4e284b83#32),        -- aese    v3.16b, v28.16b
    (0x7cf870#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf874#64, 0x4e284b80#32),        -- aese    v0.16b, v28.16b
    (0x7cf878#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf87c#64, 0x54000220#32),        -- b.eq    7cf8c0 <.Lenc_finish_first_blocks>  // b.none
    (0x7cf880#64, 0x4e284ba1#32),        -- aese    v1.16b, v29.16b
    (0x7cf884#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf888#64, 0x4e284ba2#32),        -- aese    v2.16b, v29.16b
    (0x7cf88c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf890#64, 0x4e284ba0#32),        -- aese    v0.16b, v29.16b
    (0x7cf894#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf898#64, 0x4e284ba3#32),        -- aese    v3.16b, v29.16b
    (0x7cf89c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cf8a0#64, 0x4e284bc1#32),        -- aese    v1.16b, v30.16b
    (0x7cf8a4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf8a8#64, 0x4e284bc2#32),        -- aese    v2.16b, v30.16b
    (0x7cf8ac#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf8b0#64, 0x4e284bc0#32),        -- aese    v0.16b, v30.16b
    (0x7cf8b4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf8b8#64, 0x4e284bc3#32),        -- aese    v3.16b, v30.16b
    (0x7cf8bc#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b

    -- 00000000007cf8c0 <.Lenc_finish_first_blocks>:
    (0x7cf8c0#64, 0xeb05001f#32),        -- cmp     x0, x5
    (0x7cf8c4#64, 0x6e291e31#32),        -- eor     v17.16b, v17.16b, v9.16b
    (0x7cf8c8#64, 0x4e284be2#32),        -- aese    v2.16b, v31.16b
    (0x7cf8cc#64, 0x4ecd2988#32),        -- trn1    v8.2d, v12.2d, v13.2d
    (0x7cf8d0#64, 0x4e284be1#32),        -- aese    v1.16b, v31.16b
    (0x7cf8d4#64, 0x4e284be0#32),        -- aese    v0.16b, v31.16b
    (0x7cf8d8#64, 0x4e284be3#32),        -- aese    v3.16b, v31.16b
    (0x7cf8dc#64, 0x6e281e10#32),        -- eor     v16.16b, v16.16b, v8.16b
    (0x7cf8e0#64, 0x540034ea#32),        -- b.ge    7cff7c <.Lenc_tail>  // b.tcont
    (0x7cf8e4#64, 0xa9415013#32),        -- ldp     x19, x20, [x0, #16]
    (0x7cf8e8#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cf8ec#64, 0xa9401c06#32),        -- ldp     x6, x7, [x0]
    (0x7cf8f0#64, 0xa9436017#32),        -- ldp     x23, x24, [x0, #48]
    (0x7cf8f4#64, 0xa9425815#32),        -- ldp     x21, x22, [x0, #32]
    (0x7cf8f8#64, 0x91010000#32),        -- add     x0, x0, #0x40
    (0x7cf8fc#64, 0xca0d0273#32),        -- eor     x19, x19, x13
    (0x7cf900#64, 0xca0e0294#32),        -- eor     x20, x20, x14
    (0x7cf904#64, 0x9e670265#32),        -- fmov    d5, x19
    (0x7cf908#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7cf90c#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7cf910#64, 0xca0e0318#32),        -- eor     x24, x24, x14
    (0x7cf914#64, 0x9e6700c4#32),        -- fmov    d4, x6
    (0x7cf918#64, 0xeb05001f#32),        -- cmp     x0, x5
    (0x7cf91c#64, 0x9eaf00e4#32),        -- fmov    v4.d[1], x7
    (0x7cf920#64, 0xca0d02f7#32),        -- eor     x23, x23, x13
    (0x7cf924#64, 0xca0d02b5#32),        -- eor     x21, x21, x13
    (0x7cf928#64, 0x9eaf0285#32),        -- fmov    v5.d[1], x20
    (0x7cf92c#64, 0x9e6702a6#32),        -- fmov    d6, x21
    (0x7cf930#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cf934#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cf938#64, 0x9e6702e7#32),        -- fmov    d7, x23
    (0x7cf93c#64, 0xca0e02d6#32),        -- eor     x22, x22, x14
    (0x7cf940#64, 0x9eaf02c6#32),        -- fmov    v6.d[1], x22
    (0x7cf944#64, 0x6e201c84#32),        -- eor     v4.16b, v4.16b, v0.16b
    (0x7cf948#64, 0x9e670140#32),        -- fmov    d0, x10
    (0x7cf94c#64, 0x9eaf0120#32),        -- fmov    v0.d[1], x9
    (0x7cf950#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cf954#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cf958#64, 0x6e211ca5#32),        -- eor     v5.16b, v5.16b, v1.16b
    (0x7cf95c#64, 0x9e670141#32),        -- fmov    d1, x10
    (0x7cf960#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cf964#64, 0x9eaf0121#32),        -- fmov    v1.d[1], x9
    (0x7cf968#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cf96c#64, 0x4c9f7044#32),        -- st1     {v4.16b}, [x2], #16
    (0x7cf970#64, 0x9eaf0307#32),        -- fmov    v7.d[1], x24
    (0x7cf974#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cf978#64, 0x6e221cc6#32),        -- eor     v6.16b, v6.16b, v2.16b
    (0x7cf97c#64, 0x4c9f7045#32),        -- st1     {v5.16b}, [x2], #16
    (0x7cf980#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cf984#64, 0x9e670142#32),        -- fmov    d2, x10
    (0x7cf988#64, 0x9eaf0122#32),        -- fmov    v2.d[1], x9
    (0x7cf98c#64, 0x4c9f7046#32),        -- st1     {v6.16b}, [x2], #16
    (0x7cf990#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cf994#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cf998#64, 0x6e231ce7#32),        -- eor     v7.16b, v7.16b, v3.16b
    (0x7cf99c#64, 0x4c9f7047#32),        -- st1     {v7.16b}, [x2], #16
    (0x7cf9a0#64, 0x54001a8a#32),        -- b.ge    7cfcf0 <.Lenc_prepretail>  // b.tcont

    -- 00000000007cf9a4 <.Lenc_main_loop>:
    (0x7cf9a4#64, 0x4e284a40#32),        -- aese    v0.16b, v18.16b
    (0x7cf9a8#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf9ac#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7cf9b0#64, 0x4e284a41#32),        -- aese    v1.16b, v18.16b
    (0x7cf9b4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf9b8#64, 0x9e670143#32),        -- fmov    d3, x10
    (0x7cf9bc#64, 0x4e284a42#32),        -- aese    v2.16b, v18.16b
    (0x7cf9c0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf9c4#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7cf9c8#64, 0x4e284a60#32),        -- aese    v0.16b, v19.16b
    (0x7cf9cc#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf9d0#64, 0x9eaf0123#32),        -- fmov    v3.d[1], x9
    (0x7cf9d4#64, 0x4e284a61#32),        -- aese    v1.16b, v19.16b
    (0x7cf9d8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cf9dc#64, 0xa9436017#32),        -- ldp     x23, x24, [x0, #48]
    (0x7cf9e0#64, 0x4e284a62#32),        -- aese    v2.16b, v19.16b
    (0x7cf9e4#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cf9e8#64, 0xa9425815#32),        -- ldp     x21, x22, [x0, #32]
    (0x7cf9ec#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7cf9f0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cf9f4#64, 0x6e2b1c84#32),        -- eor     v4.16b, v4.16b, v11.16b
    (0x7cf9f8#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7cf9fc#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfa00#64, 0x4e284a43#32),        -- aese    v3.16b, v18.16b
    (0x7cfa04#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfa08#64, 0xca0d02f7#32),        -- eor     x23, x23, x13
    (0x7cfa0c#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7cfa10#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfa14#64, 0x5e18062a#32),        -- mov     d10, v17.d[1]
    (0x7cfa18#64, 0x4eefe089#32),        -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7cfa1c#64, 0xca0e02d6#32),        -- eor     x22, x22, x14
    (0x7cfa20#64, 0x5e180488#32),        -- mov     d8, v4.d[1]
    (0x7cfa24#64, 0x4e284a63#32),        -- aese    v3.16b, v19.16b
    (0x7cfa28#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfa2c#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7cfa30#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7cfa34#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfa38#64, 0x0eefe08b#32),        -- pmull   v11.1q, v4.1d, v15.1d
    (0x7cfa3c#64, 0x2e241d08#32),        -- eor     v8.8b, v8.8b, v4.8b
    (0x7cfa40#64, 0x4e284a82#32),        -- aese    v2.16b, v20.16b
    (0x7cfa44#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfa48#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7cfa4c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfa50#64, 0x4e2008e7#32),        -- rev64   v7.16b, v7.16b
    (0x7cfa54#64, 0x4eeee0a4#32),        -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7cfa58#64, 0x0eeae10a#32),        -- pmull   v10.1q, v8.1d, v10.1d
    (0x7cfa5c#64, 0x4e2008c6#32),        -- rev64   v6.16b, v6.16b
    (0x7cfa60#64, 0x0eeee0a8#32),        -- pmull   v8.1q, v5.1d, v14.1d
    (0x7cfa64#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7cfa68#64, 0x5e1804a4#32),        -- mov     d4, v5.d[1]
    (0x7cfa6c#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7cfa70#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfa74#64, 0x4e284a83#32),        -- aese    v3.16b, v20.16b
    (0x7cfa78#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfa7c#64, 0x6e281d6b#32),        -- eor     v11.16b, v11.16b, v8.16b
    (0x7cfa80#64, 0x4e284aa2#32),        -- aese    v2.16b, v21.16b
    (0x7cfa84#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfa88#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7cfa8c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfa90#64, 0x5e1804c8#32),        -- mov     d8, v6.d[1]
    (0x7cfa94#64, 0x4e284aa3#32),        -- aese    v3.16b, v21.16b
    (0x7cfa98#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfa9c#64, 0x2e251c84#32),        -- eor     v4.8b, v4.8b, v5.8b
    (0x7cfaa0#64, 0x4e284ac2#32),        -- aese    v2.16b, v22.16b
    (0x7cfaa4#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfaa8#64, 0x4e284b00#32),        -- aese    v0.16b, v24.16b
    (0x7cfaac#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfab0#64, 0x2e261d08#32),        -- eor     v8.8b, v8.8b, v6.8b
    (0x7cfab4#64, 0x4e284ac3#32),        -- aese    v3.16b, v22.16b
    (0x7cfab8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfabc#64, 0x0ef1e084#32),        -- pmull   v4.1q, v4.1d, v17.1d
    (0x7cfac0#64, 0x4e284b20#32),        -- aese    v0.16b, v25.16b
    (0x7cfac4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfac8#64, 0x4e284ae3#32),        -- aese    v3.16b, v23.16b
    (0x7cfacc#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfad0#64, 0x6e180508#32),        -- mov     v8.d[1], v8.d[0]
    (0x7cfad4#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7cfad8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfadc#64, 0x4e284b40#32),        -- aese    v0.16b, v26.16b
    (0x7cfae0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfae4#64, 0x4e284ae2#32),        -- aese    v2.16b, v23.16b
    (0x7cfae8#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfaec#64, 0x4e284b01#32),        -- aese    v1.16b, v24.16b
    (0x7cfaf0#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfaf4#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7cfaf8#64, 0x4eede0c4#32),        -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7cfafc#64, 0x0eede0c5#32),        -- pmull   v5.1q, v6.1d, v13.1d
    (0x7cfb00#64, 0x4e284b21#32),        -- aese    v1.16b, v25.16b
    (0x7cfb04#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfb08#64, 0x0eece0e6#32),        -- pmull   v6.1q, v7.1d, v12.1d
    (0x7cfb0c#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7cfb10#64, 0x4e284b03#32),        -- aese    v3.16b, v24.16b
    (0x7cfb14#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfb18#64, 0xa9415013#32),        -- ldp     x19, x20, [x0, #16]
    (0x7cfb1c#64, 0x4e284b41#32),        -- aese    v1.16b, v26.16b
    (0x7cfb20#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfb24#64, 0x5e1804e4#32),        -- mov     d4, v7.d[1]
    (0x7cfb28#64, 0x4e284b02#32),        -- aese    v2.16b, v24.16b
    (0x7cfb2c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfb30#64, 0x6e251d6b#32),        -- eor     v11.16b, v11.16b, v5.16b
    (0x7cfb34#64, 0x4ef0e108#32),        -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7cfb38#64, 0x4eece0e5#32),        -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7cfb3c#64, 0x2e271c84#32),        -- eor     v4.8b, v4.8b, v7.8b
    (0x7cfb40#64, 0x4e284b22#32),        -- aese    v2.16b, v25.16b
    (0x7cfb44#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfb48#64, 0xca0d0273#32),        -- eor     x19, x19, x13
    (0x7cfb4c#64, 0x4e284b42#32),        -- aese    v2.16b, v26.16b
    (0x7cfb50#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfb54#64, 0x6e281d4a#32),        -- eor     v10.16b, v10.16b, v8.16b
    (0x7cfb58#64, 0x4e284b23#32),        -- aese    v3.16b, v25.16b
    (0x7cfb5c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfb60#64, 0xca0d02b5#32),        -- eor     x21, x21, x13
    (0x7cfb64#64, 0x4e284b43#32),        -- aese    v3.16b, v26.16b
    (0x7cfb68#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfb6c#64, 0x0f06e448#32),        -- movi    v8.8b, #0xc2
    (0x7cfb70#64, 0x0ef0e084#32),        -- pmull   v4.1q, v4.1d, v16.1d
    (0x7cfb74#64, 0x6e251d29#32),        -- eor     v9.16b, v9.16b, v5.16b
    (0x7cfb78#64, 0xf100323f#32),        -- cmp     x17, #0xc
    (0x7cfb7c#64, 0x9e670265#32),        -- fmov    d5, x19
    (0x7cfb80#64, 0xa9401c06#32),        -- ldp     x6, x7, [x0]
    (0x7cfb84#64, 0x5400044b#32),        -- b.lt    7cfc0c <.Lenc_main_loop_continue>  // b.tstop
    (0x7cfb88#64, 0x4e284b61#32),        -- aese    v1.16b, v27.16b
    (0x7cfb8c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfb90#64, 0x4e284b60#32),        -- aese    v0.16b, v27.16b
    (0x7cfb94#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfb98#64, 0x4e284b62#32),        -- aese    v2.16b, v27.16b
    (0x7cfb9c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfba0#64, 0x4e284b63#32),        -- aese    v3.16b, v27.16b
    (0x7cfba4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfba8#64, 0x4e284b80#32),        -- aese    v0.16b, v28.16b
    (0x7cfbac#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfbb0#64, 0x4e284b81#32),        -- aese    v1.16b, v28.16b
    (0x7cfbb4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfbb8#64, 0x4e284b82#32),        -- aese    v2.16b, v28.16b
    (0x7cfbbc#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfbc0#64, 0x4e284b83#32),        -- aese    v3.16b, v28.16b
    (0x7cfbc4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfbc8#64, 0x54000220#32),        -- b.eq    7cfc0c <.Lenc_main_loop_continue>  // b.none
    (0x7cfbcc#64, 0x4e284ba0#32),        -- aese    v0.16b, v29.16b
    (0x7cfbd0#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfbd4#64, 0x4e284ba1#32),        -- aese    v1.16b, v29.16b
    (0x7cfbd8#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfbdc#64, 0x4e284ba2#32),        -- aese    v2.16b, v29.16b
    (0x7cfbe0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfbe4#64, 0x4e284ba3#32),        -- aese    v3.16b, v29.16b
    (0x7cfbe8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfbec#64, 0x4e284bc1#32),        -- aese    v1.16b, v30.16b
    (0x7cfbf0#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfbf4#64, 0x4e284bc0#32),        -- aese    v0.16b, v30.16b
    (0x7cfbf8#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfbfc#64, 0x4e284bc2#32),        -- aese    v2.16b, v30.16b
    (0x7cfc00#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfc04#64, 0x4e284bc3#32),        -- aese    v3.16b, v30.16b
    (0x7cfc08#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b

    -- 00000000007cfc0c <.Lenc_main_loop_continue>:
    (0x7cfc0c#64, 0x5f785508#32),        -- shl     d8, d8, #56
    (0x7cfc10#64, 0x6e261d6b#32),        -- eor     v11.16b, v11.16b, v6.16b
    (0x7cfc14#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7cfc18#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cfc1c#64, 0x6e291d64#32),        -- eor     v4.16b, v11.16b, v9.16b
    (0x7cfc20#64, 0x91010000#32),        -- add     x0, x0, #0x40
    (0x7cfc24#64, 0x0ee8e127#32),        -- pmull   v7.1q, v9.1d, v8.1d
    (0x7cfc28#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cfc2c#64, 0x6e094129#32),        -- ext     v9.16b, v9.16b, v9.16b, #8
    (0x7cfc30#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7cfc34#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7cfc38#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7cfc3c#64, 0x9e6700c4#32),        -- fmov    d4, x6
    (0x7cfc40#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cfc44#64, 0x6e271d27#32),        -- eor     v7.16b, v9.16b, v7.16b
    (0x7cfc48#64, 0xca0e0294#32),        -- eor     x20, x20, x14
    (0x7cfc4c#64, 0xca0e0318#32),        -- eor     x24, x24, x14
    (0x7cfc50#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cfc54#64, 0x4e284be0#32),        -- aese    v0.16b, v31.16b
    (0x7cfc58#64, 0x9eaf00e4#32),        -- fmov    v4.d[1], x7
    (0x7cfc5c#64, 0x6e271d4a#32),        -- eor     v10.16b, v10.16b, v7.16b
    (0x7cfc60#64, 0x9e6702e7#32),        -- fmov    d7, x23
    (0x7cfc64#64, 0x4e284be1#32),        -- aese    v1.16b, v31.16b
    (0x7cfc68#64, 0x9eaf0285#32),        -- fmov    v5.d[1], x20
    (0x7cfc6c#64, 0x9e6702a6#32),        -- fmov    d6, x21
    (0x7cfc70#64, 0xeb05001f#32),        -- cmp     x0, x5
    (0x7cfc74#64, 0x9eaf02c6#32),        -- fmov    v6.d[1], x22
    (0x7cfc78#64, 0x0ee8e149#32),        -- pmull   v9.1q, v10.1d, v8.1d
    (0x7cfc7c#64, 0x6e201c84#32),        -- eor     v4.16b, v4.16b, v0.16b
    (0x7cfc80#64, 0x9e670140#32),        -- fmov    d0, x10
    (0x7cfc84#64, 0x9eaf0120#32),        -- fmov    v0.d[1], x9
    (0x7cfc88#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cfc8c#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cfc90#64, 0x6e211ca5#32),        -- eor     v5.16b, v5.16b, v1.16b
    (0x7cfc94#64, 0x9e670141#32),        -- fmov    d1, x10
    (0x7cfc98#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cfc9c#64, 0x9eaf0121#32),        -- fmov    v1.d[1], x9
    (0x7cfca0#64, 0x4e284be2#32),        -- aese    v2.16b, v31.16b
    (0x7cfca4#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cfca8#64, 0x4c9f7044#32),        -- st1     {v4.16b}, [x2], #16
    (0x7cfcac#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cfcb0#64, 0x6e291d6b#32),        -- eor     v11.16b, v11.16b, v9.16b
    (0x7cfcb4#64, 0x9eaf0307#32),        -- fmov    v7.d[1], x24
    (0x7cfcb8#64, 0x6e0a414a#32),        -- ext     v10.16b, v10.16b, v10.16b, #8
    (0x7cfcbc#64, 0x4c9f7045#32),        -- st1     {v5.16b}, [x2], #16
    (0x7cfcc0#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cfcc4#64, 0x4e284be3#32),        -- aese    v3.16b, v31.16b
    (0x7cfcc8#64, 0x6e221cc6#32),        -- eor     v6.16b, v6.16b, v2.16b
    (0x7cfccc#64, 0x9e670142#32),        -- fmov    d2, x10
    (0x7cfcd0#64, 0x4c9f7046#32),        -- st1     {v6.16b}, [x2], #16
    (0x7cfcd4#64, 0x9eaf0122#32),        -- fmov    v2.d[1], x9
    (0x7cfcd8#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7cfcdc#64, 0x6e2a1d6b#32),        -- eor     v11.16b, v11.16b, v10.16b
    (0x7cfce0#64, 0xaa098169#32),        -- orr     x9, x11, x9, lsl #32
    (0x7cfce4#64, 0x6e231ce7#32),        -- eor     v7.16b, v7.16b, v3.16b
    (0x7cfce8#64, 0x4c9f7047#32),        -- st1     {v7.16b}, [x2], #16
    (0x7cfcec#64, 0x54ffe5cb#32),        -- b.lt    7cf9a4 <.Lenc_main_loop>  // b.tstop

    -- 00000000007cfcf0 <.Lenc_prepretail>:
    (0x7cfcf0#64, 0x4e284a41#32),        -- aese    v1.16b, v18.16b
    (0x7cfcf4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfcf8#64, 0x4e2008c6#32),        -- rev64   v6.16b, v6.16b
    (0x7cfcfc#64, 0x4e284a42#32),        -- aese    v2.16b, v18.16b
    (0x7cfd00#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfd04#64, 0x9e670143#32),        -- fmov    d3, x10
    (0x7cfd08#64, 0x4e284a40#32),        -- aese    v0.16b, v18.16b
    (0x7cfd0c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfd10#64, 0x4e200884#32),        -- rev64   v4.16b, v4.16b
    (0x7cfd14#64, 0x9eaf0123#32),        -- fmov    v3.d[1], x9
    (0x7cfd18#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7cfd1c#64, 0x4e284a62#32),        -- aese    v2.16b, v19.16b
    (0x7cfd20#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfd24#64, 0x4e284a60#32),        -- aese    v0.16b, v19.16b
    (0x7cfd28#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfd2c#64, 0x6e2b1c84#32),        -- eor     v4.16b, v4.16b, v11.16b
    (0x7cfd30#64, 0x4e2008a5#32),        -- rev64   v5.16b, v5.16b
    (0x7cfd34#64, 0x4e284a82#32),        -- aese    v2.16b, v20.16b
    (0x7cfd38#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfd3c#64, 0x4e284a43#32),        -- aese    v3.16b, v18.16b
    (0x7cfd40#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfd44#64, 0x5e18062a#32),        -- mov     d10, v17.d[1]
    (0x7cfd48#64, 0x4e284a61#32),        -- aese    v1.16b, v19.16b
    (0x7cfd4c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfd50#64, 0x0eefe08b#32),        -- pmull   v11.1q, v4.1d, v15.1d
    (0x7cfd54#64, 0x5e180488#32),        -- mov     d8, v4.d[1]
    (0x7cfd58#64, 0x4eefe089#32),        -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7cfd5c#64, 0x4e284aa2#32),        -- aese    v2.16b, v21.16b
    (0x7cfd60#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfd64#64, 0x4e284a81#32),        -- aese    v1.16b, v20.16b
    (0x7cfd68#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfd6c#64, 0x2e241d08#32),        -- eor     v8.8b, v8.8b, v4.8b
    (0x7cfd70#64, 0x4e284a80#32),        -- aese    v0.16b, v20.16b
    (0x7cfd74#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfd78#64, 0x4e284a63#32),        -- aese    v3.16b, v19.16b
    (0x7cfd7c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfd80#64, 0x4e284aa1#32),        -- aese    v1.16b, v21.16b
    (0x7cfd84#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfd88#64, 0x0eeae10a#32),        -- pmull   v10.1q, v8.1d, v10.1d
    (0x7cfd8c#64, 0x4eeee0a4#32),        -- pmull2  v4.1q, v5.2d, v14.2d
    (0x7cfd90#64, 0x0eeee0a8#32),        -- pmull   v8.1q, v5.1d, v14.1d
    (0x7cfd94#64, 0x4e284a83#32),        -- aese    v3.16b, v20.16b
    (0x7cfd98#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfd9c#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7cfda0#64, 0x5e1804a4#32),        -- mov     d4, v5.d[1]
    (0x7cfda4#64, 0x4e284aa0#32),        -- aese    v0.16b, v21.16b
    (0x7cfda8#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfdac#64, 0x6e281d6b#32),        -- eor     v11.16b, v11.16b, v8.16b
    (0x7cfdb0#64, 0x4e284aa3#32),        -- aese    v3.16b, v21.16b
    (0x7cfdb4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfdb8#64, 0x2e251c84#32),        -- eor     v4.8b, v4.8b, v5.8b
    (0x7cfdbc#64, 0x5e1804c8#32),        -- mov     d8, v6.d[1]
    (0x7cfdc0#64, 0x4e284ac0#32),        -- aese    v0.16b, v22.16b
    (0x7cfdc4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfdc8#64, 0x4e2008e7#32),        -- rev64   v7.16b, v7.16b
    (0x7cfdcc#64, 0x4e284ac3#32),        -- aese    v3.16b, v22.16b
    (0x7cfdd0#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfdd4#64, 0x0ef1e084#32),        -- pmull   v4.1q, v4.1d, v17.1d
    (0x7cfdd8#64, 0x2e261d08#32),        -- eor     v8.8b, v8.8b, v6.8b
    (0x7cfddc#64, 0x1100058c#32),        -- add     w12, w12, #0x1
    (0x7cfde0#64, 0x0eede0c5#32),        -- pmull   v5.1q, v6.1d, v13.1d
    (0x7cfde4#64, 0x4e284ae3#32),        -- aese    v3.16b, v23.16b
    (0x7cfde8#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfdec#64, 0x4e284ac2#32),        -- aese    v2.16b, v22.16b
    (0x7cfdf0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfdf4#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7cfdf8#64, 0x4eede0c4#32),        -- pmull2  v4.1q, v6.2d, v13.2d
    (0x7cfdfc#64, 0x6e251d6b#32),        -- eor     v11.16b, v11.16b, v5.16b
    (0x7cfe00#64, 0x6e180508#32),        -- mov     v8.d[1], v8.d[0]
    (0x7cfe04#64, 0x4e284ae2#32),        -- aese    v2.16b, v23.16b
    (0x7cfe08#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfe0c#64, 0x6e241d29#32),        -- eor     v9.16b, v9.16b, v4.16b
    (0x7cfe10#64, 0x5e1804e4#32),        -- mov     d4, v7.d[1]
    (0x7cfe14#64, 0x4e284ac1#32),        -- aese    v1.16b, v22.16b
    (0x7cfe18#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfe1c#64, 0x4ef0e108#32),        -- pmull2  v8.1q, v8.2d, v16.2d
    (0x7cfe20#64, 0x2e271c84#32),        -- eor     v4.8b, v4.8b, v7.8b
    (0x7cfe24#64, 0x4eece0e5#32),        -- pmull2  v5.1q, v7.2d, v12.2d
    (0x7cfe28#64, 0x4e284ae1#32),        -- aese    v1.16b, v23.16b
    (0x7cfe2c#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfe30#64, 0x0ef0e084#32),        -- pmull   v4.1q, v4.1d, v16.1d
    (0x7cfe34#64, 0x6e281d4a#32),        -- eor     v10.16b, v10.16b, v8.16b
    (0x7cfe38#64, 0x4e284ae0#32),        -- aese    v0.16b, v23.16b
    (0x7cfe3c#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfe40#64, 0x4e284b01#32),        -- aese    v1.16b, v24.16b
    (0x7cfe44#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfe48#64, 0x4e284b02#32),        -- aese    v2.16b, v24.16b
    (0x7cfe4c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfe50#64, 0x4e284b00#32),        -- aese    v0.16b, v24.16b
    (0x7cfe54#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfe58#64, 0x0f06e448#32),        -- movi    v8.8b, #0xc2
    (0x7cfe5c#64, 0x4e284b03#32),        -- aese    v3.16b, v24.16b
    (0x7cfe60#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfe64#64, 0x4e284b21#32),        -- aese    v1.16b, v25.16b
    (0x7cfe68#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfe6c#64, 0x6e251d29#32),        -- eor     v9.16b, v9.16b, v5.16b
    (0x7cfe70#64, 0x4e284b20#32),        -- aese    v0.16b, v25.16b
    (0x7cfe74#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfe78#64, 0x4e284b23#32),        -- aese    v3.16b, v25.16b
    (0x7cfe7c#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfe80#64, 0x5f785508#32),        -- shl     d8, d8, #56
    (0x7cfe84#64, 0x4e284b41#32),        -- aese    v1.16b, v26.16b
    (0x7cfe88#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfe8c#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7cfe90#64, 0x0eece0e6#32),        -- pmull   v6.1q, v7.1d, v12.1d
    (0x7cfe94#64, 0x4e284b43#32),        -- aese    v3.16b, v26.16b
    (0x7cfe98#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfe9c#64, 0xf100323f#32),        -- cmp     x17, #0xc
    (0x7cfea0#64, 0x4e284b40#32),        -- aese    v0.16b, v26.16b
    (0x7cfea4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfea8#64, 0x6e261d6b#32),        -- eor     v11.16b, v11.16b, v6.16b
    (0x7cfeac#64, 0x4e284b22#32),        -- aese    v2.16b, v25.16b
    (0x7cfeb0#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfeb4#64, 0x6e291d4a#32),        -- eor     v10.16b, v10.16b, v9.16b
    (0x7cfeb8#64, 0x4e284b42#32),        -- aese    v2.16b, v26.16b
    (0x7cfebc#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfec0#64, 0x0ee8e124#32),        -- pmull   v4.1q, v9.1d, v8.1d
    (0x7cfec4#64, 0x6e094129#32),        -- ext     v9.16b, v9.16b, v9.16b, #8
    (0x7cfec8#64, 0x6e2b1d4a#32),        -- eor     v10.16b, v10.16b, v11.16b
    (0x7cfecc#64, 0x5400044b#32),        -- b.lt    7cff54 <.Lenc_finish_prepretail>  // b.tstop
    (0x7cfed0#64, 0x4e284b61#32),        -- aese    v1.16b, v27.16b
    (0x7cfed4#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cfed8#64, 0x4e284b63#32),        -- aese    v3.16b, v27.16b
    (0x7cfedc#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfee0#64, 0x4e284b60#32),        -- aese    v0.16b, v27.16b
    (0x7cfee4#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cfee8#64, 0x4e284b62#32),        -- aese    v2.16b, v27.16b
    (0x7cfeec#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cfef0#64, 0x4e284b83#32),        -- aese    v3.16b, v28.16b
    (0x7cfef4#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cfef8#64, 0x4e284b81#32),        -- aese    v1.16b, v28.16b
    (0x7cfefc#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cff00#64, 0x4e284b80#32),        -- aese    v0.16b, v28.16b
    (0x7cff04#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cff08#64, 0x4e284b82#32),        -- aese    v2.16b, v28.16b
    (0x7cff0c#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cff10#64, 0x54000220#32),        -- b.eq    7cff54 <.Lenc_finish_prepretail>  // b.none
    (0x7cff14#64, 0x4e284ba1#32),        -- aese    v1.16b, v29.16b
    (0x7cff18#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cff1c#64, 0x4e284ba0#32),        -- aese    v0.16b, v29.16b
    (0x7cff20#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cff24#64, 0x4e284ba3#32),        -- aese    v3.16b, v29.16b
    (0x7cff28#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cff2c#64, 0x4e284ba2#32),        -- aese    v2.16b, v29.16b
    (0x7cff30#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x7cff34#64, 0x4e284bc1#32),        -- aese    v1.16b, v30.16b
    (0x7cff38#64, 0x4e286821#32),        -- aesmc   v1.16b, v1.16b
    (0x7cff3c#64, 0x4e284bc0#32),        -- aese    v0.16b, v30.16b
    (0x7cff40#64, 0x4e286800#32),        -- aesmc   v0.16b, v0.16b
    (0x7cff44#64, 0x4e284bc3#32),        -- aese    v3.16b, v30.16b
    (0x7cff48#64, 0x4e286863#32),        -- aesmc   v3.16b, v3.16b
    (0x7cff4c#64, 0x4e284bc2#32),        -- aese    v2.16b, v30.16b
    (0x7cff50#64, 0x4e286842#32),        -- aesmc   v2.16b, v2.16b

    -- 00000000007cff54 <.Lenc_finish_prepretail>:
    (0x7cff54#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7cff58#64, 0x6e291d4a#32),        -- eor     v10.16b, v10.16b, v9.16b
    (0x7cff5c#64, 0x0ee8e144#32),        -- pmull   v4.1q, v10.1d, v8.1d
    (0x7cff60#64, 0x6e0a414a#32),        -- ext     v10.16b, v10.16b, v10.16b, #8
    (0x7cff64#64, 0x4e284be1#32),        -- aese    v1.16b, v31.16b
    (0x7cff68#64, 0x6e241d6b#32),        -- eor     v11.16b, v11.16b, v4.16b
    (0x7cff6c#64, 0x4e284be3#32),        -- aese    v3.16b, v31.16b
    (0x7cff70#64, 0x4e284be0#32),        -- aese    v0.16b, v31.16b
    (0x7cff74#64, 0x4e284be2#32),        -- aese    v2.16b, v31.16b
    (0x7cff78#64, 0x6e2a1d6b#32),        -- eor     v11.16b, v11.16b, v10.16b

    -- 00000000007cff7c <.Lenc_tail>:
    (0x7cff7c#64, 0x6e0b4168#32),        -- ext     v8.16b, v11.16b, v11.16b, #8
    (0x7cff80#64, 0xcb000085#32),        -- sub     x5, x4, x0
    (0x7cff84#64, 0xa8c11c06#32),        -- ldp     x6, x7, [x0], #16
    (0x7cff88#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7cff8c#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7cff90#64, 0xf100c0bf#32),        -- cmp     x5, #0x30
    (0x7cff94#64, 0x9e6700c4#32),        -- fmov    d4, x6
    (0x7cff98#64, 0x9eaf00e4#32),        -- fmov    v4.d[1], x7
    (0x7cff9c#64, 0x6e201c85#32),        -- eor     v5.16b, v4.16b, v0.16b
    (0x7cffa0#64, 0x540001ec#32),        -- b.gt    7cffdc <.Lenc_blocks_4_remaining>
    (0x7cffa4#64, 0xf10080bf#32),        -- cmp     x5, #0x20
    (0x7cffa8#64, 0x4ea21c43#32),        -- mov     v3.16b, v2.16b
    (0x7cffac#64, 0x0f00e40b#32),        -- movi    v11.8b, #0x0
    (0x7cffb0#64, 0x0f00e409#32),        -- movi    v9.8b, #0x0
    (0x7cffb4#64, 0x5100058c#32),        -- sub     w12, w12, #0x1
    (0x7cffb8#64, 0x4ea11c22#32),        -- mov     v2.16b, v1.16b
    (0x7cffbc#64, 0x0f00e40a#32),        -- movi    v10.8b, #0x0
    (0x7cffc0#64, 0x540002ec#32),        -- b.gt    7d001c <.Lenc_blocks_3_remaining>
    (0x7cffc4#64, 0x4ea11c23#32),        -- mov     v3.16b, v1.16b
    (0x7cffc8#64, 0x5100058c#32),        -- sub     w12, w12, #0x1
    (0x7cffcc#64, 0xf10040bf#32),        -- cmp     x5, #0x10
    (0x7cffd0#64, 0x540004ac#32),        -- b.gt    7d0064 <.Lenc_blocks_2_remaining>
    (0x7cffd4#64, 0x5100058c#32),        -- sub     w12, w12, #0x1
    (0x7cffd8#64, 0x14000036#32),        -- b       7d00b0 <.Lenc_blocks_1_remaining>

    -- 00000000007cffdc <.Lenc_blocks_4_remaining>:
    (0x7cffdc#64, 0x4c9f7045#32),        -- st1     {v5.16b}, [x2], #16
    (0x7cffe0#64, 0xa8c11c06#32),        -- ldp     x6, x7, [x0], #16
    (0x7cffe4#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7cffe8#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7cffec#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7cfff0#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7cfff4#64, 0x5e180496#32),        -- mov     d22, v4.d[1]
    (0x7cfff8#64, 0x9e6700c5#32),        -- fmov    d5, x6
    (0x7cfffc#64, 0x9eaf00e5#32),        -- fmov    v5.d[1], x7
    (0x7d0000#64, 0x2e241ed6#32),        -- eor     v22.8b, v22.8b, v4.8b
    (0x7d0004#64, 0x0f00e408#32),        -- movi    v8.8b, #0x0
    (0x7d0008#64, 0x5e18062a#32),        -- mov     d10, v17.d[1]
    (0x7d000c#64, 0x0eefe08b#32),        -- pmull   v11.1q, v4.1d, v15.1d
    (0x7d0010#64, 0x4eefe089#32),        -- pmull2  v9.1q, v4.2d, v15.2d
    (0x7d0014#64, 0x0eeae2ca#32),        -- pmull   v10.1q, v22.1d, v10.1d
    (0x7d0018#64, 0x6e211ca5#32),        -- eor     v5.16b, v5.16b, v1.16b

    -- 00000000007d001c <.Lenc_blocks_3_remaining>:
    (0x7d001c#64, 0x4c9f7045#32),        -- st1     {v5.16b}, [x2], #16
    (0x7d0020#64, 0xa8c11c06#32),        -- ldp     x6, x7, [x0], #16
    (0x7d0024#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7d0028#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d002c#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7d0030#64, 0x9e6700c5#32),        -- fmov    d5, x6
    (0x7d0034#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7d0038#64, 0x9eaf00e5#32),        -- fmov    v5.d[1], x7
    (0x7d003c#64, 0x0f00e408#32),        -- movi    v8.8b, #0x0
    (0x7d0040#64, 0x4eeee094#32),        -- pmull2  v20.1q, v4.2d, v14.2d
    (0x7d0044#64, 0x5e180496#32),        -- mov     d22, v4.d[1]
    (0x7d0048#64, 0x0eeee095#32),        -- pmull   v21.1q, v4.1d, v14.1d
    (0x7d004c#64, 0x2e241ed6#32),        -- eor     v22.8b, v22.8b, v4.8b
    (0x7d0050#64, 0x6e221ca5#32),        -- eor     v5.16b, v5.16b, v2.16b
    (0x7d0054#64, 0x6e341d29#32),        -- eor     v9.16b, v9.16b, v20.16b
    (0x7d0058#64, 0x0ef1e2d6#32),        -- pmull   v22.1q, v22.1d, v17.1d
    (0x7d005c#64, 0x6e351d6b#32),        -- eor     v11.16b, v11.16b, v21.16b
    (0x7d0060#64, 0x6e361d4a#32),        -- eor     v10.16b, v10.16b, v22.16b

    -- 00000000007d0064 <.Lenc_blocks_2_remaining>:
    (0x7d0064#64, 0x4c9f7045#32),        -- st1     {v5.16b}, [x2], #16
    (0x7d0068#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7d006c#64, 0xa8c11c06#32),        -- ldp     x6, x7, [x0], #16
    (0x7d0070#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7d0074#64, 0x0f00e408#32),        -- movi    v8.8b, #0x0
    (0x7d0078#64, 0xca0d00c6#32),        -- eor     x6, x6, x13
    (0x7d007c#64, 0x5e180496#32),        -- mov     d22, v4.d[1]
    (0x7d0080#64, 0x4eede094#32),        -- pmull2  v20.1q, v4.2d, v13.2d
    (0x7d0084#64, 0xca0e00e7#32),        -- eor     x7, x7, x14
    (0x7d0088#64, 0x2e241ed6#32),        -- eor     v22.8b, v22.8b, v4.8b
    (0x7d008c#64, 0x6e341d29#32),        -- eor     v9.16b, v9.16b, v20.16b
    (0x7d0090#64, 0x6e1806d6#32),        -- mov     v22.d[1], v22.d[0]
    (0x7d0094#64, 0x9e6700c5#32),        -- fmov    d5, x6
    (0x7d0098#64, 0x9eaf00e5#32),        -- fmov    v5.d[1], x7
    (0x7d009c#64, 0x4ef0e2d6#32),        -- pmull2  v22.1q, v22.2d, v16.2d
    (0x7d00a0#64, 0x0eede095#32),        -- pmull   v21.1q, v4.1d, v13.1d
    (0x7d00a4#64, 0x6e231ca5#32),        -- eor     v5.16b, v5.16b, v3.16b
    (0x7d00a8#64, 0x6e361d4a#32),        -- eor     v10.16b, v10.16b, v22.16b
    (0x7d00ac#64, 0x6e351d6b#32),        -- eor     v11.16b, v11.16b, v21.16b

    -- 00000000007d00b0 <.Lenc_blocks_1_remaining>:
    (0x7d00b0#64, 0x4e2008a4#32),        -- rev64   v4.16b, v5.16b
    (0x7d00b4#64, 0x6e281c84#32),        -- eor     v4.16b, v4.16b, v8.16b
    (0x7d00b8#64, 0x4eece094#32),        -- pmull2  v20.1q, v4.2d, v12.2d
    (0x7d00bc#64, 0x5e180488#32),        -- mov     d8, v4.d[1]
    (0x7d00c0#64, 0x5ac00989#32),        -- rev     w9, w12
    (0x7d00c4#64, 0x0eece095#32),        -- pmull   v21.1q, v4.1d, v12.1d
    (0x7d00c8#64, 0x6e341d29#32),        -- eor     v9.16b, v9.16b, v20.16b
    (0x7d00cc#64, 0x2e241d08#32),        -- eor     v8.8b, v8.8b, v4.8b
    (0x7d00d0#64, 0x0ef0e108#32),        -- pmull   v8.1q, v8.1d, v16.1d
    (0x7d00d4#64, 0x6e351d6b#32),        -- eor     v11.16b, v11.16b, v21.16b
    (0x7d00d8#64, 0x6e281d4a#32),        -- eor     v10.16b, v10.16b, v8.16b
    (0x7d00dc#64, 0x0f06e448#32),        -- movi    v8.8b, #0xc2
    (0x7d00e0#64, 0x6e291d64#32),        -- eor     v4.16b, v11.16b, v9.16b
    (0x7d00e4#64, 0x5f785508#32),        -- shl     d8, d8, #56
    (0x7d00e8#64, 0x6e241d4a#32),        -- eor     v10.16b, v10.16b, v4.16b
    (0x7d00ec#64, 0x0ee8e127#32),        -- pmull   v7.1q, v9.1d, v8.1d
    (0x7d00f0#64, 0x6e094129#32),        -- ext     v9.16b, v9.16b, v9.16b, #8
    (0x7d00f4#64, 0x6e271d4a#32),        -- eor     v10.16b, v10.16b, v7.16b
    (0x7d00f8#64, 0x6e291d4a#32),        -- eor     v10.16b, v10.16b, v9.16b
    (0x7d00fc#64, 0x0ee8e149#32),        -- pmull   v9.1q, v10.1d, v8.1d
    (0x7d0100#64, 0x6e0a414a#32),        -- ext     v10.16b, v10.16b, v10.16b, #8
    (0x7d0104#64, 0xb9000e09#32),        -- str     w9, [x16, #12]
    (0x7d0108#64, 0x4c007045#32),        -- st1     {v5.16b}, [x2]
    (0x7d010c#64, 0x6e291d6b#32),        -- eor     v11.16b, v11.16b, v9.16b
    (0x7d0110#64, 0x6e2a1d6b#32),        -- eor     v11.16b, v11.16b, v10.16b
    (0x7d0114#64, 0x6e0b416b#32),        -- ext     v11.16b, v11.16b, v11.16b, #8
    (0x7d0118#64, 0x4e20096b#32),        -- rev64   v11.16b, v11.16b
    (0x7d011c#64, 0xaa0f03e0#32),        -- mov     x0, x15
    (0x7d0120#64, 0x4c00706b#32),        -- st1     {v11.16b}, [x3]
    (0x7d0124#64, 0xa94153f3#32),        -- ldp     x19, x20, [sp, #16]
    (0x7d0128#64, 0xa9425bf5#32),        -- ldp     x21, x22, [sp, #32]
    (0x7d012c#64, 0xa94363f7#32),        -- ldp     x23, x24, [sp, #48]
    (0x7d0130#64, 0x6d4427e8#32),        -- ldp     d8, d9, [sp, #64]
    (0x7d0134#64, 0x6d452fea#32),        -- ldp     d10, d11, [sp, #80]
    (0x7d0138#64, 0x6d4637ec#32),        -- ldp     d12, d13, [sp, #96]
    (0x7d013c#64, 0x6d473fee#32),        -- ldp     d14, d15, [sp, #112]
    (0x7d0140#64, 0xa8c87bfd#32),        -- ldp     x29, x30, [sp], #128
    (0x7d0144#64, 0xd65f03c0#32)         -- ret
  ]

end AESGCMEncKernelProgram
