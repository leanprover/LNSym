/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec

namespace AESHWSetEncryptKeyProgram

open BitVec

/-

  int aes_hw_set_encrypt_key(const uint8_t *user_key, const int bits, AES_KEY *key);

  input: user_key - Initial key (x0)
         bits - 128/192/256 (w1)
  output: key (x2) - rd_key - Generated round keys
                     rounds - Number of rounds
  constants: rcon first (01), rotation indexes, and rcon second to last (1b) from address in x3

-/

def aes_hw_set_encrypt_key_program : program :=
  def_program
  [ -- 000000000079f380 <aes_hw_set_encrypt_key>:
    (0x79f380#64,  0xa9bf7bfd#32),   -- stp  x29, x30, [sp, #-16]!
    (0x79f384#64,  0x910003fd#32),   -- mov  x29, sp
    (0x79f388#64,  0x92800003#32),   -- mov  x3, #0xffffffffffffffff      // #-1
    (0x79f38c#64,  0xf100001f#32),   -- cmp  x0, #0x0
    (0x79f390#64,  0x54000f60#32),   -- b.eq  79f57c <.Lenc_key_abort>  // b.none
    (0x79f394#64,  0xf100005f#32),   -- cmp  x2, #0x0
    (0x79f398#64,  0x54000f20#32),   -- b.eq  79f57c <.Lenc_key_abort>  // b.none
    (0x79f39c#64,  0x92800023#32),   -- mov  x3, #0xfffffffffffffffe      // #-2
    (0x79f3a0#64,  0x7102003f#32),   -- cmp  w1, #0x80
    (0x79f3a4#64,  0x54000ecb#32),   -- b.lt  79f57c <.Lenc_key_abort>  // b.tstop
    (0x79f3a8#64,  0x7104003f#32),   -- cmp  w1, #0x100
    (0x79f3ac#64,  0x54000e8c#32),   -- b.gt  79f57c <.Lenc_key_abort>
    (0x79f3b0#64,  0x7200143f#32),   -- tst  w1, #0x3f
    (0x79f3b4#64,  0x54000e41#32),   -- b.ne  79f57c <.Lenc_key_abort>  // b.any
    (0x79f3b8#64,  0xf001c303#32),   -- adrp  x3, 4002000 <self_test_ffc_dh_fb_key.kDH_g+0x20c>
    (0x79f3bc#64,  0x91328063#32),   -- add  x3, x3, #0xca0
    (0x79f3c0#64,  0x7103003f#32),   -- cmp  w1, #0xc0
    (0x79f3c4#64,  0x6e201c00#32),   -- eor  v0.16b, v0.16b, v0.16b
    (0x79f3c8#64,  0x4cdf7003#32),   -- ld1  {v3.16b}, [x0], #16
    (0x79f3cc#64,  0x52800101#32),   -- mov  w1, #0x8                     // #8
    (0x79f3d0#64,  0x4cdfa861#32),   -- ld1  {v1.4s, v2.4s}, [x3], #32
    (0x79f3d4#64,  0x5400006b#32),   -- b.lt  79f3e0 <.Loop128>  // b.tstop
    (0x79f3d8#64,  0x540005c0#32),   -- b.eq  79f490 <.L192>  // b.none
    (0x79f3dc#64,  0x14000049#32),   -- b  79f500 <.L256>

    -- 000000000079f3e0 <.Loop128>:
    (0x79f3e0#64,  0x4e020066#32),   -- tbl  v6.16b, {v3.16b}, v2.16b
    (0x79f3e4#64,  0x6e036005#32),   -- ext  v5.16b, v0.16b, v3.16b, #12
    (0x79f3e8#64,  0x4c9f7843#32),   -- st1  {v3.4s}, [x2], #16
    (0x79f3ec#64,  0x4e284806#32),   -- aese  v6.16b, v0.16b
    (0x79f3f0#64,  0x71000421#32),   -- subs  w1, w1, #0x1
    (0x79f3f4#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f3f8#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f3fc#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f400#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f404#64,  0x6e211cc6#32),   -- eor  v6.16b, v6.16b, v1.16b
    (0x79f408#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f40c#64,  0x4f095421#32),   -- shl  v1.16b, v1.16b, #1
    (0x79f410#64,  0x6e261c63#32),   -- eor  v3.16b, v3.16b, v6.16b
    (0x79f414#64,  0x54fffe61#32),   -- b.ne  79f3e0 <.Loop128>  // b.any
    (0x79f418#64,  0x4c407861#32),   -- ld1  {v1.4s}, [x3]
    (0x79f41c#64,  0x4e020066#32),   -- tbl  v6.16b, {v3.16b}, v2.16b
    (0x79f420#64,  0x6e036005#32),   -- ext  v5.16b, v0.16b, v3.16b, #12
    (0x79f424#64,  0x4c9f7843#32),   -- st1  {v3.4s}, [x2], #16
    (0x79f428#64,  0x4e284806#32),   -- aese  v6.16b, v0.16b
    (0x79f42c#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f430#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f434#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f438#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f43c#64,  0x6e211cc6#32),   -- eor  v6.16b, v6.16b, v1.16b
    (0x79f440#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f444#64,  0x4f095421#32),   -- shl  v1.16b, v1.16b, #1
    (0x79f448#64,  0x6e261c63#32),   -- eor  v3.16b, v3.16b, v6.16b
    (0x79f44c#64,  0x4e020066#32),   -- tbl  v6.16b, {v3.16b}, v2.16b
    (0x79f450#64,  0x6e036005#32),   -- ext  v5.16b, v0.16b, v3.16b, #12
    (0x79f454#64,  0x4c9f7843#32),   -- st1  {v3.4s}, [x2], #16
    (0x79f458#64,  0x4e284806#32),   -- aese  v6.16b, v0.16b
    (0x79f45c#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f460#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f464#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f468#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f46c#64,  0x6e211cc6#32),   -- eor  v6.16b, v6.16b, v1.16b
    (0x79f470#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f474#64,  0x6e261c63#32),   -- eor  v3.16b, v3.16b, v6.16b
    (0x79f478#64,  0x4c007843#32),   -- st1  {v3.4s}, [x2]
    (0x79f47c#64,  0x91014042#32),   -- add  x2, x2, #0x50
    (0x79f480#64,  0x5280014c#32),   -- mov  w12, #0xa                     // #10
    (0x79f484#64,  0x1400003c#32),   -- b  79f574 <.Ldone>
    (0x79f488#64,  0xd503201f#32),   -- nop
    (0x79f48c#64,  0xd503201f#32),   -- nop

    -- 000000000079f490 <.L192>:
    (0x79f490#64,  0x0cdf7004#32),   -- ld1  {v4.8b}, [x0], #8
    (0x79f494#64,  0x4f00e506#32),   -- movi  v6.16b, #0x8
    (0x79f498#64,  0x4c9f7843#32),   -- st1  {v3.4s}, [x2], #16
    (0x79f49c#64,  0x6e268442#32),   -- sub  v2.16b, v2.16b, v6.16b

    -- 000000000079f4a0 <.Loop192>:
    (0x79f4a0#64,  0x4e020086#32),   -- tbl  v6.16b, {v4.16b}, v2.16b
    (0x79f4a4#64,  0x6e036005#32),   -- ext  v5.16b, v0.16b, v3.16b, #12
    (0x79f4a8#64,  0x0c9f7044#32),   -- st1  {v4.8b}, [x2], #8
    (0x79f4ac#64,  0x4e284806#32),   -- aese  v6.16b, v0.16b
    (0x79f4b0#64,  0x71000421#32),   -- subs  w1, w1, #0x1
    (0x79f4b4#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f4b8#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f4bc#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f4c0#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f4c4#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f4c8#64,  0x4e1c0465#32),   -- dup  v5.4s, v3.s[3]
    (0x79f4cc#64,  0x6e241ca5#32),   -- eor  v5.16b, v5.16b, v4.16b
    (0x79f4d0#64,  0x6e211cc6#32),   -- eor  v6.16b, v6.16b, v1.16b
    (0x79f4d4#64,  0x6e046004#32),   -- ext  v4.16b, v0.16b, v4.16b, #12
    (0x79f4d8#64,  0x4f095421#32),   -- shl  v1.16b, v1.16b, #1
    (0x79f4dc#64,  0x6e251c84#32),   -- eor  v4.16b, v4.16b, v5.16b
    (0x79f4e0#64,  0x6e261c63#32),   -- eor  v3.16b, v3.16b, v6.16b
    (0x79f4e4#64,  0x6e261c84#32),   -- eor  v4.16b, v4.16b, v6.16b
    (0x79f4e8#64,  0x4c9f7843#32),   -- st1  {v3.4s}, [x2], #16
    (0x79f4ec#64,  0x54fffda1#32),   -- b.ne  79f4a0 <.Loop192>  // b.any
    (0x79f4f0#64,  0x5280018c#32),   -- mov  w12, #0xc                     // #12
    (0x79f4f4#64,  0x91008042#32),   -- add  x2, x2, #0x20
    (0x79f4f8#64,  0x1400001f#32),   -- b  79f574 <.Ldone>
    (0x79f4fc#64,  0xd503201f#32),   -- nop

    -- 000000000079f500 <.L256>:
    (0x79f500#64,  0x4c407004#32),   -- ld1  {v4.16b}, [x0]
    (0x79f504#64,  0x528000e1#32),   -- mov  w1, #0x7                     // #7
    (0x79f508#64,  0x528001cc#32),   -- mov  w12, #0xe                     // #14
    (0x79f50c#64,  0x4c9f7843#32),   -- st1  {v3.4s}, [x2], #16

    -- 000000000079f510 <.Loop256>:
    (0x79f510#64,  0x4e020086#32),   -- tbl  v6.16b, {v4.16b}, v2.16b
    (0x79f514#64,  0x6e036005#32),   -- ext  v5.16b, v0.16b, v3.16b, #12
    (0x79f518#64,  0x4c9f7844#32),   -- st1  {v4.4s}, [x2], #16
    (0x79f51c#64,  0x4e284806#32),   -- aese  v6.16b, v0.16b
    (0x79f520#64,  0x71000421#32),   -- subs  w1, w1, #0x1
    (0x79f524#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f528#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f52c#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f530#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f534#64,  0x6e211cc6#32),   -- eor  v6.16b, v6.16b, v1.16b
    (0x79f538#64,  0x6e251c63#32),   -- eor  v3.16b, v3.16b, v5.16b
    (0x79f53c#64,  0x4f095421#32),   -- shl  v1.16b, v1.16b, #1
    (0x79f540#64,  0x6e261c63#32),   -- eor  v3.16b, v3.16b, v6.16b
    (0x79f544#64,  0x4c9f7843#32),   -- st1  {v3.4s}, [x2], #16
    (0x79f548#64,  0x54000160#32),   -- b.eq  79f574 <.Ldone>  // b.none
    (0x79f54c#64,  0x4e1c0466#32),   -- dup  v6.4s, v3.s[3]
    (0x79f550#64,  0x6e046005#32),   -- ext  v5.16b, v0.16b, v4.16b, #12
    (0x79f554#64,  0x4e284806#32),   -- aese  v6.16b, v0.16b
    (0x79f558#64,  0x6e251c84#32),   -- eor  v4.16b, v4.16b, v5.16b
    (0x79f55c#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f560#64,  0x6e251c84#32),   -- eor  v4.16b, v4.16b, v5.16b
    (0x79f564#64,  0x6e056005#32),   -- ext  v5.16b, v0.16b, v5.16b, #12
    (0x79f568#64,  0x6e251c84#32),   -- eor  v4.16b, v4.16b, v5.16b
    (0x79f56c#64,  0x6e261c84#32),   -- eor  v4.16b, v4.16b, v6.16b
    (0x79f570#64,  0x17ffffe8#32),   -- b  79f510 <.Loop256>

    -- 000000000079f574 <.Ldone>:
    (0x79f574#64,  0xb900004c#32),   -- str  w12, [x2]
    (0x79f578#64,  0xd2800003#32),   -- mov  x3, #0x0                     // #0

    -- 000000000079f57c <.Lenc_key_abort>:
    (0x79f57c#64,  0xaa0303e0#32),   -- mov  x0, x3
    (0x79f580#64,  0xf84107fd#32),   -- ldr  x29, [sp], #16
    (0x79f584#64,  0xd65f03c0#32),   -- ret
  ]

end AESHWSetEncryptKeyProgram
