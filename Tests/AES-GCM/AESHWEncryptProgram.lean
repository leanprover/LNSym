/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.Exec

namespace AESHWEncryptProgram

open BitVec

/-
  void aes_hw_encrypt(const uint8_t *in, uint8_t *out, const AES_KEY *key);

  input: in - one message block to be encrypted (x0)
         key -- AES key schedule and rounds (x2)
  output: out - output ciphertext (x1)
-/


def aes_hw_encrypt_program : Program :=
  def_program
  [ -- 000000000079f5a0 <aes_hw_encrypt>:
    (0x79f5a0#64,       0xb940f043#32),        -- ldr     w3, [x2, #240]
    (0x79f5a4#64,       0x4cdf7840#32),        -- ld1     {v0.4s}, [x2], #16
    (0x79f5a8#64,       0x4c407002#32),        -- ld1     {v2.16b}, [x0]
    (0x79f5ac#64,       0x51000863#32),        -- sub     w3, w3, #0x2
    (0x79f5b0#64,       0x4cdf7841#32),        -- ld1     {v1.4s}, [x2], #16

    -- 000000000079f5b4 <.Loop_enc>:
    (0x79f5b4#64,       0x4e284802#32),        -- aese    v2.16b, v0.16b
    (0x79f5b8#64,       0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x79f5bc#64,       0x4cdf7840#32),        -- ld1     {v0.4s}, [x2], #16
    (0x79f5c0#64,       0x71000863#32),        -- subs    w3, w3, #0x2
    (0x79f5c4#64,       0x4e284822#32),        -- aese    v2.16b, v1.16b
    (0x79f5c8#64,       0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x79f5cc#64,       0x4cdf7841#32),        -- ld1     {v1.4s}, [x2], #16
    (0x79f5d0#64,       0x54ffff2c#32),        -- b.gt    79f5b4 <.Loop_enc>
    (0x79f5d4#64,       0x4e284802#32),        -- aese    v2.16b, v0.16b
    (0x79f5d8#64,       0x4e286842#32),        -- aesmc   v2.16b, v2.16b
    (0x79f5dc#64,       0x4c407840#32),        -- ld1     {v0.4s}, [x2]
    (0x79f5e0#64,       0x4e284822#32),        -- aese    v2.16b, v1.16b
    (0x79f5e4#64,       0x6e201c42#32),        -- eor     v2.16b, v2.16b, v0.16b
    (0x79f5e8#64,       0x4c007022#32),        -- st1     {v2.16b}, [x1]
    (0x79f5ec#64,       0xd65f03c0#32)         -- ret
  ]

end AESHWEncryptProgram
