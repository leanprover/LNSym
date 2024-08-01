/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec

namespace GCMGmultV8Program

open BitVec

/-
 void gcm_gmult_v8(u8 Xi[16],const u128 Htable[16]);

 input: Xi - current hash value; (x0)
        Htable - table precomputed in gcm_init_v8; (x1)
 output: Xi - next hash value Xi;
-/

def gcm_gmult_v8_program : Program :=
 def_program
  [ -- 00000000007d8800 <gcm_gmult_v8>:
    (0x7d8800#64, 0x4c407c11#32),        -- ld1     {v17.2d}, [x0]
    (0x7d8804#64, 0x4f07e433#32),        -- movi    v19.16b, #0xe1
    (0x7d8808#64, 0x4c40ac34#32),        -- ld1     {v20.2d, v21.2d}, [x1]
    (0x7d880c#64, 0x6e144294#32),        -- ext     v20.16b, v20.16b, v20.16b, #8
    (0x7d8810#64, 0x4f795673#32),        -- shl     v19.2d, v19.2d, #57
    (0x7d8814#64, 0x4e200a31#32),        -- rev64   v17.16b, v17.16b
    (0x7d8818#64, 0x6e114223#32),        -- ext     v3.16b, v17.16b, v17.16b, #8
    (0x7d881c#64, 0x0ee3e280#32),        -- pmull   v0.1q, v20.1d, v3.1d
    (0x7d8820#64, 0x6e231e31#32),        -- eor     v17.16b, v17.16b, v3.16b
    (0x7d8824#64, 0x4ee3e282#32),        -- pmull2  v2.1q, v20.2d, v3.2d
    (0x7d8828#64, 0x0ef1e2a1#32),        -- pmull   v1.1q, v21.1d, v17.1d
    (0x7d882c#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d8830#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8834#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8838#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d883c#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8840#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8844#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8848#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d884c#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8850#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8854#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8858#64, 0x6e321c00#32),        -- eor     v0.16b, v0.16b, v18.16b
    (0x7d885c#64, 0x4e200800#32),        -- rev64   v0.16b, v0.16b
    (0x7d8860#64, 0x6e004000#32),        -- ext     v0.16b, v0.16b, v0.16b, #8
    (0x7d8864#64, 0x4c007c00#32),        -- st1     {v0.2d}, [x0]
    (0x7d8868#64, 0xd65f03c0#32)         -- ret
  ]

end GCMGmultV8Program
