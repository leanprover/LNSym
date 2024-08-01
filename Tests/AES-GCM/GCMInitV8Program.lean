/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Arm.Exec

namespace GCMInitV8Program

open BitVec

/-
 void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

 input:  H - initial hash (x1)
 output: Htable - powers of H precomputed up to H^12 (x0)
-/

def gcm_init_v8_program : Program :=
  def_program
  [ -- 00000000007d85a0 <gcm_init_v8>:
    (0x7d85a0#64, 0x4c407c31#32),        -- ld1     {v17.2d}, [x1]
    (0x7d85a4#64, 0x4f07e433#32),        -- movi    v19.16b, #0xe1
    (0x7d85a8#64, 0x4f795673#32),        -- shl     v19.2d, v19.2d, #57
    (0x7d85ac#64, 0x6e114223#32),        -- ext     v3.16b, v17.16b, v17.16b, #8
    (0x7d85b0#64, 0x6f410672#32),        -- ushr    v18.2d, v19.2d, #63
    (0x7d85b4#64, 0x4e0c0631#32),        -- dup     v17.4s, v17.s[1]
    (0x7d85b8#64, 0x6e134250#32),        -- ext     v16.16b, v18.16b, v19.16b, #8
    (0x7d85bc#64, 0x6f410472#32),        -- ushr    v18.2d, v3.2d, #63
    (0x7d85c0#64, 0x4f210631#32),        -- sshr    v17.4s, v17.4s, #31
    (0x7d85c4#64, 0x4e301e52#32),        -- and     v18.16b, v18.16b, v16.16b
    (0x7d85c8#64, 0x4f415463#32),        -- shl     v3.2d, v3.2d, #1
    (0x7d85cc#64, 0x6e124252#32),        -- ext     v18.16b, v18.16b, v18.16b, #8
    (0x7d85d0#64, 0x4e311e10#32),        -- and     v16.16b, v16.16b, v17.16b
    (0x7d85d4#64, 0x4eb21c63#32),        -- orr     v3.16b, v3.16b, v18.16b
    (0x7d85d8#64, 0x6e301c74#32),        -- eor     v20.16b, v3.16b, v16.16b
    (0x7d85dc#64, 0x6e144294#32),        -- ext     v20.16b, v20.16b, v20.16b, #8
    (0x7d85e0#64, 0x4c9f7c14#32),        -- st1     {v20.2d}, [x0], #16
    (0x7d85e4#64, 0x6e144290#32),        -- ext     v16.16b, v20.16b, v20.16b, #8
    (0x7d85e8#64, 0x4ef4e280#32),        -- pmull2  v0.1q, v20.2d, v20.2d
    (0x7d85ec#64, 0x6e341e10#32),        -- eor     v16.16b, v16.16b, v20.16b
    (0x7d85f0#64, 0x0ef4e282#32),        -- pmull   v2.1q, v20.1d, v20.1d
    (0x7d85f4#64, 0x0ef0e201#32),        -- pmull   v1.1q, v16.1d, v16.1d
    (0x7d85f8#64, 0x6e024011#32),        -- ext     v17.16b, v0.16b, v2.16b, #8
    (0x7d85fc#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8600#64, 0x6e311c21#32),        -- eor     v1.16b, v1.16b, v17.16b
    (0x7d8604#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8608#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d860c#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8610#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8614#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8618#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d861c#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8620#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8624#64, 0x6e321c11#32),        -- eor     v17.16b, v0.16b, v18.16b
    (0x7d8628#64, 0x6e114236#32),        -- ext     v22.16b, v17.16b, v17.16b, #8
    (0x7d862c#64, 0x6e361e31#32),        -- eor     v17.16b, v17.16b, v22.16b
    (0x7d8630#64, 0x6e114215#32),        -- ext     v21.16b, v16.16b, v17.16b, #8
    (0x7d8634#64, 0x4c9f7c15#32),        -- st1     {v21.2d}, [x0], #16
    (0x7d8638#64, 0x4c9f7c16#32),        -- st1     {v22.2d}, [x0], #16
    (0x7d863c#64, 0x4ef6e280#32),        -- pmull2  v0.1q, v20.2d, v22.2d
    (0x7d8640#64, 0x4ef6e2c5#32),        -- pmull2  v5.1q, v22.2d, v22.2d
    (0x7d8644#64, 0x0ef6e282#32),        -- pmull   v2.1q, v20.1d, v22.1d
    (0x7d8648#64, 0x0ef6e2c7#32),        -- pmull   v7.1q, v22.1d, v22.1d
    (0x7d864c#64, 0x0ef1e201#32),        -- pmull   v1.1q, v16.1d, v17.1d
    (0x7d8650#64, 0x0ef1e226#32),        -- pmull   v6.1q, v17.1d, v17.1d
    (0x7d8654#64, 0x6e024010#32),        -- ext     v16.16b, v0.16b, v2.16b, #8
    (0x7d8658#64, 0x6e0740b1#32),        -- ext     v17.16b, v5.16b, v7.16b, #8
    (0x7d865c#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8660#64, 0x6e301c21#32),        -- eor     v1.16b, v1.16b, v16.16b
    (0x7d8664#64, 0x6e271ca4#32),        -- eor     v4.16b, v5.16b, v7.16b
    (0x7d8668#64, 0x6e311cc6#32),        -- eor     v6.16b, v6.16b, v17.16b
    (0x7d866c#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8670#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d8674#64, 0x6e241cc6#32),        -- eor     v6.16b, v6.16b, v4.16b
    (0x7d8678#64, 0x0ef3e0a4#32),        -- pmull   v4.1q, v5.1d, v19.1d
    (0x7d867c#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8680#64, 0x6e0844c7#32),        -- mov     v7.d[0], v6.d[1]
    (0x7d8684#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8688#64, 0x6e1804a6#32),        -- mov     v6.d[1], v5.d[0]
    (0x7d868c#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8690#64, 0x6e241cc5#32),        -- eor     v5.16b, v6.16b, v4.16b
    (0x7d8694#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8698#64, 0x6e0540a4#32),        -- ext     v4.16b, v5.16b, v5.16b, #8
    (0x7d869c#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d86a0#64, 0x0ef3e0a5#32),        -- pmull   v5.1q, v5.1d, v19.1d
    (0x7d86a4#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d86a8#64, 0x6e271c84#32),        -- eor     v4.16b, v4.16b, v7.16b
    (0x7d86ac#64, 0x6e321c10#32),        -- eor     v16.16b, v0.16b, v18.16b
    (0x7d86b0#64, 0x6e241cb1#32),        -- eor     v17.16b, v5.16b, v4.16b
    (0x7d86b4#64, 0x6e104217#32),        -- ext     v23.16b, v16.16b, v16.16b, #8
    (0x7d86b8#64, 0x6e114239#32),        -- ext     v25.16b, v17.16b, v17.16b, #8
    (0x7d86bc#64, 0x6e1642d2#32),        -- ext     v18.16b, v22.16b, v22.16b, #8
    (0x7d86c0#64, 0x6e371e10#32),        -- eor     v16.16b, v16.16b, v23.16b
    (0x7d86c4#64, 0x6e391e31#32),        -- eor     v17.16b, v17.16b, v25.16b
    (0x7d86c8#64, 0x6e361e52#32),        -- eor     v18.16b, v18.16b, v22.16b
    (0x7d86cc#64, 0x6e114218#32),        -- ext     v24.16b, v16.16b, v17.16b, #8
    (0x7d86d0#64, 0x4c9f6c17#32),        -- st1     {v23.2d-v25.2d}, [x0], #48
    (0x7d86d4#64, 0x4ef7e2c0#32),        -- pmull2  v0.1q, v22.2d, v23.2d
    (0x7d86d8#64, 0x4ef7e2e5#32),        -- pmull2  v5.1q, v23.2d, v23.2d
    (0x7d86dc#64, 0x0ef7e2c2#32),        -- pmull   v2.1q, v22.1d, v23.1d
    (0x7d86e0#64, 0x0ef7e2e7#32),        -- pmull   v7.1q, v23.1d, v23.1d
    (0x7d86e4#64, 0x0ef2e201#32),        -- pmull   v1.1q, v16.1d, v18.1d
    (0x7d86e8#64, 0x0ef0e206#32),        -- pmull   v6.1q, v16.1d, v16.1d
    (0x7d86ec#64, 0x6e024010#32),        -- ext     v16.16b, v0.16b, v2.16b, #8
    (0x7d86f0#64, 0x6e0740b1#32),        -- ext     v17.16b, v5.16b, v7.16b, #8
    (0x7d86f4#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d86f8#64, 0x6e301c21#32),        -- eor     v1.16b, v1.16b, v16.16b
    (0x7d86fc#64, 0x6e271ca4#32),        -- eor     v4.16b, v5.16b, v7.16b
    (0x7d8700#64, 0x6e311cc6#32),        -- eor     v6.16b, v6.16b, v17.16b
    (0x7d8704#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d8708#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d870c#64, 0x6e241cc6#32),        -- eor     v6.16b, v6.16b, v4.16b
    (0x7d8710#64, 0x0ef3e0a4#32),        -- pmull   v4.1q, v5.1d, v19.1d
    (0x7d8714#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d8718#64, 0x6e0844c7#32),        -- mov     v7.d[0], v6.d[1]
    (0x7d871c#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d8720#64, 0x6e1804a6#32),        -- mov     v6.d[1], v5.d[0]
    (0x7d8724#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d8728#64, 0x6e241cc5#32),        -- eor     v5.16b, v6.16b, v4.16b
    (0x7d872c#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d8730#64, 0x6e0540a4#32),        -- ext     v4.16b, v5.16b, v5.16b, #8
    (0x7d8734#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d8738#64, 0x0ef3e0a5#32),        -- pmull   v5.1q, v5.1d, v19.1d
    (0x7d873c#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d8740#64, 0x6e271c84#32),        -- eor     v4.16b, v4.16b, v7.16b
    (0x7d8744#64, 0x6e321c10#32),        -- eor     v16.16b, v0.16b, v18.16b
    (0x7d8748#64, 0x6e241cb1#32),        -- eor     v17.16b, v5.16b, v4.16b
    (0x7d874c#64, 0x6e10421a#32),        -- ext     v26.16b, v16.16b, v16.16b, #8
    (0x7d8750#64, 0x6e11423c#32),        -- ext     v28.16b, v17.16b, v17.16b, #8
    (0x7d8754#64, 0x6e1642d2#32),        -- ext     v18.16b, v22.16b, v22.16b, #8
    (0x7d8758#64, 0x6e3a1e10#32),        -- eor     v16.16b, v16.16b, v26.16b
    (0x7d875c#64, 0x6e3c1e31#32),        -- eor     v17.16b, v17.16b, v28.16b
    (0x7d8760#64, 0x6e361e52#32),        -- eor     v18.16b, v18.16b, v22.16b
    (0x7d8764#64, 0x6e11421b#32),        -- ext     v27.16b, v16.16b, v17.16b, #8
    (0x7d8768#64, 0x4c9f6c1a#32),        -- st1     {v26.2d-v28.2d}, [x0], #48
    (0x7d876c#64, 0x4efae2c0#32),        -- pmull2  v0.1q, v22.2d, v26.2d
    (0x7d8770#64, 0x4efce2c5#32),        -- pmull2  v5.1q, v22.2d, v28.2d
    (0x7d8774#64, 0x0efae2c2#32),        -- pmull   v2.1q, v22.1d, v26.1d
    (0x7d8778#64, 0x0efce2c7#32),        -- pmull   v7.1q, v22.1d, v28.1d
    (0x7d877c#64, 0x0ef2e201#32),        -- pmull   v1.1q, v16.1d, v18.1d
    (0x7d8780#64, 0x0ef2e226#32),        -- pmull   v6.1q, v17.1d, v18.1d
    (0x7d8784#64, 0x6e024010#32),        -- ext     v16.16b, v0.16b, v2.16b, #8
    (0x7d8788#64, 0x6e0740b1#32),        -- ext     v17.16b, v5.16b, v7.16b, #8
    (0x7d878c#64, 0x6e221c12#32),        -- eor     v18.16b, v0.16b, v2.16b
    (0x7d8790#64, 0x6e301c21#32),        -- eor     v1.16b, v1.16b, v16.16b
    (0x7d8794#64, 0x6e271ca4#32),        -- eor     v4.16b, v5.16b, v7.16b
    (0x7d8798#64, 0x6e311cc6#32),        -- eor     v6.16b, v6.16b, v17.16b
    (0x7d879c#64, 0x6e321c21#32),        -- eor     v1.16b, v1.16b, v18.16b
    (0x7d87a0#64, 0x0ef3e012#32),        -- pmull   v18.1q, v0.1d, v19.1d
    (0x7d87a4#64, 0x6e241cc6#32),        -- eor     v6.16b, v6.16b, v4.16b
    (0x7d87a8#64, 0x0ef3e0a4#32),        -- pmull   v4.1q, v5.1d, v19.1d
    (0x7d87ac#64, 0x6e084422#32),        -- mov     v2.d[0], v1.d[1]
    (0x7d87b0#64, 0x6e0844c7#32),        -- mov     v7.d[0], v6.d[1]
    (0x7d87b4#64, 0x6e180401#32),        -- mov     v1.d[1], v0.d[0]
    (0x7d87b8#64, 0x6e1804a6#32),        -- mov     v6.d[1], v5.d[0]
    (0x7d87bc#64, 0x6e321c20#32),        -- eor     v0.16b, v1.16b, v18.16b
    (0x7d87c0#64, 0x6e241cc5#32),        -- eor     v5.16b, v6.16b, v4.16b
    (0x7d87c4#64, 0x6e004012#32),        -- ext     v18.16b, v0.16b, v0.16b, #8
    (0x7d87c8#64, 0x6e0540a4#32),        -- ext     v4.16b, v5.16b, v5.16b, #8
    (0x7d87cc#64, 0x0ef3e000#32),        -- pmull   v0.1q, v0.1d, v19.1d
    (0x7d87d0#64, 0x0ef3e0a5#32),        -- pmull   v5.1q, v5.1d, v19.1d
    (0x7d87d4#64, 0x6e221e52#32),        -- eor     v18.16b, v18.16b, v2.16b
    (0x7d87d8#64, 0x6e271c84#32),        -- eor     v4.16b, v4.16b, v7.16b
    (0x7d87dc#64, 0x6e321c10#32),        -- eor     v16.16b, v0.16b, v18.16b
    (0x7d87e0#64, 0x6e241cb1#32),        -- eor     v17.16b, v5.16b, v4.16b
    (0x7d87e4#64, 0x6e10421d#32),        -- ext     v29.16b, v16.16b, v16.16b, #8
    (0x7d87e8#64, 0x6e11423f#32),        -- ext     v31.16b, v17.16b, v17.16b, #8
    (0x7d87ec#64, 0x6e3d1e10#32),        -- eor     v16.16b, v16.16b, v29.16b
    (0x7d87f0#64, 0x6e3f1e31#32),        -- eor     v17.16b, v17.16b, v31.16b
    (0x7d87f4#64, 0x6e11421e#32),        -- ext     v30.16b, v16.16b, v17.16b, #8
    (0x7d87f8#64, 0x4c006c1d#32),        -- st1     {v29.2d-v31.2d}, [x0]
    (0x7d87fc#64, 0xd65f03c0#32)         -- ret
  ]

end GCMInitV8Program
