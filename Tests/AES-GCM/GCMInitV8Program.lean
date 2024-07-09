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
  [ -- 00000000007aa1c0 <gcm_init_v8>:
    (0x7aa1c0#64,  0x4c407c31#32),   -- ld1  {v17.2d}, [x1]
    (0x7aa1c4#64,  0x4f07e433#32),   -- movi  v19.16b, #0xe1
    (0x7aa1c8#64,  0x4f795673#32),   -- shl  v19.2d, v19.2d, #57
    (0x7aa1cc#64,  0x6e114223#32),   -- ext  v3.16b, v17.16b, v17.16b, #8
    (0x7aa1d0#64,  0x6f410672#32),   -- ushr  v18.2d, v19.2d, #63
    (0x7aa1d4#64,  0x4e0c0631#32),   -- dup  v17.4s, v17.s[1]
    (0x7aa1d8#64,  0x6e134250#32),   -- ext  v16.16b, v18.16b, v19.16b, #8
    (0x7aa1dc#64,  0x6f410472#32),   -- ushr  v18.2d, v3.2d, #63
    (0x7aa1e0#64,  0x4f210631#32),   -- sshr  v17.4s, v17.4s, #31
    (0x7aa1e4#64,  0x4e301e52#32),   -- and  v18.16b, v18.16b, v16.16b
    (0x7aa1e8#64,  0x4f415463#32),   -- shl  v3.2d, v3.2d, #1
    (0x7aa1ec#64,  0x6e124252#32),   -- ext  v18.16b, v18.16b, v18.16b, #8
    (0x7aa1f0#64,  0x4e311e10#32),   -- and  v16.16b, v16.16b, v17.16b
    (0x7aa1f4#64,  0x4eb21c63#32),   -- orr  v3.16b, v3.16b, v18.16b
    (0x7aa1f8#64,  0x6e301c74#32),   -- eor  v20.16b, v3.16b, v16.16b
    (0x7aa1fc#64,  0x4c9f7c14#32),   -- st1  {v20.2d}, [x0], #16
    (0x7aa200#64,  0x6e144290#32),   -- ext  v16.16b, v20.16b, v20.16b, #8
    (0x7aa204#64,  0x0ef4e280#32),   -- pmull  v0.1q, v20.1d, v20.1d
    (0x7aa208#64,  0x6e341e10#32),   -- eor  v16.16b, v16.16b, v20.16b
    (0x7aa20c#64,  0x4ef4e282#32),   -- pmull2  v2.1q, v20.2d, v20.2d
    (0x7aa210#64,  0x0ef0e201#32),   -- pmull  v1.1q, v16.1d, v16.1d
    (0x7aa214#64,  0x6e024011#32),   -- ext  v17.16b, v0.16b, v2.16b, #8
    (0x7aa218#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa21c#64,  0x6e311c21#32),   -- eor  v1.16b, v1.16b, v17.16b
    (0x7aa220#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa224#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa228#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa22c#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa230#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa234#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa238#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa23c#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa240#64,  0x6e321c16#32),   -- eor  v22.16b, v0.16b, v18.16b
    (0x7aa244#64,  0x6e1642d1#32),   -- ext  v17.16b, v22.16b, v22.16b, #8
    (0x7aa248#64,  0x6e361e31#32),   -- eor  v17.16b, v17.16b, v22.16b
    (0x7aa24c#64,  0x6e114215#32),   -- ext  v21.16b, v16.16b, v17.16b, #8
    (0x7aa250#64,  0x4c9fac15#32),   -- st1  {v21.2d, v22.2d}, [x0], #32
    (0x7aa254#64,  0x0ef6e280#32),   -- pmull  v0.1q, v20.1d, v22.1d
    (0x7aa258#64,  0x0ef6e2c5#32),   -- pmull  v5.1q, v22.1d, v22.1d
    (0x7aa25c#64,  0x4ef6e282#32),   -- pmull2  v2.1q, v20.2d, v22.2d
    (0x7aa260#64,  0x4ef6e2c7#32),   -- pmull2  v7.1q, v22.2d, v22.2d
    (0x7aa264#64,  0x0ef1e201#32),   -- pmull  v1.1q, v16.1d, v17.1d
    (0x7aa268#64,  0x0ef1e226#32),   -- pmull  v6.1q, v17.1d, v17.1d
    (0x7aa26c#64,  0x6e024010#32),   -- ext  v16.16b, v0.16b, v2.16b, #8
    (0x7aa270#64,  0x6e0740b1#32),   -- ext  v17.16b, v5.16b, v7.16b, #8
    (0x7aa274#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa278#64,  0x6e301c21#32),   -- eor  v1.16b, v1.16b, v16.16b
    (0x7aa27c#64,  0x6e271ca4#32),   -- eor  v4.16b, v5.16b, v7.16b
    (0x7aa280#64,  0x6e311cc6#32),   -- eor  v6.16b, v6.16b, v17.16b
    (0x7aa284#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa288#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa28c#64,  0x6e241cc6#32),   -- eor  v6.16b, v6.16b, v4.16b
    (0x7aa290#64,  0x0ef3e0a4#32),   -- pmull  v4.1q, v5.1d, v19.1d
    (0x7aa294#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa298#64,  0x6e0844c7#32),   -- mov  v7.d[0], v6.d[1]
    (0x7aa29c#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa2a0#64,  0x6e1804a6#32),   -- mov  v6.d[1], v5.d[0]
    (0x7aa2a4#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa2a8#64,  0x6e241cc5#32),   -- eor  v5.16b, v6.16b, v4.16b
    (0x7aa2ac#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa2b0#64,  0x6e0540a4#32),   -- ext  v4.16b, v5.16b, v5.16b, #8
    (0x7aa2b4#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa2b8#64,  0x0ef3e0a5#32),   -- pmull  v5.1q, v5.1d, v19.1d
    (0x7aa2bc#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa2c0#64,  0x6e271c84#32),   -- eor  v4.16b, v4.16b, v7.16b
    (0x7aa2c4#64,  0x6e321c17#32),   -- eor  v23.16b, v0.16b, v18.16b
    (0x7aa2c8#64,  0x6e241cb9#32),   -- eor  v25.16b, v5.16b, v4.16b
    (0x7aa2cc#64,  0x6e1742f0#32),   -- ext  v16.16b, v23.16b, v23.16b, #8
    (0x7aa2d0#64,  0x6e194331#32),   -- ext  v17.16b, v25.16b, v25.16b, #8
    (0x7aa2d4#64,  0x6e1642d2#32),   -- ext  v18.16b, v22.16b, v22.16b, #8
    (0x7aa2d8#64,  0x6e371e10#32),   -- eor  v16.16b, v16.16b, v23.16b
    (0x7aa2dc#64,  0x6e391e31#32),   -- eor  v17.16b, v17.16b, v25.16b
    (0x7aa2e0#64,  0x6e361e52#32),   -- eor  v18.16b, v18.16b, v22.16b
    (0x7aa2e4#64,  0x6e114218#32),   -- ext  v24.16b, v16.16b, v17.16b, #8
    (0x7aa2e8#64,  0x4c9f6c17#32),   -- st1  {v23.2d-v25.2d}, [x0], #48
    (0x7aa2ec#64,  0x0ef7e2c0#32),   -- pmull  v0.1q, v22.1d, v23.1d
    (0x7aa2f0#64,  0x0ef7e2e5#32),   -- pmull  v5.1q, v23.1d, v23.1d
    (0x7aa2f4#64,  0x4ef7e2c2#32),   -- pmull2  v2.1q, v22.2d, v23.2d
    (0x7aa2f8#64,  0x4ef7e2e7#32),   -- pmull2  v7.1q, v23.2d, v23.2d
    (0x7aa2fc#64,  0x0ef2e201#32),   -- pmull  v1.1q, v16.1d, v18.1d
    (0x7aa300#64,  0x0ef0e206#32),   -- pmull  v6.1q, v16.1d, v16.1d
    (0x7aa304#64,  0x6e024010#32),   -- ext  v16.16b, v0.16b, v2.16b, #8
    (0x7aa308#64,  0x6e0740b1#32),   -- ext  v17.16b, v5.16b, v7.16b, #8
    (0x7aa30c#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa310#64,  0x6e301c21#32),   -- eor  v1.16b, v1.16b, v16.16b
    (0x7aa314#64,  0x6e271ca4#32),   -- eor  v4.16b, v5.16b, v7.16b
    (0x7aa318#64,  0x6e311cc6#32),   -- eor  v6.16b, v6.16b, v17.16b
    (0x7aa31c#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa320#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa324#64,  0x6e241cc6#32),   -- eor  v6.16b, v6.16b, v4.16b
    (0x7aa328#64,  0x0ef3e0a4#32),   -- pmull  v4.1q, v5.1d, v19.1d
    (0x7aa32c#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa330#64,  0x6e0844c7#32),   -- mov  v7.d[0], v6.d[1]
    (0x7aa334#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa338#64,  0x6e1804a6#32),   -- mov  v6.d[1], v5.d[0]
    (0x7aa33c#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa340#64,  0x6e241cc5#32),   -- eor  v5.16b, v6.16b, v4.16b
    (0x7aa344#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa348#64,  0x6e0540a4#32),   -- ext  v4.16b, v5.16b, v5.16b, #8
    (0x7aa34c#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa350#64,  0x0ef3e0a5#32),   -- pmull  v5.1q, v5.1d, v19.1d
    (0x7aa354#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa358#64,  0x6e271c84#32),   -- eor  v4.16b, v4.16b, v7.16b
    (0x7aa35c#64,  0x6e321c1a#32),   -- eor  v26.16b, v0.16b, v18.16b
    (0x7aa360#64,  0x6e241cbc#32),   -- eor  v28.16b, v5.16b, v4.16b
    (0x7aa364#64,  0x6e1a4350#32),   -- ext  v16.16b, v26.16b, v26.16b, #8
    (0x7aa368#64,  0x6e1c4391#32),   -- ext  v17.16b, v28.16b, v28.16b, #8
    (0x7aa36c#64,  0x6e1642d2#32),   -- ext  v18.16b, v22.16b, v22.16b, #8
    (0x7aa370#64,  0x6e3a1e10#32),   -- eor  v16.16b, v16.16b, v26.16b
    (0x7aa374#64,  0x6e3c1e31#32),   -- eor  v17.16b, v17.16b, v28.16b
    (0x7aa378#64,  0x6e361e52#32),   -- eor  v18.16b, v18.16b, v22.16b
    (0x7aa37c#64,  0x6e11421b#32),   -- ext  v27.16b, v16.16b, v17.16b, #8
    (0x7aa380#64,  0x4c9f6c1a#32),   -- st1  {v26.2d-v28.2d}, [x0], #48
    (0x7aa384#64,  0x0efae2c0#32),   -- pmull  v0.1q, v22.1d, v26.1d
    (0x7aa388#64,  0x0efce2c5#32),   -- pmull  v5.1q, v22.1d, v28.1d
    (0x7aa38c#64,  0x4efae2c2#32),   -- pmull2  v2.1q, v22.2d, v26.2d
    (0x7aa390#64,  0x4efce2c7#32),   -- pmull2  v7.1q, v22.2d, v28.2d
    (0x7aa394#64,  0x0ef2e201#32),   -- pmull  v1.1q, v16.1d, v18.1d
    (0x7aa398#64,  0x0ef2e226#32),   -- pmull  v6.1q, v17.1d, v18.1d
    (0x7aa39c#64,  0x6e024010#32),   -- ext  v16.16b, v0.16b, v2.16b, #8
    (0x7aa3a0#64,  0x6e0740b1#32),   -- ext  v17.16b, v5.16b, v7.16b, #8
    (0x7aa3a4#64,  0x6e221c12#32),   -- eor  v18.16b, v0.16b, v2.16b
    (0x7aa3a8#64,  0x6e301c21#32),   -- eor  v1.16b, v1.16b, v16.16b
    (0x7aa3ac#64,  0x6e271ca4#32),   -- eor  v4.16b, v5.16b, v7.16b
    (0x7aa3b0#64,  0x6e311cc6#32),   -- eor  v6.16b, v6.16b, v17.16b
    (0x7aa3b4#64,  0x6e321c21#32),   -- eor  v1.16b, v1.16b, v18.16b
    (0x7aa3b8#64,  0x0ef3e012#32),   -- pmull  v18.1q, v0.1d, v19.1d
    (0x7aa3bc#64,  0x6e241cc6#32),   -- eor  v6.16b, v6.16b, v4.16b
    (0x7aa3c0#64,  0x0ef3e0a4#32),   -- pmull  v4.1q, v5.1d, v19.1d
    (0x7aa3c4#64,  0x6e084422#32),   -- mov  v2.d[0], v1.d[1]
    (0x7aa3c8#64,  0x6e0844c7#32),   -- mov  v7.d[0], v6.d[1]
    (0x7aa3cc#64,  0x6e180401#32),   -- mov  v1.d[1], v0.d[0]
    (0x7aa3d0#64,  0x6e1804a6#32),   -- mov  v6.d[1], v5.d[0]
    (0x7aa3d4#64,  0x6e321c20#32),   -- eor  v0.16b, v1.16b, v18.16b
    (0x7aa3d8#64,  0x6e241cc5#32),   -- eor  v5.16b, v6.16b, v4.16b
    (0x7aa3dc#64,  0x6e004012#32),   -- ext  v18.16b, v0.16b, v0.16b, #8
    (0x7aa3e0#64,  0x6e0540a4#32),   -- ext  v4.16b, v5.16b, v5.16b, #8
    (0x7aa3e4#64,  0x0ef3e000#32),   -- pmull  v0.1q, v0.1d, v19.1d
    (0x7aa3e8#64,  0x0ef3e0a5#32),   -- pmull  v5.1q, v5.1d, v19.1d
    (0x7aa3ec#64,  0x6e221e52#32),   -- eor  v18.16b, v18.16b, v2.16b
    (0x7aa3f0#64,  0x6e271c84#32),   -- eor  v4.16b, v4.16b, v7.16b
    (0x7aa3f4#64,  0x6e321c1d#32),   -- eor  v29.16b, v0.16b, v18.16b
    (0x7aa3f8#64,  0x6e241cbf#32),   -- eor  v31.16b, v5.16b, v4.16b
    (0x7aa3fc#64,  0x6e1d43b0#32),   -- ext  v16.16b, v29.16b, v29.16b, #8
    (0x7aa400#64,  0x6e1f43f1#32),   -- ext  v17.16b, v31.16b, v31.16b, #8
    (0x7aa404#64,  0x6e3d1e10#32),   -- eor  v16.16b, v16.16b, v29.16b
    (0x7aa408#64,  0x6e3f1e31#32),   -- eor  v17.16b, v17.16b, v31.16b
    (0x7aa40c#64,  0x6e11421e#32),   -- ext  v30.16b, v16.16b, v17.16b, #8
    (0x7aa410#64,  0x4c006c1d#32),   -- st1  {v29.2d-v31.2d}, [x0]
    (0x7aa414#64,  0xd65f03c0#32),   -- ret
  ]

end GCMInitV8Program
