/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/

import Specs.AESArm

-- Reference : https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf Section B

-- Testing AES-128 encryption of one message block

namespace AESSpecTest

open BitVec

-- The specification expects little-endian input
protected def input : BitVec 128 :=
  BitVec.flatten
    [ 0x32#8, 0x43#8, 0xf6#8, 0xa8#8,
      0x88#8, 0x5a#8, 0x30#8, 0x8d#8,
      0x31#8, 0x31#8, 0x98#8, 0xa2#8,
      0xe0#8, 0x37#8, 0x07#8, 0x34#8 ].reverse

protected def key : BitVec 128 :=
  BitVec.flatten
    [ 0x2b#8, 0x7e#8, 0x15#8, 0x16#8,
      0x28#8, 0xae#8, 0xd2#8, 0xa6#8,
      0xab#8, 0xf7#8, 0x15#8, 0x88#8,
      0x09#8, 0xcf#8, 0x4f#8, 0x3c#8 ].reverse

protected def output : BitVec 128 :=
  BitVec.flatten
    [ 0x39#8, 0x25#8, 0x84#8, 0x1d#8,
      0x02#8, 0xdc#8, 0x09#8, 0xfb#8,
      0xdc#8, 0x11#8, 0x85#8, 0x97#8,
      0x19#8, 0x6a#8, 0x0b#8, 0x32#8 ].reverse

example : AESArm.AES_encrypt (Param := AESArm.AES128KBR) AESSpecTest.input AESSpecTest.key = AESSpecTest.output := by native_decide

end AESSpecTest
