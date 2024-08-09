/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Data.BitVec

namespace sha512_helpers

open BitVec

def sigma_big_0 (op : BitVec 64) : BitVec 64 :=
  (BitVec.ror op 28) ^^^ (BitVec.ror op 34) ^^^ (BitVec.ror op 39)

def sigma_big_1 (op : BitVec 64) : BitVec 64 :=
   (BitVec.ror op 14) ^^^ (BitVec.ror op 18) ^^^ (BitVec.ror op 41)

def sigma_0 (op : BitVec 64) : BitVec 64 :=
  (BitVec.ror op 1) ^^^ (BitVec.ror op 8) ^^^ (op >>> 7)

def sigma_1 (op : BitVec 64) : BitVec 64 :=
  (BitVec.ror op 19) ^^^ (BitVec.ror op 61) ^^^ (op >>> 6)      

def ch (op1 : BitVec 64) (op2 : BitVec 64) (op3 : BitVec 64)
  : BitVec 64 :=
  (op1 &&& op2) ^^^ ((~~~op1) &&& op3)

def maj (op1 : BitVec 64) (op2 : BitVec 64) (op3 : BitVec 64)
  : BitVec 64 :=
  ((op1 &&& op2) ^^^ (op1 &&& op3)) ^^^ (op2 &&& op3)

end sha512_helpers
