/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
import Specs.SHA512
import Init.System.IO

section SHA512SpecTest

open BitVec

-- See https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf

-- Also see SHA512StandardSpecTest.lean which contains a test for the
-- Lean spec. of SHA512 that follows the NIST standard.

----------------------------------------------------------------------

---- One block test ----

def ms_one_block : List (List (BitVec 64)) :=
  open BitVec in
  [[0x6162638000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000018#64]]

def expected : SHA2.Hash :=
  open BitVec in
  { a := 0xddaf35a193617aba#64,
    b := 0xcc417349ae204131#64,
    c := 0x12e6fa4e89a97ea2#64,
    d := 0x0a9eeee64b55d39a#64,
    e := 0x2192992a274fc1a8#64,
    f := 0x36ba3c23a3feebbd#64,
    g := 0x454d4423643ce80e#64,
    h := 0x2a9ac94fa54ca49f#64 }

-- Memoized version
def ms_mem := (SHA2.message_schedule_mem 0 SHA2.j_512 [])

def ans_one_blk_mem : IO SHA2.Hash := do
  pure (SHA2.sha512 ms_mem ms_one_block)
-- #eval timeit "sha512 one block (memoized):" ans_one_blk_mem -- ~11 ms

example : SHA2.sha512 ms_mem ms_one_block = expected := by
  native_decide

-- #time
-- example : SHA2.processBlocks_alt SHA2.j_512 SHA2.h0_512 SHA2.k_512 ms_one_block =
--           expected := by native_decide

-- Lazy version
def ms_lazy := (SHA2.message_schedule_lazy SHA2.j_512)

def ans_one_blk_lazy : IO SHA2.Hash := do
  pure (SHA2.sha512 ms_lazy ms_one_block)

-- #eval timeit "sha512 one block (lazy lists):" ans_one_blk_lazy -- ~20 ms

-- example : SHA2.sha512 ms_lazy ms_one_block = expected := by
--  native_decide

----------------------------------------------------------------------

---- Two blocks test ----

def ms_two_blocks : List (List (BitVec 64)) :=
  open BitVec in
  [[0x6162636465666768#64,
    0x6263646566676869#64,
    0x636465666768696A#64,
    0x6465666768696A6B#64,
    0x65666768696A6B6C#64,
    0x666768696A6B6C6D#64,
    0x6768696A6B6C6D6E#64,
    0x68696A6B6C6D6E6F#64,
    0x696A6B6C6D6E6F70#64,
    0x6A6B6C6D6E6F7071#64,
    0x6B6C6D6E6F707172#64,
    0x6C6D6E6F70717273#64,
    0x6D6E6F7071727374#64,
    0x6E6F707172737475#64,
    0x8000000000000000#64,
    0x0000000000000000#64],
   [0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000000#64,
    0x0000000000000380#64]]

def expected2 : SHA2.Hash :=
  open BitVec in
  { a := 0x8e959b75dae313da#64,
    b := 0x8cf4f72814fc143f#64,
    c := 0x8f7779c6eb9f7fa1#64,
    d := 0x7299aeadb6889018#64,
    e := 0x501d289e4900f7e4#64,
    f := 0x331b99dec4b5433a#64,
    g := 0xc7d329eeb6dd2654#64,
    h := 0x5e96e55b874be909#64 }

-- Memoized version
def ans_two_blks_mem : IO SHA2.Hash := do
  pure (SHA2.sha512 ms_mem ms_two_blocks)

-- #eval timeit "sha512 two blocks (memoized):" ans_two_blks_mem -- ~16 ms

example : SHA2.sha512 ms_mem ms_two_blocks = expected2 := by
  native_decide

-- Lazy version
def ans_two_blks_lazy : IO SHA2.Hash := do
  pure (SHA2.sha512 ms_lazy ms_two_blocks)

-- #eval timeit "sha512 two blocks (lazy lists):" ans_two_blks_lazy -- ~17 ms

-- example : SHA2.sha512 ms_lazy ms_two_blocks = expected2 := by
--   native_decide

end SHA512SpecTest
