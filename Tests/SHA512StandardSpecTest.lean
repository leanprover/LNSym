/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import «Tests».SHA512SpecTest

section SHA512StandardSpecTest

open BitVec

-- See https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf

-- Standard version
def ms_standard := (SHA2.message_schedule 0 SHA2.j_512)

def ans_one_blk_standard : IO SHA2.Hash := do
  pure (SHA2.sha512 ms_standard ms_one_block)
#eval timeit "sha512 one block (standard):" ans_one_blk_standard -- ~45 seconds

example : SHA2.sha512 ms_standard ms_one_block = expected := by
  native_decide

-- Standard version takes too long for testing two message blocks, so
-- we don't even try it here.

end SHA512StandardSpecTest
