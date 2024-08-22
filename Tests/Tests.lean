/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import «Tests».SHA2.SHA512SpecTest
-- Commenting out the standard spec. test --- it takes too long to
-- build/execute and also bloats the lnsym binary.
-- import «Tests».SHA2.SHA512StandardSpecTest
import «Tests».SHA2.SHA512ProgramTest
import «Tests».LDSTTest
import «Tests».«AES-GCM».AESSpecTest
import «Tests».«AES-GCM».AESGCMSpecTest
import «Tests».«AES-GCM».GCMProgramTests
import «Tests».«AES-GCM».GCMSpecTests
import «Tests».«AES-GCM».AESV8ProgramTests
import «Tests».«AES-GCM».AESV8SpecTests
import «Tests».«AES-GCM».AESGCMProgramTests
import «Tests».«ELFParser».MiscTests
import «Tests».Tactics.CSE
import «Tests».Tactics.Sym
import «Tests».Tactics.ReduceFetchInst
