/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import «Tests».SHA512SpecTest
-- Commenting out the standard spec. test --- it takes too long to
-- build/execute and also bloats the lnsym binary.
-- import «Tests».SHA512StandardSpecTest
import «Tests».SHA512ProgramTest
import «Tests».LDSTTest
import «Tests».AESSpecTest
import «Tests».AESGCMSpecTest

