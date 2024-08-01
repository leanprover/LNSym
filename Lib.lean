/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

We collect all modules in LNsym to build a single library for documentation generation.
-/

import Arm
import Main
import Proofs
/-
Enabling `tests` seems to cause `doc-gen4` to fail entirely, so we disable it for the time being.
Expected behaviour: `doc-gen4` must gracefully bail out.
trace: .> ELAN_HOME=/Users/sidbhatz/.elan ELAN_TOOLCHAIN=leanprover/lean4:nightly-2024-07-25 LAKE=/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25/bin/lake LAKE_HOME=/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25 LAKE_PKG_URL_MAP={} LEAN_GITHASH=39e0b41fe1ab4d16f15efb0dc9bd7607a8941713 LEAN_SYSROOT=/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25 LEAN_AR=/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25/bin/llvm-ar LEAN_CC= LEAN_PATH=././.lake/packages/LeanSAT/.lake/build/lib:././.lake/packages/Cli/.lake/build/lib:././.lake/packages/ELFSage/.lake/build/lib:././.lake/packages/MD4Lean/.lake/build/lib:././.lake/packages/UnicodeBasic/.lake/build/lib:././.lake/packages/BibtexQuery/.lake/build/lib:././.lake/packages/doc-gen4/.lake/build/lib:././.lake/build/lib:/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25/lib/lean LEAN_SRC_PATH=././.lake/packages/LeanSAT/./.:././.lake/packages/LeanSAT/./.:././.lake/packages/LeanSAT/./.:././.lake/packages/Cli/./.:././.lake/packages/ELFSage/./.:././.lake/packages/MD4Lean/./.:././.lake/packages/UnicodeBasic/./.:././.lake/packages/BibtexQuery/./.:././.lake/packages/doc-gen4/./.:./././.:./././.:./././.:./././.:./././.:./././.:/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25/src/lean/lake PATH DYLD_LIBRARY_PATH=././.lake/packages/LeanSAT/.lake/build/lib:././.lake/packages/Cli/.lake/build/lib:././.lake/packages/ELFSage/.lake/build/lib:././.lake/packages/MD4Lean/.lake/build/lib:././.lake/packages/UnicodeBasic/.lake/build/lib:././.lake/packages/BibtexQuery/.lake/build/lib:././.lake/packages/doc-gen4/.lake/build/lib:././.lake/build/lib:/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25/lib/lean:/Users/sidbhatz/.elan/toolchains/leanprover--lean4---nightly-2024-07-25/lib ././.lake/packages/doc-gen4/.lake/build/bin/doc-gen4 single Tests.«AES-GCM».AESHWCtr32EncryptBlocksProgram https://github.com/bollu/LNSym/blob/ac7b1e50d8925adf166b67f7a4c0854f901d5810/Tests/«AES-GCM»/AESHWCtr32EncryptBlocksProgram.lean
error: no such file or directory (error code: 2)
  file: ././.lake/build/doc/Tests/AES-GCM/AESHWCtr32EncryptBlocksProgram.html
-/
-- import Tests
import Tactics
