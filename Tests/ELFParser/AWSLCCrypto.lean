/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Tests.ELFParser.SymbolContents

def CryptoELF := (getELFFile (System.mkFilePath ["Tests", "ELFParser", "Data", "crypto_test"]))

/--
info: true -/
#guard_msgs in
#eval do (pure (← CryptoELF).is64Bit)

/--
info: false -/
#guard_msgs in
#eval do (pure (← CryptoELF).isBigendian)
