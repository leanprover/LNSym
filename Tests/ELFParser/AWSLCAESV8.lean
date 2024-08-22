/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Tests.ELFParser.AWSLCCrypto

-- Importing just the aesv8-armx.S.o file to avoid relying on the
-- linker-generated addresses.
-- Details: PC-relative addressing is often used for locating constants.
-- The addresses can change every time linking happens, which
-- means that the 32-bit hex for instructions that use PC-relative offsets
-- can change. This causes the values obtained by `getSymbolWords` to vary
-- and causes `#guard_msgs` to fail.
--
-- We use the .o files to avoid having to deal with the repercussions of
-- such potential address changes.
def AESV8ELF :=
  (getELFFile (System.mkFilePath
    ["Tests", "ELFParser", "Data", "aws-lc-build", "crypto",
    "fipsmodule", "CMakeFiles", "fipsmodule.dir",
    "aesv8-armx.S.o"]))

/--
info: [0xa9bf7bfd#32,
 0x910003fd#32,
 0x92800003#32,
 0xf100001f#32,
 0x54000f60#32,
 0xf100005f#32,
 0x54000f20#32,
 0x92800023#32,
 0x7102003f#32,
 0x54000ecb#32,
 0x7104003f#32,
 0x54000e8c#32,
 0x7200143f#32,
 0x54000e41#32,
 0x90000003#32,
 0x91000063#32,
 0x7103003f#32,
 0x6e201c00#32,
 0x4cdf7003#32,
 0x52800101#32,
 0x4cdfa861#32,
 0x5400006b#32,
 0x540005c0#32,
 0x14000049#32,
 0x4e020066#32,
 0x6e036005#32,
 0x4c9f7843#32,
 0x4e284806#32,
 0x71000421#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e211cc6#32,
 0x6e251c63#32,
 0x4f095421#32,
 0x6e261c63#32,
 0x54fffe61#32,
 0x4c407861#32,
 0x4e020066#32,
 0x6e036005#32,
 0x4c9f7843#32,
 0x4e284806#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e211cc6#32,
 0x6e251c63#32,
 0x4f095421#32,
 0x6e261c63#32,
 0x4e020066#32,
 0x6e036005#32,
 0x4c9f7843#32,
 0x4e284806#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e211cc6#32,
 0x6e251c63#32,
 0x6e261c63#32,
 0x4c007843#32,
 0x91014042#32,
 0x5280014c#32,
 0x1400003c#32,
 0xd503201f#32,
 0xd503201f#32,
 0x0cdf7004#32,
 0x4f00e506#32,
 0x4c9f7843#32,
 0x6e268442#32,
 0x4e020086#32,
 0x6e036005#32,
 0x0c9f7044#32,
 0x4e284806#32,
 0x71000421#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e251c63#32,
 0x4e1c0465#32,
 0x6e241ca5#32,
 0x6e211cc6#32,
 0x6e046004#32,
 0x4f095421#32,
 0x6e251c84#32,
 0x6e261c63#32,
 0x6e261c84#32,
 0x4c9f7843#32,
 0x54fffda1#32,
 0x5280018c#32,
 0x91008042#32,
 0x1400001f#32,
 0xd503201f#32,
 0x4c407004#32,
 0x528000e1#32,
 0x528001cc#32,
 0x4c9f7843#32,
 0x4e020086#32,
 0x6e036005#32,
 0x4c9f7844#32,
 0x4e284806#32,
 0x71000421#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e251c63#32,
 0x6e056005#32,
 0x6e211cc6#32,
 0x6e251c63#32,
 0x4f095421#32,
 0x6e261c63#32,
 0x4c9f7843#32,
 0x54000160#32,
 0x4e1c0466#32,
 0x6e046005#32,
 0x4e284806#32,
 0x6e251c84#32,
 0x6e056005#32,
 0x6e251c84#32,
 0x6e056005#32,
 0x6e251c84#32,
 0x6e261c84#32,
 0x17ffffe8#32,
 0xb900004c#32,
 0xd2800003#32,
 0xaa0303e0#32,
 0xf84107fd#32,
 0xd65f03c0#32]
-/
#guard_msgs in
#eval do (getSymbolWords "aes_hw_set_encrypt_key" (← AESV8ELF))

/--
info: [0x00000001#32,
 0x00000001#32,
 0x00000001#32,
 0x00000001#32,
 0x0c0f0e0d#32,
 0x0c0f0e0d#32,
 0x0c0f0e0d#32,
 0x0c0f0e0d#32,
 0x0000001b#32,
 0x0000001b#32,
 0x0000001b#32,
 0x0000001b#32]
-/
#guard_msgs in
#eval do (getSymbolWords ".Lrcon" (← CryptoELF))

/--
info: [0xb940f043#32,
 0x4cdf7840#32,
 0x4c407002#32,
 0x51000863#32,
 0x4cdf7841#32,
 0x4e284802#32,
 0x4e286842#32,
 0x4cdf7840#32,
 0x71000863#32,
 0x4e284822#32,
 0x4e286842#32,
 0x4cdf7841#32,
 0x54ffff2c#32,
 0x4e284802#32,
 0x4e286842#32,
 0x4c407840#32,
 0x4e284822#32,
 0x6e201c42#32,
 0x4c007022#32,
 0xd65f03c0#32]
-/
#guard_msgs in
#eval do (getSymbolWords "aes_hw_encrypt" (← CryptoELF))

/--
info: [0xa9bf7bfd#32,
 0x910003fd#32,
 0xb940f065#32,
 0xb9400c88#32,
 0x4c407880#32,
 0x4c40a870#32,
 0x510010a5#32,
 0xd280020c#32,
 0xf100085f#32,
 0x8b051067#32,
 0x510008a5#32,
 0x4cdfa8f4#32,
 0x4cdfa8f6#32,
 0x4c4078e7#32,
 0x91008067#32,
 0x2a0503e6#32,
 0x5ac00908#32,
 0x1100050a#32,
 0x4ea01c06#32,
 0x5ac0094a#32,
 0x4e1c1d46#32,
 0x11000908#32,
 0x4ea61cc1#32,
 0x54000b49#32,
 0x5ac0090c#32,
 0x4e1c1d86#32,
 0xd1000c42#32,
 0x4ea61cd2#32,
 0x14000004#32,
 0xd503201f#32,
 0xd503201f#32,
 0xd503201f#32,
 0x4e284a00#32,
 0x4e286800#32,
 0x4e284a01#32,
 0x4e286821#32,
 0x4e284a12#32,
 0x4e286a52#32,
 0x4cdf78f0#32,
 0x710008c6#32,
 0x4e284a20#32,
 0x4e286800#32,
 0x4e284a21#32,
 0x4e286821#32,
 0x4e284a32#32,
 0x4e286a52#32,
 0x4cdf78f1#32,
 0x54fffe2c#32,
 0x4e284a00#32,
 0x4e286804#32,
 0x4e284a01#32,
 0x4e286825#32,
 0x4cdf7002#32,
 0x11000509#32,
 0x4e284a12#32,
 0x4e286a52#32,
 0x4cdf7003#32,
 0x5ac00929#32,
 0x4e284a24#32,
 0x4e286884#32,
 0x4e284a25#32,
 0x4e2868a5#32,
 0x4cdf7013#32,
 0xaa0303e7#32,
 0x4e284a32#32,
 0x4e286a51#32,
 0x4e284a84#32,
 0x4e286884#32,
 0x4e284a85#32,
 0x4e2868a5#32,
 0x6e271c42#32,
 0x1100090a#32,
 0x4e284a91#32,
 0x4e286a31#32,
 0x6e271c63#32,
 0x11000d08#32,
 0x4e284aa4#32,
 0x4e286884#32,
 0x4e284aa5#32,
 0x4e2868a5#32,
 0x6e271e73#32,
 0x4e1c1d26#32,
 0x4e284ab1#32,
 0x4e286a31#32,
 0x4ea61cc0#32,
 0x5ac0094a#32,
 0x4e284ac4#32,
 0x4e286884#32,
 0x4e1c1d46#32,
 0x5ac0090c#32,
 0x4e284ac5#32,
 0x4e2868a5#32,
 0x4ea61cc1#32,
 0x4e1c1d86#32,
 0x4e284ad1#32,
 0x4e286a31#32,
 0x4ea61cd2#32,
 0xf1000c42#32,
 0x4e284ae4#32,
 0x4e284ae5#32,
 0x4e284af1#32,
 0x6e241c42#32,
 0x4cdf78f0#32,
 0x4c9f7022#32,
 0x6e251c63#32,
 0x2a0503e6#32,
 0x4c9f7023#32,
 0x6e311e73#32,
 0x4cdf78f1#32,
 0x4c9f7033#32,
 0x54fff642#32,
 0xb1000c42#32,
 0x54000600#32,
 0xf100045f#32,
 0x540005cb#32,
 0xd280020c#32,
 0x9a8c03ec#32,
 0x4e284a00#32,
 0x4e286800#32,
 0x4e284a01#32,
 0x4e286821#32,
 0x4cdf78f0#32,
 0x710008c6#32,
 0x4e284a20#32,
 0x4e286800#32,
 0x4e284a21#32,
 0x4e286821#32,
 0x4cdf78f1#32,
 0x54fffe2c#32,
 0x4e284a00#32,
 0x4e286800#32,
 0x4e284a01#32,
 0x4e286821#32,
 0x4e284a20#32,
 0x4e286800#32,
 0x4e284a21#32,
 0x4e286821#32,
 0x4ccc7002#32,
 0x4e284a80#32,
 0x4e286800#32,
 0x4e284a81#32,
 0x4e286821#32,
 0x4c407003#32,
 0x4e284aa0#32,
 0x4e286800#32,
 0x4e284aa1#32,
 0x4e286821#32,
 0x6e271c42#32,
 0x4e284ac0#32,
 0x4e286800#32,
 0x4e284ac1#32,
 0x4e286821#32,
 0x6e271c63#32,
 0x4e284ae0#32,
 0x4e284ae1#32,
 0x6e201c42#32,
 0x6e211c63#32,
 0x4c9f7022#32,
 0xb400004c#32,
 0x4c007023#32,
 0xf84107fd#32,
 0xd65f03c0#32]
-/
#guard_msgs in
#eval do (getSymbolWords "aes_hw_ctr32_encrypt_blocks" (← CryptoELF))
