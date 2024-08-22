/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Tests.ELFParser.SymbolContents

private def RELTestELF := (getELFFile (System.mkFilePath ["Tests", "ELFParser", "Data", "test.o"]))
/--
info: [(0x0000000000000000#64, 0xa9be7bfd#32),
 (0x0000000000000001#64, 0x910003fd#32),
 (0x0000000000000002#64, 0x92800000#32),
 (0x0000000000000003#64, 0x94000000#32),
 (0x0000000000000004#64, 0xf9000fa0#32),
 (0x0000000000000005#64, 0x90000000#32),
 (0x0000000000000006#64, 0x91000000#32),
 (0x0000000000000007#64, 0xf9400fa1#32),
 (0x0000000000000008#64, 0x94000000#32),
 (0x0000000000000009#64, 0x52800000#32),
 (0x000000000000000a#64, 0xa8c27bfd#32),
 (0x000000000000000b#64, 0xd65f03c0#32)]
-/
#guard_msgs in
#eval do (pure (getSymbolMap "main" (← RELTestELF)))

private def DYNTestELF := (getELFFile (System.mkFilePath ["Tests", "ELFParser", "Data", "libtest.so"]))
/--
info: [(0x0000000000000770#64, 0xa9be7bfd#32),
 (0x0000000000000771#64, 0x910003fd#32),
 (0x0000000000000772#64, 0x92800000#32),
 (0x0000000000000773#64, 0x97ffffbd#32),
 (0x0000000000000774#64, 0xf9000fa0#32),
 (0x0000000000000775#64, 0x90000000#32),
 (0x0000000000000776#64, 0x911ec000#32),
 (0x0000000000000777#64, 0xf9400fa1#32),
 (0x0000000000000778#64, 0x97ffffbc#32),
 (0x0000000000000779#64, 0x52800000#32),
 (0x000000000000077a#64, 0xa8c27bfd#32),
 (0x000000000000077b#64, 0xd65f03c0#32)]
-/
#guard_msgs in
#eval do (pure (getSymbolMap "main" (← DYNTestELF)))
