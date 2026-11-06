/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Tests.ELFParser.SymbolContents

private def RELTestELF := (getELFFile (System.mkFilePath ["Tests", "ELFParser", "Data", "test.o"]))
/--
info: [(0#64, 2847833085#32), (1#64, 2432697341#32), (2#64, 2457862144#32), (3#64, 2483027968#32), (4#64, 4177530784#32),
  (5#64, 2415919104#32), (6#64, 2432696320#32), (7#64, 4181725089#32), (8#64, 2483027968#32), (9#64, 1384120320#32),
  (10#64, 2831318013#32), (11#64, 3596551104#32)]
-/
#guard_msgs in
#eval do getSymbolMap "main" (← RELTestELF)

private def DYNTestELF := (getELFFile (System.mkFilePath ["Tests", "ELFParser", "Data", "libtest.so"]))
/--
info: [(1904#64, 2847833085#32), (1905#64, 2432697341#32), (1906#64, 2457862144#32), (1907#64, 2550136765#32),
  (1908#64, 4177530784#32), (1909#64, 2415919104#32), (1910#64, 2434711552#32), (1911#64, 4181725089#32),
  (1912#64, 2550136764#32), (1913#64, 1384120320#32), (1914#64, 2831318013#32), (1915#64, 3596551104#32)]
-/
#guard_msgs in
#eval do getSymbolMap "main" (← DYNTestELF)
