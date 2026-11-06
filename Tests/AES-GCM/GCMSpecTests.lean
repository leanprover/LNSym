/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Specs.GCMV8
import Tests.«AES-GCM».GCMProgramTests

open BitVec

namespace GCMInitV8SpecTest

def flatten_H := BitVec.flatten GCMProgramTestParams.H
def spec_table := GCMV8.GCMInitV8 flatten_H

example : extractLsb' 0 (12 * 128) (revflat spec_table)
        = extractLsb' 0 (12 * 128) (revflat GCMProgramTestParams.Htable)
        := by native_decide

end GCMInitV8SpecTest

namespace GCMGmultV8SpecTest

def H : BitVec 128 :=
  GCMProgramTestParams.Htable[1]! ++
  GCMProgramTestParams.Htable[0]!
def X0 := GCMProgramTestParams.X[0]!
def X1 := GCMProgramTestParams.X[1]!

-- v4.16: no-progress simp → decide
example : GCMV8.GCMGmultV8 H X0 (by decide) = X1 := by native_decide

end GCMGmultV8SpecTest

namespace GCMGhashV8SpecTest

def H : BitVec 128 :=
  GCMProgramTestParams.Htable[1]! ++
  GCMProgramTestParams.Htable[0]!
def X1 := GCMProgramTestParams.X[1]!
def X2 := GCMProgramTestParams.X[2]!
def X3 := GCMProgramTestParams.X[3]!
def inp1 := List.replicate 16 0x2a#8
def inp2 := List.replicate 32 0x2a#8

example : GCMV8.GCMGhashV8 H X1 inp1 (by decide)
            (by decide) = X2 := by native_decide

example : GCMV8.GCMGhashV8 H X2 inp2 (by decide)
            (by decide) = X3 := by native_decide

end GCMGhashV8SpecTest
