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

example : extractLsb (12 * 128) 0 (revflat spec_table)
        = extractLsb (12 * 128) 0 (revflat GCMProgramTestParams.Htable) := by native_decide

end GCMInitV8SpecTest

namespace GCMGmultV8SpecTest

def H : BitVec 128 :=
  List.get! GCMProgramTestParams.Htable 1 ++
  List.get! GCMProgramTestParams.Htable 0
def X0 := List.get! GCMProgramTestParams.X 0
def X1 := List.get! GCMProgramTestParams.X 1

example : have h : 8 * X0.length = 128 := by simp [List.length]
  GCMV8.GCMGmultV8 H X0 h = X1 := by native_decide

end GCMGmultV8SpecTest

namespace GCMGhashV8SpecTest

def H : BitVec 128 :=
  List.get! GCMProgramTestParams.Htable 1 ++
  List.get! GCMProgramTestParams.Htable 0
def X1 := List.get! GCMProgramTestParams.X 1
def X2 := List.get! GCMProgramTestParams.X 2
def X3 := List.get! GCMProgramTestParams.X 3
def inp1 := List.replicate 16 0x2a#8
def inp2 := List.replicate 32 0x2a#8

example : have h1 : X1.length = 16 := by simp [List.length]
  have h2 : 16 ∣ inp1.length := by simp [List.length]; omega
  GCMV8.GCMGhashV8 H X1 inp1 h1 h2 = X2 := by native_decide

example : have h1 : X2.length = 16 := by simp [List.length]
  have h2 : 16 ∣ inp2.length := by simp [List.length]; omega
  GCMV8.GCMGhashV8 H X2 inp2 h1 h2 = X3 := by native_decide

end GCMGhashV8SpecTest
