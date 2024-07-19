/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec

def revflat (x : List (BitVec n)) : BitVec (n * x.length) := 
  have h : n * x.reverse.length = n * x.length := by simp only [List.length_reverse]
  BitVec.cast h $ BitVec.flatten (List.reverse x)
