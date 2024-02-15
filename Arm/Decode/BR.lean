/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
import Arm.BitVec

------------------------------------------------------------------------------

section Decode

open Std.BitVec

-- Branches, Exception Generating and System Instructions

structure Compare_branch_inst where
  sf     : BitVec 1               -- [31:31]
  _fixed : BitVec 5 := 0b011010#5 -- [30:25]
  op     : BitVec 1               -- [24:24]
  imm19  : BitVec 19              -- [23:5]
  Rt     : BitVec 5               --  [4:0]
deriving DecidableEq, Repr

instance : ToString Compare_branch_inst where toString a := toString (repr a)

structure Uncond_branch_imm_inst where
  op     : BitVec 1              -- [31:31]
  _fixed : BitVec 5 := 0b00101#5 -- [30:26]
  imm26  : BitVec 26             --  [25:0]
deriving DecidableEq, Repr

instance : ToString Uncond_branch_imm_inst where toString a := toString (repr a)

structure Uncond_branch_reg_inst where
  _fixed : BitVec 7 := 0b1101011#7 -- [31:25]
  opc    : BitVec 4                -- [24:21]
  op2    : BitVec 5                -- [20:16]
  op3    : BitVec 6                -- [15:10]
  Rn     : BitVec 5                --   [9:5]
  -- This field is indeed called
  -- op4 in the Arm manual; note
  -- that the width is 5 bits.
  op4    : BitVec 5                --  [4:0]
deriving DecidableEq, Repr

instance : ToString Uncond_branch_reg_inst where toString a := toString (repr a)

structure Cond_branch_imm_inst where
  _fixed : BitVec 8 := 0b01010100#8 -- [31:24]
  imm19  : BitVec 19                -- [23:5]
  o0     : BitVec 1                 -- [4:4]
  cond   : BitVec 4                 -- [3:0]
deriving DecidableEq, Repr

instance : ToString Cond_branch_imm_inst where toString a := toString (repr a)

inductive BranchInst where
  | Compare_branch :
    Compare_branch_inst → BranchInst
  | Uncond_branch_imm :
    Uncond_branch_imm_inst → BranchInst
  | Uncond_branch_reg :
    Uncond_branch_reg_inst → BranchInst
  | Cond_branch_imm :
    Cond_branch_imm_inst → BranchInst
deriving DecidableEq, Repr

instance : ToString BranchInst where toString a := toString (repr a)

end Decode
