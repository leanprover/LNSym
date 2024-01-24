/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.BitVec

------------------------------------------------------------------------------

section Decode

open Std.BitVec

-- Data Processing (Register) Instructions --

structure Add_sub_carry_cls where
  sf      : BitVec 1                 -- [31:31]
  op      : BitVec 1                 -- [30:30]
  S       : BitVec 1                 -- [29:29]
  _fixed1 : BitVec 8 := 0b11010000#8 -- [28:21]
  Rm      : BitVec 5                 -- [20:16]
  _fixed2 : BitVec 6 := 0b000000#6   -- [15:10]
  Rn      : BitVec 5                 --   [9:5]
  Rd      : BitVec 5                 --   [4:0]
deriving DecidableEq, Repr

instance : ToString Add_sub_carry_cls where toString a := toString (repr a)

def Add_sub_carry_cls.toBitVec32 (x : Add_sub_carry_cls) : BitVec 32 :=
  x.sf ++ x.op ++ x.S ++ x._fixed1 ++ x.Rm ++ x._fixed2 ++ x.Rn ++ x.Rd

structure Conditional_select_cls where
  sf     : BitVec 1                 -- [31:31]
  op     : BitVec 1                 -- [30:30]
  S      : BitVec 1                 -- [29:29]
  _fixed : BitVec 8 := 0b11010100#8 -- [28:21]
  Rm     : BitVec 5                 -- [20:16]
  cond   : BitVec 4                 -- [15:12]
  op2    : BitVec 2                 -- [11:10]
  Rn     : BitVec 5                 --   [9:5]
  Rd     : BitVec 5                 --   [4:0]
deriving DecidableEq, Repr

instance : ToString Conditional_select_cls where toString a := toString (repr a)

def Conditional_select_cls.toBitVec32 (x : Conditional_select_cls) : BitVec 32 :=
  x.sf ++ x.op ++ x.S ++ x._fixed ++ x.Rm ++ x.cond ++ x.op2 ++ x.Rn ++ x.Rd

structure Logical_shifted_reg_cls where
  sf     : BitVec 1                 -- [31:31]
  opc    : BitVec 2                 -- [30:29]
  _fixed : BitVec 5 := 0b01010      -- [28:24]
  shift  : BitVec 2                 -- [23:22]
  N      : BitVec 1                 -- [21:21]
  Rm     : BitVec 5                 -- [20:16]
  imm6   : BitVec 6                 -- [15:10]
  Rn     : BitVec 5                 --   [9:5]
  Rd     : BitVec 5                 --   [4:0]
deriving DecidableEq, Repr

instance : ToString Logical_shifted_reg_cls where toString a := toString (repr a)

def Logical_shifted_reg_cls.toBitVec32 (x : Logical_shifted_reg_cls) : BitVec 32 :=
  x.sf ++ x.opc ++ x._fixed ++ x.shift ++ x.N ++ x.Rm ++ x.imm6 ++ x.Rn ++ x.Rd

inductive DataProcRegInst where
  | Add_sub_carry :
    Add_sub_carry_cls → DataProcRegInst
  | Conditional_select :
    Conditional_select_cls → DataProcRegInst
  | Logical_shifted_reg :
    Logical_shifted_reg_cls → DataProcRegInst
deriving DecidableEq, Repr

instance : ToString DataProcRegInst where toString a := toString (repr a)

end Decode
