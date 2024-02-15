/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.BitVec

------------------------------------------------------------------------------

section Decode

open Std.BitVec

-- Data Processing (Immediate) Instructions --

structure Add_sub_imm_cls where
  sf     : BitVec 1               -- [31:31]
  op     : BitVec 1               -- [30:30]
  S      : BitVec 1               -- [29:29]
  _fixed : BitVec 6 := 0b100010#6 -- [28:23]
  sh     : BitVec 1               -- [22:22]
  imm12  : BitVec 12              -- [21:10]
  Rn     : BitVec 5               --   [9:5]
  Rd     : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString Add_sub_imm_cls where toString a := toString (repr a)

def Add_sub_imm_cls.toBitVec32 (x : Add_sub_imm_cls) : BitVec 32 :=
  x.sf ++ x.op ++ x.S ++ x._fixed ++ x.sh ++ x.imm12 ++ x.Rn ++ x.Rd

structure Logical_imm_cls where
  sf     : BitVec 1                -- [31:31]
  opc    : BitVec 2                -- [30:29]
  _fixed : BitVec 6 := 0b100100#6  -- [28:23]
  N      : BitVec 1                -- [22:22]
  immr   : BitVec 6                -- [21:16]
  imms   : BitVec 6                -- [15:10]
  Rn     : BitVec 5                --  [9:5]
  Rd     : BitVec 5                --  [4:0]
deriving DecidableEq, Repr

instance : ToString Logical_imm_cls where toString a := toString (repr a)

def Logical_imm_cls.toBitVec32 (x : Logical_imm_cls) : BitVec 32 :=
  x.sf ++ x.opc ++ x._fixed ++ x.N ++ x.immr ++ x.imms ++ x.Rn ++ x.Rd

structure PC_rel_addressing_cls where
  op     : BitVec 1              -- [31:31]
  immlo  : BitVec 2              -- [30:29]
  _fixed : BitVec 5 := 0b10000#5 -- [28:24]
  immhi  : BitVec 19             -- [23:5]
  Rd     : BitVec 5              -- [4:0]
deriving DecidableEq, Repr

instance : ToString PC_rel_addressing_cls where toString a := toString (repr a)

structure Bitfield_cls where 
  sf     : BitVec 1                -- [31:31]
  opc    : BitVec 2                -- [30:29]
  _fixed : BitVec 6 := 0b100110#6  -- [28:23]
  N      : BitVec 1                -- [22:22]
  immr   : BitVec 6                -- [21:16]
  imms   : BitVec 6                -- [15:10]
  Rn     : BitVec 5                --  [9:5]
  Rd     : BitVec 5                --  [4:0]
deriving DecidableEq, Repr

instance : ToString Bitfield_cls where toString a := toString (repr a)

inductive DataProcImmInst where
  | Add_sub_imm :
    Add_sub_imm_cls → DataProcImmInst
  | Logical_imm :
    Logical_imm_cls → DataProcImmInst
  | PC_rel_addressing :
    PC_rel_addressing_cls → DataProcImmInst
  | Bitfield :
    Bitfield_cls → DataProcImmInst
deriving DecidableEq, Repr

instance : ToString DataProcImmInst where toString a := toString (repr a)

end Decode

-- inductive Operand where
--   | reg : GPRIndex → Operand
--   | imm : BitVec n → Operand
-- deriving Repr

-- structure DisassembledInst where
--   mnemonic : String
--   op1      : Option Operand := none
--   op2      : Option Operand := none
--   op3      : Option Operand := none
--   op4      : Option Operand := none
--   -- aliases  : Option Operand := none
-- deriving Repr

------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- @[reducible] def decode_data_proc_imm (i : BitVec 32) : ArmInst × Option DisassembledInst :=
--   match_bv i with
--   | [sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5] =>
--      let ai := ArmInst.DPI (DataProcImmInst.Add_sub_imm {sf, op, S, sh, imm12, Rn, Rd})
--      let (di : DisassembledInst) :=
--         match sf, op, S with
--         | 0#1, 0#1, 0#1 =>
--         { mnemonic := "ADD32",
--           op1 := Operand.reg ⟨Rd, GPR31.sp⟩,
--           op2 := Operand.reg ⟨Rn, GPR31.sp⟩,
--           op3 := Operand.imm imm12 }
--         | _, _, _ => {mnemonic := "NONE"}
--       ⟨ai, di⟩
--   | [sf:1, opc:2, 100100, N:1, immr:6, imms:6, Rn:5, Rd:5] =>
--     ⟨ArmInst.DPI (DataProcImmInst.Logical_imm {sf, opc, N, immr, imms, Rn, Rd}), none⟩
--   | _ => ⟨ArmInst.Unimplemented "Unimplemented", none⟩
