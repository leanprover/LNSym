/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel, Yan Peng
-/
import Arm.BitVec

------------------------------------------------------------------------------

section Decode

open Std.BitVec

-- Load and Store Instructions

structure Reg_imm_post_indexed_cls where
  size    : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b111#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 2 := 0b00#2  -- [25:24]
  opc     : BitVec 2            -- [23:22]
  _fixed3 : BitVec 1 := 0b0#1   -- [21:21]
  imm9    : BitVec 9            -- [20:12]
  _fixed4 : BitVec 2 := 0b01#2  -- [11:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_imm_post_indexed_cls where toString a := toString (repr a)

structure Reg_unsigned_imm_cls where
  size    : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b111#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 2 := 0b01#2  -- [25:24]
  opc     : BitVec 2            -- [23:22]
  imm12   : BitVec 12           -- [21:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_unsigned_imm_cls where toString a := toString (repr a)

structure Reg_pair_pre_indexed_cls where
  opc     : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b101#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 3 := 0b011#3 -- [25:23]
  L       : BitVec 1            -- [22:22]
  imm7    : BitVec 7            -- [21:15]
  Rt2     : BitVec 5            -- [14:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_pair_pre_indexed_cls where toString a := toString (repr a)

structure Reg_pair_post_indexed_cls where
  opc     : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b101#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 3 := 0b001#3 -- [25:23]
  L       : BitVec 1            -- [22:22]
  imm7    : BitVec 7            -- [21:15]
  Rt2     : BitVec 5            -- [14:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_pair_post_indexed_cls where toString a := toString (repr a)

structure Reg_pair_signed_offset_cls where
  opc     : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b101#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 3 := 0b010#3 -- [25:23]
  L       : BitVec 1            -- [22:22]
  imm7    : BitVec 7            -- [21:15]
  Rt2     : BitVec 5            -- [14:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_pair_signed_offset_cls where toString a := toString (repr a)

structure Advanced_simd_multiple_struct_cls where
  _fixed1 : BitVec 1 := 0b0#1       -- [31:31]
  Q       : BitVec 1                -- [30:30]
  _fixed2 : BitVec 7 := 0b0011000#7 -- [29:23]
  L       : BitVec 1                -- [22:22]
  _fixed3 : BitVec 6 := 0b000000#6  -- [21:16]
  opcode  : BitVec 4                -- [15:12]
  size    : BitVec 2                -- [11:10]
  Rn      : BitVec 5                --   [9:5]
  Rt      : BitVec 5                --   [4:0]
deriving DecidableEq, Repr

instance : ToString Advanced_simd_multiple_struct_cls where toString a := toString (repr a)

structure Advanced_simd_multiple_struct_post_indexed_cls where
  _fixed1 : BitVec 1 := 0b0#1       -- [31:31]
  Q       : BitVec 1                -- [30:30]
  _fixed2 : BitVec 7 := 0b0011001#7 -- [29:23]
  L       : BitVec 1                -- [22:22]
  _fixed3 : BitVec 1 := 0b0#1       -- [21:21]
  Rm      : BitVec 5                -- [20:16]
  opcode  : BitVec 4                -- [15:12]
  size    : BitVec 2                -- [11:10]
  Rn      : BitVec 5                --   [9:5]
  Rt      : BitVec 5                --   [4:0]
deriving DecidableEq, Repr

instance : ToString Advanced_simd_multiple_struct_post_indexed_cls where toString a := toString (repr a)

inductive LDSTInst where
  | Reg_imm_post_indexed :
    Reg_imm_post_indexed_cls → LDSTInst
  | Reg_unsigned_imm :
    Reg_unsigned_imm_cls → LDSTInst
  | Reg_pair_pre_indexed :
    Reg_pair_pre_indexed_cls → LDSTInst
  | Reg_pair_post_indexed :
    Reg_pair_post_indexed_cls → LDSTInst
  | Reg_pair_signed_offset :
    Reg_pair_signed_offset_cls → LDSTInst
  | Advanced_simd_multiple_struct :
    Advanced_simd_multiple_struct_cls → LDSTInst
  | Advanced_simd_multiple_struct_post_indexed :
    Advanced_simd_multiple_struct_post_indexed_cls → LDSTInst
deriving DecidableEq, Repr

instance : ToString LDSTInst where toString a := toString (repr a)

end Decode
