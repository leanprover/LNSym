/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Memory
import Arm.Decode.DPI
import Arm.Decode.DPR
import Arm.Decode.BR
import Arm.Decode.LDST
import Arm.Decode.DPSFP

------------------------------------------------------------------------------

section Decode

open BitVec

-- We do not tag any of the decode functions (e.g., decode_raw_inst or
-- its callees) with the `simp` attribute because we always expect
-- these functions to be called with a concrete instruction value. For
-- now, we can "execute" these definitions in proof using
-- "simp (config := { ground := true })".

-- Notation: We use CamelCase to define the top-level instruction
-- types, but their sub-categories' names (e.g.,
-- DataProcImmInst.Add_sub_imm) are longer and use underscores.

/-- A fully-decoded Arm instruction is represented by the ArmInst
structure. --/
inductive ArmInst where
  | DPI   : DataProcImmInst → ArmInst
  | BR    : BranchInst      → ArmInst
  | DPR   : DataProcRegInst → ArmInst
  | DPSFP : DataProcSFPInst → ArmInst
  | LDST  : LDSTInst        → ArmInst
deriving DecidableEq, Repr

instance : ToString ArmInst where toString a := toString (repr a)

def decode_data_proc_imm (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open DataProcImmInst in
  match_bv i with
  | [sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5] =>
     DPI (Add_sub_imm {sf, op, S, sh, imm12, Rn, Rd})
  | [sf:1, opc:2, 100100, N:1, immr:6, imms:6, Rn:5, Rd:5] =>
    DPI (Logical_imm {sf, opc, N, immr, imms, Rn, Rd})
  | [op:1, immlo:2, 10000, immhi:19, Rd:5] =>
    DPI (PC_rel_addressing {op, immlo, immhi, Rd})
  | [sf:1, opc:2, 100110, N:1, immr:6, imms:6, Rn:5, Rd:5] =>
    DPI (Bitfield {sf, opc, N, immr, imms, Rn, Rd})
  | _ => none

def decode_branch (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open BranchInst in
  match_bv i with
  | [sf:1, 011010, op:1, imm19:19, Rt:5] =>
    BR (Compare_branch {sf, op, imm19, Rt})
  | [op:1, 00101, imm26:26] =>
    BR (Uncond_branch_imm {op, imm26})
  | [1101011, opc:4, op2:5, op3:6, Rn:5, op4:5] =>
    BR (Uncond_branch_reg {opc, op2, op3, Rn, op4})
  | [01010100, imm19:19, o0:1, cond:4] =>
    BR (Cond_branch_imm {imm19, o0, cond})
  | _ => none

def decode_data_proc_reg (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open DataProcRegInst in
  match_bv i with
  | [sf:1, op:1, S:1, 11010000, Rm:5, 000000, Rn:5, Rd:5] =>
    DPR (Add_sub_carry {sf, op, S, Rm, Rn, Rd})
  | [sf:1, op:1, S:1, 01011, shift:2, 0, Rm:5, imm6:6 , Rn:5, Rd:5] =>
    DPR (Add_sub_shifted_reg {sf, op, S, shift, Rm, imm6, Rn, Rd})
  | [sf:1, op:1, S:1, 11010100, Rm:5, cond:4, op2:2, Rn:5, Rd:5] =>
    DPR (Conditional_select {sf, op, S, Rm, cond, op2, Rn, Rd})
  | [sf:1, 1, S:1, 11010110, opcode2:5, opcode:6, Rn:5, Rd:5] =>
    DPR (Data_processing_one_source {sf, S, opcode2, opcode, Rn, Rd})
  | [sf:1, 0, S:1, 11010110, Rm:5, opcode:6, Rn:5, Rd:5] =>
    DPR (Data_processing_two_source {sf, S, Rm, opcode, Rn, Rd})
  | [sf:1, opc:2, 01010, shift:2, N:1, Rm:5, imm6:6, Rn:5, Rd:5] =>
    DPR (Logical_shifted_reg {sf, opc, shift, N, Rm, imm6, Rn, Rd})
  | _ => none

def decode_data_proc_sfp (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open DataProcSFPInst in
  match_bv i with
  | [01001110, size:2, 10100, opcode:5, 10, Rn:5, Rd:5] =>
    DPSFP (Crypto_aes {size, opcode, Rn, Rd})
  | [11001110011, Rm:5, 1, O:1, 00, opcode:2, Rn:5, Rd:5] =>
    DPSFP (Crypto_three_reg_sha512 {Rm, O, opcode, Rn, Rd})
  | [11001110110000001000, opcode:2, Rn:5, Rd:5] =>
    DPSFP (Crypto_two_reg_sha512 {opcode, Rn, Rd})
  | [110011100, Op0:2, Rm:5, 0, Ra:5, Rn:5, Rd:5] =>
    DPSFP (Crypto_four_reg {Op0, Rm, Ra, Rn, Rd})
  | [0, Q:1, U:1, 01110, size:2, 10000, opcode:5, 10, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_two_reg_misc {Q, U, size, opcode, Rn, Rd})
  | [0, Q:1, op:1, 01110000, imm5:5, 0, imm4:4, 1, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_copy {Q, op, imm5, imm4, Rn, Rd})
  | [0, Q:1, 101110, op2:2, 0, Rm:5, 0, imm4:4, 0, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_extract {Q, op2, Rm, imm4, Rn, Rd})
  | [0, Q:1, 001110, size:2, 0, Rm:5, 0, opcode:3, 10, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_permute {Q, size, Rm, opcode, Rn, Rd})
  | [0, Q:1, op:1, 0111100000, a:1, b:1, c:1, cmode:4, o2:1, 1, d:1, e:1, f:1, g:1, h:1, Rd:5] =>
    DPSFP (Advanced_simd_modified_immediate {Q, op, a, b, c, cmode, o2, d, e, f, g, h, Rd})
  -- Note: Advanced SIMD shift by immediate constraint immh != 0000
  -- An instruction will be matched against `Advanced_simd_modified_immediate` first,
  -- if it doesn't match, then we know immh can't be 0b0000#4
  | [0, Q:1, U:1, 011110, immh:4, immb:3, opcode:5, 1, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_shift_by_immediate {Q, U, immh, immb, opcode, Rn, Rd})
  | [01, U:1, 111110, immh:4, immb:3, opcode:5, 1, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_scalar_shift_by_immediate {U, immh, immb, opcode, Rn, Rd})
  | [01, op:1, 11110000, imm5:5, 0, imm4:4, 1, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_scalar_copy {op, imm5, imm4, Rn, Rd})
  | [0, Q:1, 001110, op2:2, 0, Rm:5, 0, len:2, op:1, 00, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_table_lookup {Q, op2, Rm, len, op, Rn, Rd})
  | [0, Q:1, U:1, 01110, size:2, 1, Rm:5, opcode:5, 1, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_three_same {Q, U, size, Rm, opcode, Rn, Rd})
  | [0, Q:1, U:1, 01110, size:2, 1, Rm:5, opcode:4, 00, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_three_different {Q, U, size, Rm, opcode, Rn, Rd})
  | [sf:1, 0, S:1, 11110, ftype:2, 1, rmode:2, opcode:3, 000000, Rn:5, Rd:5] =>
    DPSFP (Conversion_between_FP_and_Int {sf, S, ftype, rmode, opcode, Rn, Rd})
  | _ => none

def decode_ldst_inst (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open LDSTInst in
  match_bv i with
  | [size:2, 111, V:1, 00, opc:2, 0, imm9:9, 01, Rn:5, Rt:5] =>
    LDST (Reg_imm_post_indexed {size, V, opc, imm9, Rn, Rt})
  | [size:2, 111, V:1, 01, opc:2, imm12:12, Rn:5, Rt:5] =>
    LDST (Reg_unsigned_imm {size, V, opc, imm12, Rn, Rt})
  | [opc:2, 101, V:1, 011, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_pre_indexed {opc, V, L, imm7, Rt2, Rn, Rt})
  | [opc:2, 101, V:1, 001, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_post_indexed {opc, V, L, imm7, Rt2, Rn, Rt})
  | [opc:2, 101, V:1, 010, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_signed_offset {opc, V, L, imm7, Rt2, Rn, Rt})
  | [0, Q:1, 0011000, L:1, 000000, opcode:4, size:2, Rn:5, Rt:5] =>
    LDST (Advanced_simd_multiple_struct {Q, L, opcode, size, Rn, Rt})
  | [0, Q:1, 0011001, L:1, 0, Rm:5, opcode:4, size:2, Rn:5, Rt:5] =>
    LDST (Advanced_simd_multiple_struct_post_indexed {Q, L, Rm, opcode, size, Rn, Rt})
  | _ => none

-- Decode a 32-bit instruction `i`.
def decode_raw_inst (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  match_bv i with
  | [op0:1, _x:2, op1:4, _y:25] =>
    match op0, op1 with
    | _, 0b1000#4 | _, 0b1001#4 => decode_data_proc_imm i
    | _, 0b1010#4 | _, 0b1011#4 => decode_branch i
    | _, 0b1101#4 | _, 0b0101#4 => decode_data_proc_reg i
    | _, 0b0111#4 | _, 0b1111#4 => decode_data_proc_sfp i
    | _, 0b0100#4 | _, 0b1100#4 | _, 0b0110#4 | _, 0b1110#4 => decode_ldst_inst i
    | _, _ => none
  | _ => none

------------------------------------------------------------------------

-- add x1, x1, 1
example : decode_raw_inst 0x91000421#32 =
          (ArmInst.DPI (DataProcImmInst.Add_sub_imm
          {sf := 1#1, op := 0#1, S := 0#1, sh := 0#1,
            imm12 := 1#12, Rn := 1#5, Rd := 1#5})) := by
        rfl

-- adc x1, x1, x0
example : decode_raw_inst 0b00011010000000000000000000100001#32 =
          (ArmInst.DPR (DataProcRegInst.Add_sub_carry
               { sf := 0#1, op := 0#1, S := 0#1, Rm := 0#5,
                 Rn := 1#5, Rd := 1#5 })) := by
        rfl

-- sha512h q3, q5, v6.2d
example : decode_raw_inst 0xce6680a3#32 =
          (ArmInst.DPSFP (DataProcSFPInst.Crypto_three_reg_sha512
               { Rm := 6#5, O := 0#1, opcode := 0#2,
                 Rn := 5#5, Rd := 3#5 })) := by
        rfl

-- sha512h2 q3, q1, v0.2d
example : decode_raw_inst 0xce608423#32 =
          (ArmInst.DPSFP (DataProcSFPInst.Crypto_three_reg_sha512
               { Rm := 0#5, O := 0#1, opcode := 1#2,
                 Rn := 1#5, Rd := 3#5 })) := by
        rfl

-- sha512su1 v16.2d, v23.2d, v7.2d
example : decode_raw_inst 0xce678af0#32 =
          (ArmInst.DPSFP (DataProcSFPInst.Crypto_three_reg_sha512
          { Rm := 7#5, O := 0#1, opcode := 2#2,
            Rn := 23#5, Rd := 16#5 })) := by
        rfl

-- sha512su0 v16.2d, v17.2d
example : decode_raw_inst 0xcec08230#32 =
          (ArmInst.DPSFP (DataProcSFPInst.Crypto_two_reg_sha512
               { opcode := 0#2, Rn := 17#5, Rd := 16#5 })) := by
        rfl

-- ldr	q16, [x0], #16
example : decode_raw_inst 0x3cc10410#32 =
          (ArmInst.LDST (LDSTInst.Reg_imm_post_indexed
               { size := 0x0#2, V := 0x1#1, opc := 0x3#2, imm9 := 0x010#9,
                 Rn := 0x00#5, Rt := 0x10#5 })) := by
        rfl

-- stp	x29, x30, [sp, #-16]!
example : decode_raw_inst 0xa9bf7bfd#32 =
          (ArmInst.LDST (LDSTInst.Reg_pair_pre_indexed
               { opc := 0x2#2, V := 0x0#1, L := 0x0#1, imm7 := 0x7e#7,
                 Rt2 := 0x1e#5, Rn := 0x1f#5, Rt := 0x1d#5 })) := by
        rfl

-- ld1	{v16.16b-v19.16b}, [x1], #64
example : decode_raw_inst 0x4cdf2030#32 =
          (ArmInst.LDST
               (LDSTInst.Advanced_simd_multiple_struct_post_indexed
                 { Q := 0x1#1, L := 0x1#1, Rm := 0x1f#5, opcode := 0x2#4,
                   size := 0x0#2, Rn := 0x01#5, Rt := 0x10#5 })) := by
        rfl

-- ld1	{v24.2d}, [x3], #16
example : decode_raw_inst 0x4cdf7c78#32 =
          (ArmInst.LDST
               (LDSTInst.Advanced_simd_multiple_struct_post_indexed
                 { Q := 0x1#1, L := 0x1#1, Rm := 0x1f#5, opcode := 0x7#4,
                   size := 0x3#2, Rn := 0x03#5, Rt := 0x18#5 })) := by
        rfl

-- ld1	{v0.2d-v3.2d}, [x0]
example : decode_raw_inst 0x4c402c00#32 =
          (ArmInst.LDST
          (LDSTInst.Advanced_simd_multiple_struct
            { Q := 0x1#1, L := 0x1#1, opcode := 0x2#4,
              size := 0x3#2, Rn := 0x00#5, Rt := 0x00#5 })) := by
        rfl

-- st1	{v0.2d-v3.2d}, [x0]
example :  decode_raw_inst 0x4c002c00#32 =
           (ArmInst.LDST
                (LDSTInst.Advanced_simd_multiple_struct
                  { Q := 0x1#1, L := 0x0#1, opcode := 0x2#4, size := 0x3#2,
                    Rn := 0x00#5, Rt := 0x00#5 })) := by rfl

-- add	v24.2d, v24.2d, v16.2d
example : decode_raw_inst 0x4ef08718#32 =
  (ArmInst.DPSFP (DataProcSFPInst.Advanced_simd_three_same
       { Q := 0x1#1, U := 0x0#1, size := 0x3#2, Rm := 0x10#5,
         opcode := 0x10#5, Rn := 0x18#5, Rd := 0x18#5 })) := by
  rfl

-- adrp x3, ...
example : decode_raw_inst 0xd0000463#32 =
          (ArmInst.DPI (DataProcImmInst.PC_rel_addressing
               { op := 0x1#1, immlo := 0x2#2, immhi := 0x00023#19,
                 Rd := 0x03#5 })) := by
        rfl

-- csel	x1, x1, x4, ne
example : decode_raw_inst 0x9a841021#32 =
          (ArmInst.DPR (DataProcRegInst.Conditional_select
               { sf := 0x1#1, op := 0x0#1, S := 0x0#1, Rm := 0x04#5,
                 cond := 0x1#4, op2 := 0x0#2, Rn := 0x01#5,
                 Rd := 0x01#5 })) := by
        rfl

-- b ...
example : decode_raw_inst 0x14000001#32 =
          (ArmInst.BR (BranchInst.Uncond_branch_imm
               { op := 0x0#1, imm26 := 0x0000001#26 })) := by
        rfl

-- b.le ...
example : decode_raw_inst 0x5400000d#32 =
          (ArmInst.BR (BranchInst.Cond_branch_imm
               { imm19 := 0x00000#19, o0 := 0, cond := 0xd#4})) := by
        rfl

-- ret
example : decode_raw_inst 0xd65f03c0#32 =
          (ArmInst.BR (BranchInst.Uncond_branch_reg
               { opc := 0x2#4, op2 := 0x1f#5, op3 := 0x00#6,
                 Rn := 0x1e#5, op4 := 0x00#5 })) := by
        rfl

-- cbnz	x2, ...
example : decode_raw_inst 0xb5ffc382#32 =
          (ArmInst.BR (BranchInst.Compare_branch
               { sf := 0x1#1, op := 0x1#1, imm19 := 0x7fe1c#19,
                 Rt := 0x02#5 })) := by
        rfl

-- ext	v24.16b, v24.16b, v24.16b, #8
example : decode_raw_inst 0x6e184318#32 =
          (ArmInst.DPSFP (DataProcSFPInst.Advanced_simd_extract
               { Q := 0x1#1, op2 := 0x0#2, Rm := 0x18#5, imm4 := 0x8#4,
                 Rn := 0x18#5, Rd := 0x18#5 })) := by
        rfl

-- mov	x29, sp
example : decode_raw_inst 0x910003fd#32 =
          (ArmInst.DPI (DataProcImmInst.Add_sub_imm
               { sf := 0x1#1, op := 0x0#1, S := 0x0#1, sh := 0x0#1,
                 imm12 := 0x000#12, Rn := 0x1f#5, Rd := 0x1d#5 })) := by
        rfl

-- ldr	q0, [x4]
example : decode_raw_inst 0x3dc00080#32 =
          (ArmInst.LDST (LDSTInst.Reg_unsigned_imm
               { size := 0x0#2, V := 0x1#1, opc := 0x3#2,
                 imm12 := 0x000#12, Rn := 0x04#5, Rt := 0x00#5 })) := by
        rfl

-- str	q4, [x2], #16
example : decode_raw_inst 0x3c810444#32 =
          (ArmInst.LDST (LDSTInst.Reg_imm_post_indexed
               { size := 0x0#2, V := 0x1#1, opc := 0x2#2, imm9 := 0x010#9,
                 Rn := 0x02#5, Rt := 0x04#5 })) := by
        rfl

-- rev64 v0.16b, v0.16b
example : decode_raw_inst 0x4e200800#32 =
          (ArmInst.DPSFP
               (DataProcSFPInst.Advanced_simd_two_reg_misc
                 { Q := 0x1#1, U := 0x0#1, size := 0x0#2, opcode := 0x00#5,
                   Rn := 0x00#5, Rd := 0x00#5 })) := by
        rfl

-- aese	v0.16b, v16.16b
example : decode_raw_inst 0x4e284a00#32 =
          (ArmInst.DPSFP (DataProcSFPInst.Crypto_aes
               { size := 0x0#2, opcode := 0x04#5,
                 Rn := 0x10#5, Rd := 0x00#5 })) := by
        rfl

-- aesmc v0.16b, v0.16b
example : decode_raw_inst 0x4e286800#32 =
          (ArmInst.DPSFP (DataProcSFPInst.Crypto_aes
               { size := 0x0#2, opcode := 0x06#5,
                 Rn := 0x00#5, Rd := 0x00#5 })) := by
        rfl

-- mov	x28, v0.d[0]
example : decode_raw_inst 0x4e083c1c#32 =
          ArmInst.DPSFP (DataProcSFPInst.Advanced_simd_copy
              { Q := 0x1#1, op := 0x0#1, imm5 := 0x08#5,
                imm4 := 0x7#4, Rn := 0x00#5, Rd := 0x1c#5 }) := by
        rfl

-- ext v16.8B, v10.8B, v24.8B, #2
example : decode_raw_inst 0x2e181150#32 =
          (ArmInst.DPSFP
            (DataProcSFPInst.Advanced_simd_extract
            { Q := 0x0#1,
              op2 := 0x0#2,
              Rm := 0x18#5,
              imm4 := 0x2#4,
              Rn := 0x0a#5,
              Rd := 0x10#5 })) := by
        rfl

-- lsr w0, w0, #1
example : decode_raw_inst 0x53017c00#32 =
          (ArmInst.DPI
            (DataProcImmInst.Bitfield
              { sf := 0x0#1,
                opc := 0x2#2,
                _fixed := 0x26#6,
                N := 0x0#1,
                immr := 0x01#6,
                imms := 0x1f#6,
                Rn := 0x00#5,
                Rd := 0x00#5 })) := by
        rfl

-- ands x30, x3, x17, asr #35
example : decode_raw_inst 0xea918c7e#32 =
          (ArmInst.DPR (DataProcRegInst.Logical_shifted_reg
          { sf := 0x1#1,
            opc := 0x3#2,
            _fixed := 0x0a#5,
            shift := 0x2#2,
            N := 0x0#1,
            Rm := 0x11#5,
            imm6 := 0x23#6,
            Rn := 0x03#5,
            Rd := 0x1e#5})) := by
        rfl

-- eor x15, x28, #0xffffc00000000001
example : decode_raw_inst 0xd2524b8f#32 =
          (ArmInst.DPI (DataProcImmInst.Logical_imm
          { sf := 0x1#1,
            opc := 0x2#2,
            _fixed := 0x24#6,
            N := 0x1#1,
            immr := 0x12#6,
            imms := 0x12#6,
            Rn := 0x1c#5,
            Rd := 0x0f#5 })) := by
        rfl

-- sub x9, x27, x15, lsl #55
example : decode_raw_inst 0xcb0fdf69 =
          (ArmInst.DPR (DataProcRegInst.Add_sub_shifted_reg
          { sf := 0x1#1,
            op := 0x1#1,
            S := 0x0#1,
            _fixed1 := 0x0b#5,
            shift := 0x0#2,
            _fixed2 := 0x0#1,
            Rm := 0x0f#5,
            imm6 := 0x37#6,
            Rn := 0x1b#5,
            Rd := 0x09#5 })) := by
        rfl

-- orr v5.8h, #0x77, lsl #8
example : decode_raw_inst 0x4f03b6e5 =
          (ArmInst.DPSFP
            (DataProcSFPInst.Advanced_simd_modified_immediate
          { _fixed1 := 0x0#1,
            Q := 0x1#1,
            op := 0x0#1,
            _fixed2 := 0x1e0#10,
            a := 0x0#1,
            b := 0x1#1,
            c := 0x1#1,
            cmode := 0xb#4,
            o2 := 0x0#1,
            _fixed3 := 0x1#1,
            d := 0x1#1,
            e := 0x0#1,
            f := 0x1#1,
            g := 0x1#1,
            h := 0x1#1,
            Rd := 0x05#5 })) := by
        rfl

-- mov v10.h[0] v17.h[6]
example : decode_raw_inst 0x6e026e2a =
          (ArmInst.DPSFP
            (DataProcSFPInst.Advanced_simd_copy
          { _fixed1 := 0x0#1,
            Q := 0x1#1,
            op := 0x1#1,
            _fixed2 := 0x70#8,
            imm5 := 0x02#5,
            _fixed3 := 0x0#1,
            imm4 := 0xd#4,
            _fixed4 := 0x1#1,
            Rn := 0x11#5,
            Rd := 0x0a#5 })) := by
          rfl

-- fmov v25.d[1], x5
example : decode_raw_inst 0x9eaf00b9 =
          (ArmInst.DPSFP
            (DataProcSFPInst.Conversion_between_FP_and_Int
            { sf := 0x1#1,
              _fixed1 := 0x0#1,
              S := 0x0#1,
              _fixed2 := 0x1e#5,
              ftype := 0x2#2,
              _fixed3 := 0x1#1,
              rmode := 0x1#2,
              opcode := 0x7#3,
              _fixed4 := 0x00#6,
              Rn := 0x05#5,
              Rd := 0x19#5 })) := by
            rfl

-- rev x0, x25
example : decode_raw_inst 0xdac00f20 =
          (ArmInst.DPR
            (DataProcRegInst.Data_processing_one_source
            { sf := 0x1#1,
              _fixed1 := 0x1#1,
              S := 0x0#1,
              _fixed2 := 0xd6#8,
              opcode2 := 0x00#5,
              opcode := 0x03#6,
              Rn := 0x19#5,
              Rd := 0x00#5 })) := by
          rfl

-- Unimplemented
example : decode_raw_inst 0x00000000#32 = none := by rfl

end Decode
