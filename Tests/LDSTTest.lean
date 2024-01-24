/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Yan Peng
-/

import Arm.Exec

section LDSTTest

open Std.BitVec

-- This file contains unit tests for LDST instructions
-- The cosimulation tests do not cover instructions related to memory access
-- TODO: use macros to simplify the tests

def set_init_state (find? : Store (BitVec 64) (Option (BitVec 32))) : ArmState :=
  let s := { gpr := (fun (_ : BitVec 5) => 0#64),
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0#64,
             pstate := (fun (_ : PFlag) => 0#1),
             mem := (fun (_ : BitVec 64) => 0#8),
             program := find?,
             error := StateError.None}
  s

----------------------------------------------------------------------
-- test ldr, 32-bit gpr, unsigned offset
def ldr_gpr_unsigned_offset : program :=
  def_program
    #[ (0x0#64, 0xb9400fe0#32) ]  -- ldr w0, [sp, #12]

def ldr_gpr_unsigned_offset_state : ArmState :=
  let s := set_init_state ldr_gpr_unsigned_offset.find?
  -- write 20 in 4 bytes to address 12
  let s := write_mem_bytes 4 12#64 20#32 s
  s

def ldr_gpr_unsigned_offset_final_state : ArmState := run 1 ldr_gpr_unsigned_offset_state

example : (read_store 0#5 ldr_gpr_unsigned_offset_final_state.gpr) = 20#64 := by native_decide
example : ldr_gpr_unsigned_offset_final_state.pc = 4#64 := by native_decide

----------------------------------------------------------------------
-- test str, 64-bit gpr, post-index
def str_gpr_post_index : program :=
  def_program
    #[ (0x0#64, 0xf8003420#32) ] -- str x0, [x1], #3

def str_gpr_post_index_state : ArmState :=
  let s := set_init_state str_gpr_post_index.find?
  -- write 20 in gpr x0
  let s := write_gpr 64 0#5 20#64 s
  -- write 0 in gpr x1
  write_gpr 64 1#5 0#64 s

def str_gpr_post_index_final_state : ArmState := run 1 str_gpr_post_index_state

example : (read_store 1#5 str_gpr_post_index_final_state.gpr) = 3#64 := by native_decide
example : (read_mem_bytes 8 0#64 str_gpr_post_index_final_state) = 20#64 := by native_decide
example : str_gpr_post_index_final_state.pc = 4#64 := by native_decide

----------------------------------------------------------------------
-- test ldr, 64-bit sfp, post-index
def ldr_sfp_post_index : program :=
  def_program
    #[ (0x0#64, 0xfc408420#32) ] -- ldr d0, [x1], #8

def ldr_sfp_post_index_state : ArmState :=
  let s := set_init_state ldr_sfp_post_index.find?
  let s := write_mem_bytes 8 0#64 20#64 s
  s

def ldr_sfp_post_index_final_state : ArmState := run 1 ldr_sfp_post_index_state

example : (read_store 0#5 ldr_sfp_post_index_final_state.sfp) = 20#128 := by native_decide
example : (read_store 1#5 ldr_sfp_post_index_final_state.gpr) = 8#64 := by native_decide

----------------------------------------------------------------------
-- test str, 128-bit sfp, unsigned offset
def str_stp_unsigned_offset : program :=
  def_program
    #[ (0x0#64, 0x3d800420#32) ] -- str q0, [x1, #1]

def str_sfp_unsigned_offset_state : ArmState :=
  let s := set_init_state str_stp_unsigned_offset.find?
  write_sfp 128 0#5 123#128 s

def str_sfp_unsigned_offset_final_state : ArmState := run 1 str_sfp_unsigned_offset_state

example : (read_mem_bytes 16 16#64 str_sfp_unsigned_offset_final_state) = 123#128 := by native_decide

----------------------------------------------------------------------
-- test ldrb, unsigned offset
def ldrb_unsigned_offset : program :=
  def_program
    #[ (0x0#64, 0x39401020#32) ] -- ldrb x0, [x1, #4]

def ldrb_unsigned_offset_state: ArmState :=
  let s := set_init_state ldrb_unsigned_offset.find?
  write_mem_bytes 1 4#64 20#8 s
  
def ldrb_unsigned_offset_final_state : ArmState := run 1 ldrb_unsigned_offset_state

example : (read_store 0#5 ldrb_unsigned_offset_final_state.gpr) = 20#64 := by native_decide

----------------------------------------------------------------------
-- test strb, post-index
def strb_post_index : program :=
  def_program
    #[ (0x0#64, 0x381fc420#32) ] -- strb x0, [x1], #-4

def strb_post_index_state : ArmState :=
  let s := set_init_state strb_post_index.find?
  let s := write_gpr 64 1#5 5#64 s
  write_gpr 64 0#5 20#64 s

def strb_post_index_final_state : ArmState := run 1 strb_post_index_state

example : (read_store 0#5 strb_post_index_final_state.gpr) = 20#64 := by native_decide
example : (read_store 1#5 strb_post_index_final_state.gpr) = 1#64 := by native_decide

----------------------------------------------------------------------
-- test ldp
def ldp_gpr_pre_index : program :=
  def_program
    #[ (0x0#64, 0xa9c00820#32) ] -- ldp x0, x2, [x1]!

def ldp_gpr_pre_index_state : ArmState :=
  let s := set_init_state ldp_gpr_pre_index.find?
  write_mem_bytes 16 0#64 0x1234000000000000ABCD#128 s

def ldp_gpr_pre_index_final_state : ArmState := run 1 ldp_gpr_pre_index_state

example : (read_store 0#5 ldp_gpr_pre_index_final_state.gpr) = 0xABCD#64 := by native_decide
example : (read_store 2#5 ldp_gpr_pre_index_final_state.gpr) = 0x1234#64 := by native_decide

----------------------------------------------------------------------
-- test stp
def stp_sfp_signed_offset : program :=
  def_program
    #[ (0x0#64, 0xad008820#32) ] -- stp q0, q2, [q1,#1]

def stp_sfp_signed_offset_state : ArmState :=
  let s := set_init_state stp_sfp_signed_offset.find?
  let s := write_sfp 128 0#5 0x1234#128 s
  write_sfp 128 2#5 0xabcd#128 s

#eval stp_sfp_signed_offset_state

def stp_sfp_signed_offset_final_state : ArmState := run 1 stp_sfp_signed_offset_state

#eval stp_sfp_signed_offset_final_state
#eval (read_mem_bytes 32 16#64 stp_sfp_signed_offset_final_state)

example : (read_mem_bytes 32 16#64 stp_sfp_signed_offset_final_state) =
  0xabcd00000000000000000000000000001234#256 := by native_decide

end LDSTTest
