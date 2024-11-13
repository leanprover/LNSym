/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Arm.Cfg.Cfg
import Specs.SHA512
import Tests.Debug
import Tests.SHA2.SHA512Program

section SHA512ProgramTest

open BitVec

-- We get an over-approximation of the GPR/SFP registers that may be modified in
-- a loop iteration.
/--
info: Except.ok #[RegType.GPR 0x01#5, RegType.GPR 0x02#5, RegType.GPR 0x03#5, RegType.GPR 0x04#5, RegType.SFP 0x00#5,
  RegType.SFP 0x01#5, RegType.SFP 0x02#5, RegType.SFP 0x03#5, RegType.SFP 0x04#5, RegType.SFP 0x05#5,
  RegType.SFP 0x06#5, RegType.SFP 0x07#5, RegType.SFP 0x10#5, RegType.SFP 0x11#5, RegType.SFP 0x12#5,
  RegType.SFP 0x13#5, RegType.SFP 0x14#5, RegType.SFP 0x15#5, RegType.SFP 0x16#5, RegType.SFP 0x17#5,
  RegType.SFP 0x18#5, RegType.SFP 0x19#5, RegType.SFP 0x1a#5, RegType.SFP 0x1b#5, RegType.SFP 0x1c#5,
  RegType.SFP 0x1d#5]
-/
#guard_msgs in
#eval (do let cfg ← Cfg.create' 0x126500#64 0x126c90#64 SHA512.program; pure cfg.maybe_modified_regs).mapError toString

/--
info: ok: #[(0,
   { guard := <BrOrg>0x0000000000126c90#64,
     target := <BrTgt>0x0000000000126500#64,
     next := <Seq>0x0000000000126c94#64 })]
-/
#guard_msgs in
#eval do let cfg ← Cfg.create SHA512.program; pure cfg.loops_info

-- Initial hash value, with the most-significant word first.
def SHA512_H0 : BitVec 512 :=
  SHA2.Hash.toBitVec SHA2.h0_512

-- The program expects the first K constant (i.e., 0x428a2f98d728ae22
-- as specified in the NIST standard
-- [https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf],
-- Section 4.2.3) to be stored at the smallest memory
-- address. Reversing this list and then flattening it yields a
-- bitvector where 0x428a2f98d728ae22 is the least-significant
-- word.
def SHA512_K : BitVec 5120 :=
  BitVec.flatten (List.reverse SHA2.k_512)

-- Address where the K constants are located.
def ktbl_address := 0x1b4300#64

-- init_x0
def ctx_address := 0#64

-- init_x1
def input_address := 1024#64

-- init_x2
def num_blocks := 1#64

def init_gpr : Store (BitVec 5) (BitVec 64) :=
  fun i =>
    match i with
      | 0 => ctx_address
      | 1 => input_address
      | 2 => num_blocks
      | _ => 0#64

def message_block : List (BitVec 64) :=
  [0x6162638000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000000#64,
   0x0000000000000018#64]

-- The program expects the last message word, i.e., 0x18#64 above, to
-- be stored at the largest address, so we reverse and then flatten
-- the `message_block`.
def asm_input : BitVec 1024 :=
  (BitVec.flatten (List.reverse message_block))

def init_sha512_test : ArmState :=
  let s := { gpr := init_gpr,
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc  := 0x1264c0#64,
             pstate := PState.zero,
             mem := (fun (_ : BitVec 64) => 0#8),
             program := SHA512.program,
             error := StateError.None }
  have h_input : 1024 = 1024 / 8 * 8 := by decide
  let s := write_mem_bytes (1024 / 8) input_address (BitVec.cast h_input asm_input) s
  have h_H0 : 512 = 512 / 8 * 8 := by decide
  let s := write_mem_bytes (512 / 8) ctx_address (BitVec.cast h_H0 SHA512_H0) s
  let s := write_mem_bytes (80 * 8) ktbl_address SHA512_K s
  s

-- Log the PCs of all the instructions that were simulated in
-- `Tests/SHA512_PC.log`.
-- #eval (log_run "Tests/SHA512_PC.log" pc_trace 503 init_sha512_test)

-- #eval r (.SFP 0) (run 5 init_sha512_test) =  SHA512_H0.extractLsb' 0 128
-- #eval r (.SFP 0) (run 5 init_sha512_test) =  (SHA2.h0_512.b ++ SHA2.h0_512.a)

def final_sha512_state : ArmState := run 503 init_sha512_test
def final_sha512_pc : BitVec 64 := read_pc final_sha512_state

-- read_mem_bytes below with (512/8) as the first arg. causes a
-- "maximum recursion depth has been reached" error, but that worked
-- in v4.3.0-rc1. However, things work as expected with 64 as the
-- first arg.
--
-- def final_sha512_hash : BitVec 512 := read_mem_bytes (512/8) ctx_address final_sha512_state
--
def final_sha512_hash : BitVec 512 := read_mem_bytes 64 ctx_address final_sha512_state

example : (final_sha512_hash = (r (.SFP 3) final_sha512_state) ++ (r (.SFP 2) final_sha512_state) ++
                               (r (.SFP 1) final_sha512_state) ++ (r (.SFP 0) final_sha512_state)):= by
  native_decide

-- Proof that we have reached the end of the program.
example : final_sha512_pc =
          -- Get the address (first element of the pair) from the
          -- max. element of sha512_program_map.
          SHA512.program.max!.1 := by
        native_decide

-- The final hash computed by the program is this bitvector below.
example : final_sha512_hash =
          0xa8018698f607e71485fd9f419b7061663ec081e2452ad3a1710d2fa39bbca33de8b1d23ccdc5e78e8ca5dd0a0a317e368b137f3cd4c324e4b5d80451e2f1d2a2#512 :=
        by native_decide

-- Specification Run:

-- We reverse the endianness of the message to make it suitable for
-- the specification function.
def spec_input_message : List (List (BitVec 64)) :=
  let block_revbytes :=
    List.map (fun elem => rev_elems 64 8 elem (by decide) (by decide)) message_block
  [block_revbytes]

-- The specification function computes the same hash value as our
-- program, after the endianness of the input is suitably changed.
example : SHA2.Hash.toBitVec (SHA2.sha512 (SHA2.message_schedule_mem 0 SHA2.j_512 []) spec_input_message) =
          0xa8018698f607e71485fd9f419b7061663ec081e2452ad3a1710d2fa39bbca33de8b1d23ccdc5e78e8ca5dd0a0a317e368b137f3cd4c324e4b5d80451e2f1d2a2#512
        := by native_decide

--------------------------------------------------

end SHA512ProgramTest
