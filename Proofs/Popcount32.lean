/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Nathan Wetzler
-/
import Arm.Exec
import Arm.Util
import Tactics.Sym
import Tactics.StepThms

section popcount32

open BitVec

/-!
Source: https://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel

int popcount_32 (unsigned int v) {
  v = v - ((v >> 1) & 0x55555555);
  v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
  v = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
  return(v);
}

-/

def popcount32_spec_rec (i : Nat) (x : BitVec 32) : (BitVec 32) :=
  match i with
  | 0 => BitVec.zero 32
  | i' + 1 =>
    let bit_idx := BitVec.getLsb x i'
    ((BitVec.zeroExtend 32 (BitVec.ofBool bit_idx)) + (popcount32_spec_rec i' x))

def popcount32_spec (x : BitVec 32) : BitVec 32 :=
  popcount32_spec_rec 32 x


def popcount32_program : Program :=
  def_program
  [(0x4005b4#64 , 0xd10043ff#32), -- sub sp, sp, #0x10
   (0x4005b8#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x4005bc#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005c0#64 , 0x53017c00#32), -- lsr w0, w0, #1
   (0x4005c4#64 , 0x1200f000#32), -- and w0, w0, #0x55555555
   (0x4005c8#64 , 0xb9400fe1#32), -- ldr w1, [sp, #12]
   (0x4005cc#64 , 0x4b000020#32), -- sub w0, w1, w0
   (0x4005d0#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x4005d4#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005d8#64 , 0x1200e401#32), -- and w1, w0, #0x33333333
   (0x4005dc#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005e0#64 , 0x53027c00#32), -- lsr w0, w0, #2
   (0x4005e4#64 , 0x1200e400#32), -- and w0, w0, #0x33333333
   (0x4005e8#64 , 0x0b000020#32), -- add w0, w1, w0
   (0x4005ec#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x4005f0#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005f4#64 , 0x53047c01#32), -- lsr w1, w0, #4
   (0x4005f8#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x4005fc#64 , 0x0b000020#32), -- add w0, w1, w0
   (0x400600#64 , 0x1200cc01#32), -- and w1, w0, #0xf0f0f0f
   (0x400604#64 , 0x3200c3e0#32), -- mov w0, #0x1010101
   (0x400608#64 , 0x1b007c20#32), -- mul w0, w1, w0
   (0x40060c#64 , 0x53187c00#32), -- lsr w0, w0, #24
   (0x400610#64 , 0xb9000fe0#32), -- str w0, [sp, #12]
   (0x400614#64 , 0xb9400fe0#32), -- ldr w0, [sp, #12]
   (0x400618#64 , 0x910043ff#32), -- add sp, sp, #0x10
   (0x40061c#64 , 0xd65f03c0#32)] -- ret


#genStepEqTheorems popcount32_program

theorem popcount32_sym_no_error (s0 s_final : ArmState)
    (h_s0_pc : read_pc s0 = 0x4005b4#64)
    (h_s0_program : s0.program = popcount32_program)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_s0_err : read_err s0 = StateError.None)
    (h_run : s_final = run 27 s0) :
    read_err s_final = StateError.None := by
  -- Symbolic Simulation
  sym_n 27
  done

theorem popcount32_sym_meets_spec (s0 s_final : ArmState)
    (h_s0_pc : read_pc s0 = 0x4005b4#64)
    (h_s0_program : s0.program = popcount32_program)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_s0_err : read_err s0 = StateError.None)
    (h_run : s_final = run 27 s0) :
    read_gpr 32 0#5 s_final = popcount32_spec (read_gpr 32 0#5 s0) ∧
    read_err s_final = StateError.None := by
  -- Symbolic Simulation
  sym_n 27

  simp (config := {ground := true}) only [popcount32_spec, popcount32_spec_rec,
    AddWithCarry, bitvec_rules, minimal_theory]
  -- TODO: remove once bv_decide understands extractLsb'
  simp [BitVec.extractLsb'_eq_extractLsb _ _ _ (by omega : 1 > 0)]
  -- bv_decide
  sorry

-- (true, 0x00000007#32, false)
#eval
(let x0 := 0xffffffffffffffff#64
 let sp := 0x00000000000000A0#64
 let s0 :=  { gpr := (fun (i : BitVec 5) =>
                      match i with
                      | 0#5 => x0
                      | 31#5 => sp
                      | _ => 0#64),
              sfp := (fun (_ : BitVec 5) => 0#128),
              pc  := 0x4005b4#64,
              pstate := PState.zero,
              mem := (fun (_ : BitVec 64) => 0#8),
              program := popcount32_program,
              error := StateError.None }
  let sf := run popcount32_program.length s0
  let out := read_gpr 32 0#5 sf
  let spec := popcount32_spec (BitVec.truncate 32 x0)
  (decide (Aligned sp 4), out, out == spec))

/-! ## Tests for step theorem generation -/
section Tests

/--
info: popcount32_program.stepi_eq_0x4005c0 {s : ArmState} (h_program : s.program = popcount32_program)
  (h_pc : r StateField.PC s = 4195776#64) (h_err : r StateField.ERR s = StateError.None) :
  stepi s =
    w StateField.PC (4195780#64)
      (w (StateField.GPR 0#5)
        (zeroExtend 64 ((zeroExtend 32 (r (StateField.GPR 0#5) s)).rotateRight 1) &&& 4294967295#64 &&& 2147483647#64)
        s)
-/
#guard_msgs in #check popcount32_program.stepi_eq_0x4005c0

end Tests

end popcount32
