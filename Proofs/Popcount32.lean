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
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic Simulation
  sym_n 27
  done

-- theorem popcount32_sym_meets_spec (s0 s_final : ArmState)
--   (h_s0_pc : read_pc s0 = 0x4005b4#64)
--   (h_s0_program : s0.program = popcount32_program)
--   (h_s0_sp_aligned : CheckSPAlignment s0)
--   (h_s0_err : read_err s0 = StateError.None)
--   (h_run : s_final = run 27 s0) :
--   read_gpr 32 0#5 s_final = popcount32_spec (read_gpr 32 0#5 s0) ∧
--   read_err s_final = StateError.None := by
--   -- Prelude
--   simp_all only [state_simp_rules, -h_run]
--   -- Symbolic Simulation
--   sym_n 27
--   try (clear h_step_1 h_step_2 h_step_3 h_step_4;
--        clear h_step_5 h_step_6 h_step_7 h_step_8;
--        clear h_step_9 h_step_10;
--        clear h_step_11 h_step_12 h_step_13 h_step_14;
--        clear h_step_15 h_step_16 h_step_17 h_step_18;
--        clear h_step_19 h_step_20;
--        clear h_step_21 h_step_22 h_step_23 h_step_24;
--        clear h_step_25 h_step_26)
--   -- Final Steps
--   unfold run at h_run
--   subst s_final
--   unfold popcount32_spec
--   sorry

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
