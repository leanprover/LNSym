/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec

section TestSection

open BitVec

def test_s (inst : BitVec 32): ArmState :=
  { gpr := (fun (_ : BitVec 5) => 0#64),
    sfp := (fun (_ : BitVec 5) => 0#128),
    pc  := 0#64,
    pstate := zero_pstate,
    mem := (fun (_ : BitVec 64) => 0#8),
    -- Program: BitVec 64 → Option (BitVec 32)
    program := [(0#64, inst)],
    error := StateError.None }

-- 0x91000421#32: add x1, x1, 1
example : let s' := run 1 (test_s 0x91000421#32)
          read_gpr 64 1#5 s'
          = 1#64 := by rfl

-- (TODO) Why does rfl not work for the following anymore? It still
-- works for the example above.
--  0xd1000400#32: sub x0, x0, 1
example : let s' := run 1 (test_s 0xd1000400#32)
          read_gpr 64 0#5 s'
          = 0xFFFFFFFFFFFFFFFF#64 := by
        native_decide

example : read_mem_bytes 16 0#64 (write_mem_bytes 16 0#64 0xABCD#128 (test_s 0x3dc00080#32)) =
          0x0000000000000000000000000000abcd#128 := by
          native_decide

-- 0x3cc10410#32: ldr	q16, [x0], #16
example : (let s := test_s 0x3cc10410#32;
           let s := write_mem_bytes 16 0#64 0xABCD#128 s
           let s := run 1 s
           read_sfp 128 16#5 s) =
          (0xABCD#128 : BitVec 128) := by native_decide

theorem zeroExtend_twice (x : BitVec n) :
  zeroExtend 64 (zeroExtend 64 x) = (zeroExtend 64 x) := by
  simp

theorem zeroExtend_of_Nat_64 :
  zeroExtend 64 (BitVec.ofNat 64 x) = (BitVec.ofNat 64 x) := by
  simp

theorem zeroExtend_irrelevant (x : BitVec 64) :
  zeroExtend 64 x = x := by simp

theorem add_x1_x1_1_sym_helper (x1_var : BitVec 64) :
  (BitVec.toNat x1_var + 1)#64 = x1_var + 1#64 := by
  sorry

theorem add_x1_x1_1_sym
  (h_pc : read_pc s = 0#64)
  (h_inst : fetch_inst 0#64 s = 0x91000421#32)
  (h_x1 : x1 = read_gpr 64 1#5 s)
  (h_s_ok : read_err s = StateError.None)
  (h_s' : s' = run 1 s)
  (h_x1': x1' = read_gpr 64 1#5 s') :
  x1' = x1 + 1#64 ∧ read_err s' = StateError.None := by
  sorry
          -- simp [*] at *
          -- unfold run stepi; simp [h_pc, h_inst, h_s_ok]
          -- unfold exec_inst
          -- simp (config := { ground := true }) only [h_inst]
          -- -- This proof is still broken in `simp (config := { ground := true })`
          -- sorry
          -- unfold DPI.exec_add_sub_imm; simp (config := { ground := true })
          -- unfold AddWithCarry
          -- simp (config := { ground := true }) only [zeroExtend_twice, zeroExtend_of_Nat_64]
          -- generalize (r (StateField.GPR 1#5) s) = x1_var
          -- unfold state_value at x1_var;
          -- simp at x1_var
          -- simp [zeroExtend_irrelevant]
          -- rw [add_x1_x1_1_sym_helper]
          -- trivial

-- This version of the theorem opens up run only once. See the
-- revert...intro block below.
theorem add_x1_x1_1_sym_alt
  (h_pc : read_pc s = 0#64)
  (h_inst : fetch_inst 0#64 s = 0x91000421#32)
  (h_x1 : x1 = read_gpr 64 1#5 s)
  (h_s_ok : read_err s = StateError.None)
  (h_s' : s' = run 1 s)
  (h_x1': x1' = read_gpr 64 1#5 s') :
  x1' = x1 + 1#64 ∧ read_err s' = StateError.None := by
   repeat sorry
    -- simp at h_s_ok; simp at h_pc
    -- revert h_s'
    -- unfold run stepi; simp [h_pc, h_inst, h_s_ok]
    -- simp (config := { ground := true }) only [h_inst]

    -- This proof is still broken in `simp (config := { ground := true })`
    -- sorry

    -- unfold exec_inst; simp (config := { ground := true })
    -- -- unfold DPI.exec_add_sub_imm;
    -- -- simp (config := { ground := true })
    -- unfold AddWithCarry; simp (config := { ground := true }) only
    -- intro h_s'

    -- simp (config := { ground := true }) [*, zeroExtend_twice, zeroExtend_of_Nat_64] at *
    -- generalize (r (StateField.GPR 1#5) s) = x1_var
    -- unfold state_value at x1_var; simp at x1_var
    -- -- simp [zeroExtend_irrelevant]
    -- rw [add_x1_x1_1_sym_helper]
    -- trivial

end TestSection
