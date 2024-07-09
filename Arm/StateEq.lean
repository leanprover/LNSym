/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.State
import Arm.Memory

section StateEq

open BitVec

private theorem reads_equal_implies_gpr_equal (s1 s2 : ArmState)
  (h : ∀ (f : StateField), r f s1 = r f s2) :
  ArmState.gpr s1 = ArmState.gpr s2 := by
  have h_gpr : ∀ (i : BitVec 5),
    r (StateField.GPR i) s1 = r (StateField.GPR i) s2 := by
    intro i; rw [h]
  unfold r at h_gpr
  simp only [read_base_gpr, read_store] at h_gpr
  apply funext
  assumption

private theorem reads_equal_implies_sfp_equal (s1 s2 : ArmState)
  (h : ∀ (f : StateField), r f s1 = r f s2) :
  ArmState.sfp s1 = ArmState.sfp s2 := by
  have h_sfp : ∀ (i : BitVec 5),
    r (StateField.SFP i) s1 = r (StateField.SFP i) s2 := by
    intro i; rw [h]
  unfold r at h_sfp
  simp only [read_base_sfp, read_store] at h_sfp
  apply funext
  assumption

private theorem reads_equal_implies_pc_equal (s1 s2 : ArmState)
  (h : ∀ (f : StateField), r f s1 = r f s2) :
  ArmState.pc s1 = ArmState.pc s2 := by
  have h_pc : r StateField.PC s1 = r StateField.PC s2 := by
    rw [h]
  unfold r at h_pc
  simp only [read_base_pc, read_store] at h_pc
  assumption

private theorem reads_equal_implies_pstate_equal (s1 s2 : ArmState)
  (h : ∀ (f : StateField), r f s1 = r f s2) :
  ArmState.pstate s1 = ArmState.pstate s2 := by
  have h_flag : ∀ (i : PFlag),
    r (StateField.FLAG i) s1 = r (StateField.FLAG i) s2 := by
    intro i; rw [h]
  unfold r at h_flag
  simp only [read_base_flag, read_store] at h_flag
  have h_flag_n := h_flag PFlag.N
  simp only at h_flag_n
  have h_flag_z := h_flag PFlag.Z
  simp only at h_flag_z
  have h_flag_c := h_flag PFlag.C
  simp only at h_flag_c
  have h_flag_v := h_flag PFlag.V
  simp only at h_flag_v
  clear h_flag
  rw [@PState.ext_iff s1.pstate s2.pstate]
  simp only [*, minimal_theory]
  done

private theorem reads_equal_implies_error_equal (s1 s2 : ArmState)
  (h : ∀ (f : StateField), r f s1 = r f s2) :
  ArmState.error s1 = ArmState.error s2 := by
  have h_err : r StateField.ERR s1 = r StateField.ERR s2 := by
    rw [h]
  unfold r at h_err
  simp only [read_base_error, read_store] at h_err
  assumption

private theorem read_mem_and_mem_equal (s1 s2 : ArmState)
  (h_mem : ∀ (addr : BitVec 64), read_mem addr s1 = read_mem addr s2) :
  s1.mem = s2.mem := by
  unfold read_mem read_store at h_mem
  apply funext
  simp_all only [minimal_theory]
  done

private theorem read_mem_bytes_and_read_mem (s1 s2 : ArmState)
  (h_mem : ∀ (n : Nat) (addr : BitVec 64),
      read_mem_bytes n addr s1 = read_mem_bytes n addr s2) :
  ∀ (addr : BitVec 64), read_mem addr s1 = read_mem addr s2 := by
  intro addr
  have h_read_mem_bytes_all := h_mem 1 addr
  simp [read_mem_bytes] at h_read_mem_bytes_all
  have h1 := @BitVec.empty_bitvector_append_left 8 (read_mem addr s1)
  have h2 := @BitVec.empty_bitvector_append_left 8 (read_mem addr s2)
  simp_all only
  done

private theorem read_mem_equal_implies_mem_equal (s1 s2 : ArmState)
  (h_mem : ∀ (n : Nat) (addr : BitVec 64),
    read_mem_bytes n addr s1 = read_mem_bytes n addr s2) :
  s1.mem = s2.mem := by
  rw [read_mem_and_mem_equal]; intro addr
  rwa [read_mem_bytes_and_read_mem]
  done

theorem reads_equal_implies_states_equal (s1 s2 : ArmState)
  (h_fields : ∀ (f : StateField), r f s1 = r f s2)
  (h_program : s1.program = s2.program)
  (h_mem : ∀ (n : Nat) (addr : BitVec 64),
    read_mem_bytes n addr s1 = read_mem_bytes n addr s2) :
  s1 = s2 := by
  apply ArmState.ext
  case gpr => rwa [reads_equal_implies_gpr_equal]
  case sfp => rwa [reads_equal_implies_sfp_equal]
  case pc  => rwa [reads_equal_implies_pc_equal]
  case pstate => rwa [reads_equal_implies_pstate_equal]
  case error => rwa [reads_equal_implies_error_equal]
  case program => assumption
  case mem => rwa [read_mem_equal_implies_mem_equal]
  done

theorem r_of_w_general :
  r fld1 (w fld2 v s) =
    if h : fld1 = fld2 then
      have h' : state_value fld1 = state_value fld2 := by
        simp_all
      h' ▸ v
    else
      r fld1 s := by
  by_cases h : fld1 = fld2
  case pos =>
    rw [h]; simp only [r_of_w_same, ↓reduceDIte]
  case neg =>
    simp_all only [dite_false]
    apply r_of_w_different
    assumption
  done

end StateEq
