/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.Separate

section Memory

open Std.BitVec

----------------------------------------------------------------------

---- Memory accessors and updaters ----

-- We don't add the simp attribute to read/write_mem_bytes. Instead,
-- we prove and export properties about their (non)interference.

-- (FIXME) Make read_mem private.
-- We export read_mem_bytes, not read_mem.
def read_mem (addr : BitVec 64) (s : ArmState) : BitVec 8 :=
  read_store addr s.mem

def read_mem_bytes (n : Nat) (addr : BitVec 64) (s : ArmState) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := read_mem addr s
    let rest := read_mem_bytes n' (addr + 1#64) s
    have h: n' * 8 + 8 = (n' + 1) * 8 := by simp_arith
    Std.BitVec.cast h (rest ++ byte)

-- (FIXME) Make write_mem private.
-- We export write_mem_bytes, not write_mem.
def write_mem (addr : BitVec 64) (val : BitVec 8) (s : ArmState) : ArmState :=
  let new_mem := write_store addr val s.mem
  { s with mem := new_mem }

def write_mem_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 =>
    let byte := BitVec.extract val 7 0
    let s := write_mem addr byte s
    let val_rest := Std.BitVec.zeroExtend (n' * 8) (val >>> 8)
    write_mem_bytes n' (addr + 1#64) val_rest s

---- RoW/WoW lemmas about memory and other fields ----

theorem r_of_write_mem : r fld (write_mem addr val s) = r fld s := by
  unfold r
  unfold read_base_gpr read_base_sfp read_base_pc
  unfold read_base_flag read_base_error
  unfold write_mem
  split <;> simp

@[simp]
theorem r_of_write_mem_bytes :
  r fld (write_mem_bytes n addr val s) = r fld s := by
  induction n generalizing addr s
  case succ =>
    rename_i n n_ih
    unfold write_mem_bytes; simp
    rw [n_ih, r_of_write_mem]
  case zero => rfl
  done

theorem fetch_inst_of_write_mem :
  fetch_inst addr1 (write_mem addr2 val s) = fetch_inst addr1 s := by
  unfold fetch_inst write_mem
  simp

@[simp]
theorem fetch_inst_of_write_mem_bytes :
  fetch_inst addr1 (write_mem_bytes n addr2 val s) = fetch_inst addr1 s := by
  induction n generalizing addr2 s
  case zero => rfl
  case succ =>
    rename_i n n_ih
    unfold write_mem_bytes; simp
    rw [n_ih, fetch_inst_of_write_mem]
  done

theorem read_mem_of_w :
  read_mem addr (w fld v s) = read_mem addr s := by
  unfold read_mem
  unfold w write_base_gpr write_base_sfp
  unfold write_base_pc write_base_flag write_base_error
  split <;> simp

@[simp]
theorem read_mem_bytes_of_w :
  read_mem_bytes n addr (w fld v s) = read_mem_bytes n addr s := by
  induction n generalizing addr s
  case zero => rfl
  case succ =>
    rename_i n n_ih
    unfold read_mem_bytes; simp [read_mem_of_w]
    rw [n_ih]
  done

---- Memory RoW/WoW lemmas ----

theorem read_mem_of_write_mem_same :
  read_mem addr (write_mem addr v s) = v := by
  unfold read_mem write_mem; simp [store_read_over_write_same]

theorem read_mem_of_write_mem_different (h : addr1 ≠ addr2) :
  read_mem addr1 (write_mem addr2 v s) = read_mem addr1 s := by
  unfold read_mem write_mem; simp
  rw [store_read_over_write_different]; trivial

theorem write_mem_of_write_mem_shadow :
  write_mem addr val2 (write_mem addr val1 s) = write_mem addr val2 s := by
  simp [write_mem]; unfold write_store; simp_all; done

theorem write_mem_irrelevant :
  write_mem addr (read_mem addr s) s = s := by 
  simp [read_mem, write_mem, store_write_irrelevant]  

end Memory

----------------------------------------------------------------------
