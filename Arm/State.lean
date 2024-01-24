/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Author(s): Shilpi Goel
-/
import Arm.BitVec
import Std.Data.RBMap

------------------------------------------------------------------------------
------------------------------------------------------------------------------

section State
------------------------------------------------------------------------------

---- Store formalizes the theory of arrays. ----

abbrev Store α β := α → β

def read_store {α β : Type} [DecidableEq α]
  (a : α) (store : Store α β) : β :=
  store a

def write_store {α β : Type} [DecidableEq α]
  (a : α) (b : β) (store : Store α β) : Store α β :=
  fun x => if x = a then b else (store x)

-- Let's have these theorems added to simp, but local only to this file.
@[local simp]
theorem store_read_over_write_same [DecidableEq α] (a : α) (b : β) (store : Store α β) :
  read_store a (write_store a b store) = b := by
    unfold read_store write_store
    simp

@[local simp]
theorem store_read_over_write_different [DecidableEq α]
  (a1 a2 : α) (b : β) (store : Store α β) (h : a1 ≠ a2) :
  read_store a1 (write_store a2 b store) = read_store a1 store := by
    unfold read_store write_store
    simp_all!

@[local simp]
theorem store_write_over_write_shadow [DecidableEq α]
  (a : α) (b1 b2 : β) :
  write_store a b2 (write_store a b1 store) = write_store a b2 store := by
    unfold write_store; simp_all

@[local simp]
theorem store_write_irrelevant [DecidableEq α]
  (a : α) (store : Store α β):
  write_store a (read_store a store) store = store := by
    apply funext
    unfold write_store read_store
    simp

instance [Repr β]: Repr (Store (BitVec n) β) where
  reprPrec store _ :=
    let rec helper (a : Nat) (acc : Lean.Format) :=
      let a_bv := Std.BitVec.ofNat n a
      let a_repr := "(" ++ repr a_bv ++ " : " ++ (repr (read_store a_bv store)) ++ ") "
      match a with
      | 0 => a_repr ++ acc
      | a' + 1 => helper a' (a_repr ++ acc)
    let (elide_p, upper_limit) := if n < 5 then (false, (2^n - 1)) else (true, 5)
    let ans := helper upper_limit ""
    if elide_p then (ans ++ "...") else ans

-- def init_store : Store (BitVec 5) (BitVec 10) := ((fun (_ : BitVec 5) => 0#10) : Store (BitVec 5) (BitVec 10))
-- #eval init_store
-- #eval (write_store (1#5 : BitVec 5) (2#10 : BitVec 10) init_store)
-- #eval (read_store (1#5 : BitVec 5) (write_store (1#5 : BitVec 5) (2#10 : BitVec 10) init_store))

------------------------------------------------------------------------------

---- Model of the Arm machine state ----

inductive StateError where
  | None                       : StateError
  | NotFound (e : String)      : StateError
  | Unimplemented (e : String) : StateError
  | Illegal (e : String)       : StateError
  | Fault (e : String)         : StateError
  | Other (e : String)         : StateError
deriving DecidableEq, Repr

-- PFlag (Process State's Flags)
inductive PFlag where
  | N : PFlag
  | Z : PFlag
  | C : PFlag
  | V : PFlag
deriving DecidableEq, Repr

abbrev PState := Store PFlag (BitVec 1)

instance [Repr β]: Repr (Store PFlag β) where
  reprPrec store _ :=
    let rec helper (ps : List PFlag) :=
      match ps with
      | [] => ""
      | p :: rest => "(" ++ repr p ++ " : " ++ (repr (read_store p store)) ++ ") " ++ helper rest
    open PFlag in
    helper [N, Z, C, V]

-- def init_store : Store PFlag (BitVec 1) := (fun (_ : PFlag) => 0#1)
-- #eval init_store

structure ArmState where
  -- General-purpose registers: register 31 is the stack pointer.
  gpr        : Store (BitVec 5) (BitVec 64)
  -- SIMD/floating-point registers
  sfp        : Store (BitVec 5) (BitVec 128)
  -- Program Counter
  pc         : BitVec 64
  -- PState
  pstate     : PState
  -- Memory: maps 64-bit addresses to bytes
  mem        : Store (BitVec 64) (BitVec 8)
  -- Program: maps 64-bit addresses to 32-bit instructions. None is
  -- returned when no instruction is present at a specified address.
  -- Note that we have the following assumption baked into our machine model:
  -- the program is always disjoint from the rest of the memory.
  program    : Store (BitVec 64) (Option (BitVec 32))

  -- The error field is an artifact of this model; it is set to a
  -- non-None value when some irrecoverable error is encountered
  -- (e.g., an unimplemented instruction is hit). Any reasoning or
  -- execution based off an erroneous state is invalid.
  error      : StateError
deriving Repr

---- Basic State Accessors and Updaters (except memory) ----

-- These functions should not be used as an interface to the
-- state. Instead, use functions with similar names but without the
-- "_base" substring, or functions called r and w.

-- General-purpose registers --

-- Read the `idx`-th GPR (with idx = 31 indexing the SP).
def read_base_gpr (idx : BitVec 5) (s : ArmState) : BitVec 64 :=
  read_store idx s.gpr

-- Write `val` to the `idx`-th GPR (with idx = 31 indexing the SP).
def write_base_gpr (idx : BitVec 5) (val : BitVec 64) (s : ArmState)
  : ArmState :=
    let new_gpr := write_store idx val s.gpr
    { s with gpr := new_gpr }

-- SIMD/FP Registers --

def read_base_sfp (idx : BitVec 5) (s : ArmState) : BitVec 128 :=
    read_store idx s.sfp

def write_base_sfp (idx : BitVec 5) (val : BitVec 128) (s : ArmState) : ArmState :=
   let new_sfp := write_store idx val s.sfp
   { s with sfp := new_sfp }

-- Program Counter --

def read_base_pc (s : ArmState) : BitVec 64 :=
  s.pc

def write_base_pc (val : BitVec 64) (s : ArmState) : ArmState :=
  { s with pc := val }

-- PState --

def read_base_pstate (s : ArmState) : PState :=
  s.pstate

def write_base_pstate (pstate : PState) (s : ArmState) : ArmState  :=
  { s with pstate := pstate }

def read_base_flag (flag : PFlag) (s : ArmState) : BitVec 1 :=
  read_store flag s.pstate

def write_base_flag (flag : PFlag) (val : BitVec 1) (s : ArmState) : ArmState :=
  let new_pstate := write_store flag val s.pstate
  { s with pstate := new_pstate }

-- Program --

-- Fetch the instruction at address addr.
@[irreducible]
def fetch_inst (addr : BitVec 64) (s : ArmState) : Option (BitVec 32) :=
  read_store addr s.program

-- Error --

def read_base_error (s : ArmState) : StateError :=
  s.error

def write_base_error (val : StateError) (s : ArmState) : ArmState :=
  { s with error := val }

----------------------------------------------------------------------
---- Top-level State Accessor and Updater (except Memory) ----

section Accessor_updater_functions

open Std.BitVec

inductive StateField where
  | GPR    : BitVec 5 → StateField
  | SFP    : BitVec 5 → StateField
  | PC     : StateField
  | FLAG   : PFlag → StateField
  | ERR    : StateField
deriving DecidableEq, Repr

def state_value (fld : StateField) : Type :=
  open StateField in
  match fld with
  | GPR _   => BitVec 64
  | SFP _   => BitVec 128
  | PC      => BitVec 64
  | FLAG _  => BitVec 1
  | ERR     => StateError

@[irreducible]
def r (fld : StateField) (s : ArmState) : (state_value fld) :=
  open StateField in
  match fld with
  | GPR i   => read_base_gpr i s
  | SFP i   => read_base_sfp i s
  | PC      => read_base_pc s
  | FLAG i  => read_base_flag i s
  | ERR     => read_base_error s

@[irreducible]
def w (fld : StateField) (v : (state_value fld)) (s : ArmState) : ArmState :=
  open StateField in
  match fld with
  | GPR i  => write_base_gpr i v s
  | SFP i  => write_base_sfp i v s
  | PC     => write_base_pc v s
  | FLAG i => write_base_flag i v s
  | ERR    => write_base_error v s

@[simp]
theorem r_of_w_same (fld : StateField) (v : (state_value fld)) (s : ArmState) :
  r fld (w fld v s) = v := by
  unfold r w
  unfold read_base_gpr write_base_gpr
  unfold read_base_sfp write_base_sfp
  unfold read_base_pc write_base_pc
  unfold read_base_flag write_base_flag
  unfold read_base_error write_base_error
  split <;> split <;> simp_all!

@[simp]
theorem r_of_w_different (fld1 fld2 : StateField) (v : (state_value fld2)) (s : ArmState)
  (h : fld1 ≠ fld2) :
  r fld1 (w fld2 v s) = r fld1 s := by
  unfold r w
  unfold read_base_gpr write_base_gpr
  unfold read_base_sfp write_base_sfp
  unfold read_base_pc write_base_pc
  unfold read_base_flag write_base_flag
  unfold read_base_error write_base_error
  simp_all!
  split <;> split <;> simp_all!

@[simp]
theorem w_of_w_shadow (fld : StateField) (v1 v2 : (state_value fld)) (s : ArmState) :
  w fld v2 (w fld v1 s) = w fld v2 s := by
  unfold w
  unfold write_base_gpr
  unfold write_base_sfp
  unfold write_base_pc
  unfold write_base_flag
  unfold write_base_error
  split <;> simp

@[simp]
theorem w_irrelevant (fld : StateField) (v1 v2 : (state_value fld)) (s : ArmState) :
  w fld (r fld s) s = s := by
  unfold r w
  unfold read_base_gpr write_base_gpr
  unfold read_base_sfp write_base_sfp
  unfold read_base_pc write_base_pc
  unfold read_base_flag write_base_flag
  unfold read_base_error write_base_error
  split <;> simp

@[simp]
theorem fetch_inst_of_w (addr : BitVec 64) (fld : StateField) (val : (state_value fld)) (s : ArmState) :
  fetch_inst addr (w fld val s) = fetch_inst addr s := by
  unfold fetch_inst w
  unfold write_base_gpr
  unfold write_base_sfp
  unfold write_base_pc
  unfold write_base_flag
  unfold write_base_error
  split <;> simp_all!

-- The following functions are defined in terms of r and w, but may be
-- simpler to use.

@[simp]
def read_gpr (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
    let val := r (StateField.GPR idx) s
    Std.BitVec.zeroExtend width val

-- Use read_gpr_zr when register 31 is mapped to the zero register ZR,
-- instead of the default (Stack pointer).
@[simp]
def read_gpr_zr (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
  if idx ≠ 31#5 then
    read_gpr width idx s
  else
    Std.BitVec.ofNat width 0

-- In practice, we only ever access the low 32 bits or the full 64
-- bits of these registers in Arm. When we write 32 bits to these
-- registers, the upper 32 bits are zeroed out.
@[simp]
def write_gpr (width : Nat) (idx : BitVec 5) (val : BitVec width) (s : ArmState)
  : ArmState :=
    let val := Std.BitVec.zeroExtend 64 val
    w (StateField.GPR idx) val s

-- Use write_gpr_zr when register 31 is mapped to the zero register
-- ZR, instead of the default (Stack pointer).
@[simp]
def write_gpr_zr (n : Nat) (idx : BitVec 5) (val : BitVec n) (s : ArmState)
  : ArmState :=
  if idx ≠ 31#5 then
    write_gpr n idx val s
  else
    s
-- read_gpr and write_gpr are tagged with @[simp], which let us solve
-- the following using just simp, write_gpr, read_gpr, r_of_w_same
-- (see simp?).
example (n : Nat) (idx : BitVec 5) (val : BitVec n) (s : ArmState) :
  read_gpr n idx (write_gpr n idx val s) =
  Std.BitVec.zeroExtend n (Std.BitVec.zeroExtend 64 val) := by
  simp

@[simp]
def read_sfp (width : Nat) (idx : BitVec 5) (s : ArmState) : BitVec width :=
  let val := r (StateField.SFP idx) s
  Std.BitVec.zeroExtend width val

-- Write `val` to the `idx`-th SFP, zeroing the upper bits, if
-- applicable.
@[simp]
def write_sfp (n : Nat) (idx : BitVec 5) (val : BitVec n) (s : ArmState) : ArmState :=
   let val := Std.BitVec.zeroExtend 128 val
   w (StateField.SFP idx) val s

@[simp]
def read_pc (s : ArmState) : BitVec 64 :=
  r StateField.PC s

@[simp]
def write_pc (v : BitVec 64) (s : ArmState) : ArmState :=
  w StateField.PC v s

@[simp]
def read_flag (flag : PFlag) (s : ArmState) : BitVec 1 :=
  r (StateField.FLAG flag) s

@[simp]
def write_flag (flag : PFlag) (val : BitVec 1) (s : ArmState) : ArmState :=
  w (StateField.FLAG flag) val s

@[simp]
def read_pstate (s : ArmState) : PState :=
  fun p => read_flag p s

@[simp]
def write_pstate (pstate : PState) (s : ArmState) : ArmState :=
   { s with pstate := pstate }

-- (FIXME) Define in terms of write_flag so that we see checkpoints in
-- terms of the w function.
@[simp]
def make_pstate (n z c v : BitVec 1) : PState :=
  fun (p : PFlag) =>
    open PFlag in
    match p with
      | N => n | Z => z | C => c | V => v

@[simp]
def read_err (s : ArmState) : StateError :=
  r StateField.ERR s

@[simp]
def write_err (v : StateError) (s : ArmState) : ArmState :=
  w StateField.ERR v s

end Accessor_updater_functions

----------------------------------------------------------------------

section Load_program_and_fetch_inst

-- Programs are defined as an RBMap of 64-bit addresses to 32-bit
-- instructions. RBMap has a nice find?_eq-style lemma in the Std
-- library that allows us to smoothly fetch an instruction from the
-- map during proofs (see fetch_inst_from_rbmap_program below).
--
-- TODO: Perhaps use HashMaps here when the Std library is mature?
abbrev program := Std.RBMap (BitVec 64) (BitVec 32) compare

-- We define a program as an Array of address and instruction pairs,
-- which are then converted to an RBMap.
def def_program (p : Array ((BitVec 64) × (BitVec 32))) : program :=
    Std.RBMap.ofArray p compare

theorem fetch_inst_from_rbmap_program
  {address: BitVec 64} {program : program}
  (h_program : s.program = program.find?) :
  fetch_inst address s = program.find? address := by
    unfold fetch_inst read_store
    simp_all!

end Load_program_and_fetch_inst

----------------------------------------------------------------------

example :
  read_flag flag (write_flag flag val s) = val := by
  simp

example (h : flag1 ≠ flag2) :
  read_flag flag1 (write_flag flag2 val s) = read_flag flag1 s := by
  simp [*] at *

example :
  read_gpr width idx (write_flag flag2 val s) = read_gpr width idx s := by
  simp

-- #help tactic simp

end State

----------------------------------------------------------------------
