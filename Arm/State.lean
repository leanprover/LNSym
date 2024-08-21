/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat
-/
import Lean.Data.Format
import Arm.BitVec
import Arm.Map
import Arm.Attr
import Arm.MinTheory

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
      let a_bv := BitVec.ofNat n a
      let a_repr := "(" ++ repr a_bv ++ " : " ++ (repr (read_store a_bv store)) ++ ") \n"
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

-- Injective Lemmas for StateError
attribute [state_simp_rules] StateError.NotFound.injEq
attribute [state_simp_rules] StateError.Unimplemented.injEq
attribute [state_simp_rules] StateError.Illegal.injEq
attribute [state_simp_rules] StateError.Fault.injEq
attribute [state_simp_rules] StateError.Other.injEq

-- PFlag (Process State's Flags)
inductive PFlag where
  | N : PFlag
  | Z : PFlag
  | C : PFlag
  | V : PFlag
deriving DecidableEq, Repr

instance : ToString PFlag :=
  ⟨fun p => match p with
    | PFlag.N => "N"
    | PFlag.Z => "Z"
    | PFlag.C => "C"
    | PFlag.V => "V"⟩

@[ext]
structure PState where
  n : BitVec 1
  z : BitVec 1
  c : BitVec 1
  v : BitVec 1
deriving DecidableEq, Repr

def PState.zero : PState :=
  { n := 0#1, z := 0#1, c := 0#1, v := 0#1 }

/--
Memory: maps 64-bit addresses to bytes.
We use an abbreivation to write definitions that are about memory as `*`.
-/
abbrev Memory := Store (BitVec 64) (BitVec 8)

@[ext]
structure ArmState where
  /-- General-purpose registers: register 31 is the stack pointer. -/
  private gpr        : Store (BitVec 5) (BitVec 64)
  /-- SIMD/floating-point registers -/
  private sfp        : Store (BitVec 5) (BitVec 128)
  /-- Program Counter -/
  private pc         : BitVec 64
  /-- PState -/
  private pstate     : PState
  /-- Memory: maps 64-bit addresses to bytes -/
  mem        : Memory
  /--
  Program: maps 64-bit addresses to 32-bit instructions.
  Note that we have the following assumption baked into our machine model:
  the program is always disjoint from the rest of the memory.
  -/
  program            : Program
  /--
  The error field is an artifact of this model; it is set to a
  non-None value when some irrecoverable error is encountered
  (e.g., an unimplemented instruction is hit). Any reasoning or
  execution based off an erroneous state is invalid.
  -/
  private error      : StateError
deriving Repr

def ArmState.default : ArmState := {
    gpr := fun _ => 0#64,
    sfp := fun _ => 0#128,
    pc := 0#64,
    pstate := PState.zero,
    mem := fun _ => 0#8,
    program := [],
    error := StateError.None
  }

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
  open PFlag in
  let pstate := s.pstate
  match flag with
  | N => pstate.n
  | Z => pstate.z
  | C => pstate.c
  | V => pstate.v

def write_base_flag (flag : PFlag) (val : BitVec 1) (s : ArmState) : ArmState :=
  open PFlag in
  let pstate := s.pstate
  let new_pstate :=
    match flag with
    | N => { pstate with n := val }
    | Z => { pstate with z := val }
    | C => { pstate with c := val }
    | V => { pstate with v := val }
  { s with pstate := new_pstate }

-- Program --

def set_program (s : ArmState) (program : Program) : ArmState :=
  { s with program := program }

-- Fetch the instruction at address addr.
@[irreducible]
def fetch_inst (addr : BitVec 64) (s : ArmState) : Option (BitVec 32) :=
  s.program.find? addr

-- Error --

def read_base_error (s : ArmState) : StateError :=
  s.error

def write_base_error (val : StateError) (s : ArmState) : ArmState :=
  { s with error := val }

----------------------------------------------------------------------
---- Top-level State Accessor and Updater (except Memory) ----

section Accessor_updater_functions

open BitVec

inductive StateField where
  | GPR    : BitVec 5 → StateField
  | SFP    : BitVec 5 → StateField
  | PC     : StateField
  | FLAG   : PFlag → StateField
  | ERR    : StateField
deriving DecidableEq, Repr

instance : ToString StateField :=
  ⟨fun s => match s with
  | StateField.GPR i  => "x" ++ (ToString.toString i.toNat)
  | StateField.SFP i  => "q" ++ (ToString.toString i.toNat)
  | StateField.PC     => "pc"
  | StateField.FLAG p => "flag" ++ (ToString.toString p)
  | StateField.ERR    => "err"⟩

-- Injective Lemmas for StateField
attribute [state_simp_rules] StateField.GPR.injEq
attribute [state_simp_rules] StateField.SFP.injEq
attribute [state_simp_rules] StateField.FLAG.injEq

@[reducible]
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

@[state_simp_rules]
theorem zeroExtend_eq_of_r_gpr :
  zeroExtend 64 (r (StateField.GPR i) s) = (r (StateField.GPR i) s) := by
  simp only [bitvec_rules]

@[state_simp_rules]
theorem zeroExtend_eq_of_r_sfp :
  zeroExtend 128 (r (StateField.SFP i) s) = (r (StateField.SFP i) s) := by
  simp only [bitvec_rules]

@[state_simp_rules]
theorem zeroExtend_eq_of_r_pc :
  zeroExtend 64 (r (StateField.PC) s) = (r (StateField.PC) s) := by
  simp only [bitvec_rules]

@[state_simp_rules]
theorem r_of_w_same : r fld (w fld v s) = v := by
  unfold r w
  unfold read_base_gpr write_base_gpr
  unfold read_base_sfp write_base_sfp
  unfold read_base_pc write_base_pc
  unfold read_base_flag write_base_flag
  unfold read_base_error write_base_error
  split <;> (repeat (split <;> simp_all!))

@[state_simp_rules]
theorem r_of_w_different (h : fld1 ≠ fld2) :
  r fld1 (w fld2 v s) = r fld1 s := by
  unfold r w
  unfold read_base_gpr write_base_gpr
  unfold read_base_sfp write_base_sfp
  unfold read_base_pc write_base_pc
  unfold read_base_flag write_base_flag
  unfold read_base_error write_base_error
  simp_all!
  split <;> (repeat (split <;> simp_all!))

@[state_simp_rules]
theorem w_of_w_shadow : w fld v2 (w fld v1 s) = w fld v2 s := by
  unfold w
  unfold write_base_gpr
  unfold write_base_sfp
  unfold write_base_pc
  unfold write_base_flag
  unfold write_base_error
  (repeat (split <;> simp_all!))

@[state_simp_rules]
theorem w_irrelevant : w fld (r fld s) s = s := by
  unfold r w
  unfold read_base_gpr write_base_gpr
  unfold read_base_sfp write_base_sfp
  unfold read_base_pc write_base_pc
  unfold read_base_flag write_base_flag
  unfold read_base_error write_base_error
  repeat (split <;> simp_all)

@[state_simp_rules]
theorem fetch_inst_of_w : fetch_inst addr (w fld val s) = fetch_inst addr s := by
  unfold fetch_inst w
  unfold write_base_gpr
  unfold write_base_sfp
  unfold write_base_pc
  unfold write_base_flag
  unfold write_base_error
  split <;> simp_all!

-- There is no StateField that overwrites the program.
@[state_simp_rules]
theorem w_program : (w fld v s).program = s.program := by
  intros
  cases fld <;> unfold w <;> simp
  · unfold write_base_gpr; simp
  · unfold write_base_sfp; simp
  · unfold write_base_pc; simp
  · unfold write_base_flag; simp
  · unfold write_base_error; simp

-- The following functions are defined in terms of r and w, but may be
-- simpler to use.

@[state_simp_rules]
def read_gpr (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
    let val := r (StateField.GPR idx) s
    BitVec.zeroExtend width val

-- Use read_gpr_zr when register 31 is mapped to the zero register ZR,
-- instead of the default (Stack pointer).
@[state_simp_rules]
def read_gpr_zr (width : Nat) (idx : BitVec 5) (s : ArmState)
  : BitVec width :=
  if idx ≠ 31#5 then
    read_gpr width idx s
  else
    BitVec.ofNat width 0

-- In practice, we only ever access the low 32 bits or the full 64
-- bits of these registers in Arm. When we write 32 bits to these
-- registers, the upper 32 bits are zeroed out.
@[state_simp_rules]
def write_gpr (width : Nat) (idx : BitVec 5) (val : BitVec width) (s : ArmState)
  : ArmState :=
    let val := BitVec.zeroExtend 64 val
    w (StateField.GPR idx) val s

-- Use write_gpr_zr when register 31 is mapped to the zero register
-- ZR, instead of the default (Stack pointer).
@[state_simp_rules]
def write_gpr_zr (n : Nat) (idx : BitVec 5) (val : BitVec n) (s : ArmState)
  : ArmState :=
  if idx ≠ 31#5 then
    write_gpr n idx val s
  else
    s
-- read_gpr and write_gpr are tagged with @[state_simp_rules], which let us solve
-- the following using just simp, write_gpr, read_gpr, r_of_w_same
-- (see simp?).
example (n : Nat) (idx : BitVec 5) (val : BitVec n) (s : ArmState) :
  read_gpr n idx (write_gpr n idx val s) =
  BitVec.zeroExtend n (BitVec.zeroExtend 64 val) := by
  simp [state_simp_rules, minimal_theory]

@[state_simp_rules]
def read_sfp (width : Nat) (idx : BitVec 5) (s : ArmState) : BitVec width :=
  let val := r (StateField.SFP idx) s
  BitVec.zeroExtend width val

-- Write `val` to the `idx`-th SFP, zeroing the upper bits, if
-- applicable.
@[state_simp_rules]
def write_sfp (n : Nat) (idx : BitVec 5) (val : BitVec n) (s : ArmState) : ArmState :=
   let val := BitVec.zeroExtend 128 val
   w (StateField.SFP idx) val s

@[state_simp_rules]
def read_pc (s : ArmState) : BitVec 64 :=
  r StateField.PC s

@[state_simp_rules]
def write_pc (v : BitVec 64) (s : ArmState) : ArmState :=
  w StateField.PC v s

@[state_simp_rules]
def read_flag (flag : PFlag) (s : ArmState) : BitVec 1 :=
  r (StateField.FLAG flag) s

@[state_simp_rules]
def write_flag (flag : PFlag) (val : BitVec 1) (s : ArmState) : ArmState :=
  w (StateField.FLAG flag) val s

@[state_simp_rules]
def read_pstate (s : ArmState) : PState :=
  s.pstate

@[state_simp_rules]
def write_pstate (pstate : PState) (s : ArmState) : ArmState :=
  open StateField PFlag in
  let s := w (FLAG N) pstate.n s
  let s := w (FLAG Z) pstate.z s
  let s := w (FLAG C) pstate.c s
  let s := w (FLAG V) pstate.v s
  s

@[state_simp_rules]
def make_pstate (n z c v : BitVec 1) : PState :=
  { n, z, c, v }

@[state_simp_rules]
def read_err (s : ArmState) : StateError :=
  r StateField.ERR s

@[state_simp_rules]
def write_err (v : StateError) (s : ArmState) : ArmState :=
  w StateField.ERR v s

end Accessor_updater_functions

----------------------------------------------------------------------

section Load_program_and_fetch_inst

def def_program (p : Program) : Program :=
  p

/-- Get the smallest address in a program `p`. Returns `none` if the program is empty. -/
def Program.min? (p : Program) : Option (BitVec 64) :=
  loop p none
where
  loop (p : Program) (min? : Option (BitVec 64)) : Option (BitVec 64) :=
    match p, min? with
    | [], _ => min?
    | (addr, _) :: p, none => loop p (some addr)
    | (addr, _) :: p, some min => if addr < min then loop p (some addr) else loop p (some min)

/-- Get the largest address in a program `p`. Returns `none` if the program is empty. -/
def Program.max? (p : Program) : Option (BitVec 64) :=
  loop p none
where
  loop (p : Program) (max? : Option (BitVec 64)) : Option (BitVec 64) :=
    match p, max? with
    | [], _ => max?
    | (addr, _) :: p, none => loop p (some addr)
    | (addr, _) :: p, some max => if addr > max then loop p (some addr) else loop p (some max)

/-- Get the smallest address in a program `p`, given a proof that such an address exists. -/
def Program.min (p : Program) (h : p.min?.isSome := by decide) : BitVec 64 := p.min?.get h
/-- Get the smallest address in a program `p`. Panics if the program is empty -/
def Program.min! (p : Program) : BitVec 64 := p.min?.get!

/-- Get the largest address in a program `p`, given a proof that such an address exists. -/
def Program.max (p : Program) (h : p.max?.isSome := by decide) : BitVec 64 := p.max?.get h
/-- Get the largest address in a program `p`. Panics if the program is empty -/
def Program.max! (p : Program) : BitVec 64 := p.max?.get!

theorem fetch_inst_from_program
  {address: BitVec 64} :
  fetch_inst address s = s.program.find? address := by
    unfold fetch_inst
    simp only

theorem fetch_inst_eq_of_prgram_eq_of_map_find
    {state : ArmState} {program : Program}
    {addr : BitVec 64} {inst? : Option (BitVec 32)}
    (h_program : state.program = program)
    (h_map : program.find? addr = inst?) :
    fetch_inst addr state = inst? := by
  rw [fetch_inst, h_program, h_map]

end Load_program_and_fetch_inst

----------------------------------------------------------------------

example :
  read_flag flag (write_flag flag val s) = val := by
  simp only [state_simp_rules, minimal_theory]

example (h : flag1 ≠ flag2) :
  read_flag flag1 (write_flag flag2 val s) = read_flag flag1 s := by
  simp_all only [state_simp_rules, minimal_theory]

example :
  read_gpr width idx (write_flag flag2 val s) = read_gpr width idx s := by
  simp only [state_simp_rules, minimal_theory]

end State

/-! # Memory operations on State. -/

section Memory

/-!
Ideally, `read_mem` and `write_mem` ought to be private, and we ought to only
expose `read_mem_bytes` and `write_mem_bytes` to the outside world.
However, due to layering violations with `Arm/MemoryProofs.lean`, we currently keep them public.
-/


/-- We export read_mem_bytes, not read_mem. FIXME: make private. -/
def read_mem (addr : BitVec 64) (s : ArmState) : BitVec 8 :=
  read_store addr s.mem

/--
We don't add the simp attribute to read/write_mem_bytes. Instead,
we prove and export properties about their (non)interference.
-/
def read_mem_bytes (n : Nat) (addr : BitVec 64) (s : ArmState) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := read_mem addr s
    let rest := read_mem_bytes n' (addr + 1#64) s
    (rest ++ byte).cast (by omega)

/-- We export write_mem_bytes, not write_mem. FIXME: make private. -/
def write_mem (addr : BitVec 64) (val : BitVec 8) (s : ArmState) : ArmState :=
  let new_mem := write_store addr val s.mem
  { s with mem := new_mem }

def write_mem_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 =>
    let byte := BitVec.extractLsb 7 0 val
    let s := write_mem addr byte s
    let val_rest := BitVec.zeroExtend (n' * 8) (val >>> 8)
    write_mem_bytes n' (addr + 1#64) val_rest s


/-! # Memory accessors and updaters -/

/-! ### RoW/WoW lemmas about memory and other fields -/

theorem r_of_write_mem : r fld (write_mem addr val s) = r fld s := by
  unfold r
  unfold read_base_gpr read_base_sfp read_base_pc
  unfold read_base_flag read_base_error
  unfold write_mem
  split <;> simp

@[state_simp_rules]
theorem r_of_write_mem_bytes :
  r fld (write_mem_bytes n addr val s) = r fld s := by
  induction n generalizing addr s
  case succ =>
    rename_i n n_ih
    unfold write_mem_bytes; simp only
    rw [n_ih, r_of_write_mem]
  case zero => rfl
  done

theorem fetch_inst_of_write_mem :
  fetch_inst addr1 (write_mem addr2 val s) = fetch_inst addr1 s := by
  unfold fetch_inst write_mem
  simp

@[state_simp_rules]
theorem fetch_inst_of_write_mem_bytes :
  fetch_inst addr1 (write_mem_bytes n addr2 val s) = fetch_inst addr1 s := by
  induction n generalizing addr2 s
  case zero => rfl
  case succ =>
    rename_i n n_ih
    unfold write_mem_bytes; simp only
    rw [n_ih, fetch_inst_of_write_mem]
  done

theorem read_mem_of_w :
  read_mem addr (w fld v s) = read_mem addr s := by
  unfold read_mem
  unfold w write_base_gpr write_base_sfp
  unfold write_base_pc write_base_flag write_base_error
  split <;> simp

@[state_simp_rules]
theorem read_mem_bytes_of_w :
  read_mem_bytes n addr (w fld v s) = read_mem_bytes n addr s := by
  induction n generalizing addr s
  case zero => rfl
  case succ =>
    rename_i n n_ih
    unfold read_mem_bytes; simp only [read_mem_of_w]
    rw [n_ih]
  done

@[state_simp_rules]
theorem write_mem_bytes_program {n : Nat} (addr : BitVec 64) (bytes : BitVec (n * 8)):
    (write_mem_bytes n addr bytes s).program = s.program := by
  intros
  induction n generalizing addr s
  · simp [write_mem_bytes]
  · rename_i n h_n
    simp only [write_mem_bytes]
    rw [h_n]
    simp only [write_mem]

/-! ### Memory RoW/WoW lemmas -/

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


/-!
# New definitions for the memory model

For freedom in experimenting with definitions,
we define our own version of `read_mem` and `write_mem`,
called `Memory.read` and `Memory.write`.
These operate directly on the memory, rather than the `ArmState`.
We prove their equivalence to the existing definitions
(`ArmState.read_mem_eq_mem_read`, `ArmState.write_mem_eq_mem_write`).

Furthermore, we define equivalences to `BitVec.extractLsByte`
to ease reasoning about byte-level manipulation.
As an easy corollary, we get `getLsb` theorems on these to allow
`omega` based reasoning about bit-level values of memory.
-/

/--
A variant of `read_mem` that directly talks about writes to memory, instead of over the entire `ArmState`
-/
def Memory.read (addr : BitVec 64) (m : Memory) : BitVec 8 :=
  read_store addr m

/--
Extracting a byte out of a byte returns the value if `i = 0`, and `0#8`
otherwise.
-/
@[memory_rules]
theorem Memory.extractLsByte_read (m : Memory) :
    (m.read addr).extractLsByte i = if i = 0 then m.read addr else 0#8 := by
  rw [BitVec.extractLsByte_def]
  by_cases hi : i = 0
  · subst hi
    simp only [bitvec_rules, minimal_theory]
    apply BitVec.eq_of_getLsb_eq
    simp
    omega
  · simp only [hi, ↓reduceIte]
    apply BitVec.eq_of_getLsb_eq
    intros j
    simp only [bitvec_rules, minimal_theory]
    intros _hj
    apply BitVec.getLsb_ge
    omega

theorem ArmState.read_mem_eq_mem_read : read_mem addr s = s.mem.read addr := rfl

/--
A variant of `write_mem` that directly talks about writes to memory, instead of over the entire `ArmState`
-/
def Memory.write (addr : BitVec 64) (val : BitVec 8) (m : Memory) : Memory :=
  write_store addr val m

theorem ArmState.write_mem_eq_mem_write :  (write_mem addr val s).mem = s.mem.write addr val := rfl

namespace Memory

theorem getLsb_read (mem : Memory) : (mem.read addr).getLsb i = (mem addr).getLsb i := rfl

def read_bytes (n : Nat) (addr : BitVec 64) (m : Memory) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := m.read addr
    let rest := m.read_bytes n' (addr + 1#64)
    have h : n' * 8 + 8 = (n' + 1) * 8 := by simp_arith
    BitVec.cast h (rest ++ byte)

@[memory_rules]
theorem State.read_mem_bytes_eq_mem_read_bytes (s : ArmState) :
    read_mem_bytes n addr s = s.mem.read_bytes n addr := by
  induction n generalizing addr s
  case zero => simp [read_mem_bytes, read_bytes]
  case succ n' ih =>
    simp [read_mem_bytes, read_bytes, ArmState.read_mem_eq_mem_read, ih]

@[memory_rules]
theorem read_bytes_zero_eq (m : Memory) : m.read_bytes 0 addr = 0#0 :=
  rfl

theorem read_bytes_succ_eq (m : Memory) :
  m.read_bytes (n' + 1) addr = (m.read_bytes n' (addr + 1) ++ m.read addr).cast (by omega) := rfl

theorem getLsb_read_bytes {n i : Nat} {addr : BitVec 64} {m : Memory} (hn : n ≤ 2^64) :
    (m.read_bytes n addr).getLsb i =
    (decide (i < n * 8) && (m (addr + BitVec.ofNat 64 (i / 8))).getLsb (i % 8)) := by
  induction n generalizing i addr m
  case zero =>
    simp only [Nat.reduceMul, Nat.zero_le, BitVec.getLsb_ge, Nat.zero_mul, Nat.not_lt_zero,
      decide_False, Bool.false_and]
  case succ n' ih =>
    simp only [read_bytes_succ_eq, BitVec.ofNat_eq_ofNat,
      BitVec.getLsb_cast, BitVec.getLsb_append, memory_rules,
      getLsb_read]
    rw [Nat.succ_mul]
    by_cases h₁ : (i < 8)
    · simp only [h₁, decide_True, cond_true, show i < n' * 8 + 8 by omega, Bool.true_and]
      have hdiv : i / 8 = 0 :=  Nat.div_eq_of_lt h₁
      rw [hdiv]
      simp only [BitVec.add_zero]
      have hmod : i % 8 = i := Nat.mod_eq_of_lt h₁
      simp [hmod]
    · simp only [h₁, decide_False, cond_false]
      rw [ih]
      by_cases h₂ : i - 8 < n' * 8
      · simp only [h₂, decide_True, Bool.true_and, show (i < n' * 8 + 8) by omega]
        have hi' : ∃ i', i = i' + 8 := by
          apply Classical.byContradiction
          intros h
          simp only [not_exists] at h
          specialize h (i - 8)
          omega
        obtain ⟨i', hi'⟩ := hi'
        subst hi'
        simp only [Nat.add_sub_cancel, Nat.zero_lt_succ, Nat.add_div_right, Nat.add_mod_right]
        congr 2
        rw [BitVec.add_assoc]
        congr
        rw [BitVec.add_def]
        congr 1
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        rw [Nat.mod_eq_of_lt]
        · omega
        · omega
      · simp only [h₂, decide_False, Bool.false_and, Bool.false_eq, Bool.and_eq_false_imp,
          decide_eq_true_eq]
        intros h₃
        omega
      · omega

/--
The describes the behaviour of `m.read_bytes` at a byte level granularity.
-/
@[memory_rules]
theorem extractLsByte_read_bytes {n i : Nat} {addr : BitVec 64} {m : Memory} (h : addr.toNat + n ≤ 2^64) :
    (m.read_bytes n addr).extractLsByte i =
      if i < n then m.read (addr + (BitVec.ofNat 64 i)) else 0#8 := by
  apply BitVec.eq_of_getLsb_eq
  simp only [BitVec.getLsb_extractLsByte]
  intros j
  simp only [show (j : Nat) ≤ 7 by omega, decide_True, Bool.true_and]
  rw [getLsb_read_bytes]
  by_cases h₁ : i * 8 + ↑j < n * 8
  · simp only [h₁, decide_True, Bool.true_and]
    simp only [show (i < n) by omega, ↓reduceIte]
    simp only [show (i * 8 + ↑j) / 8 = i by omega]
    simp only [show (i * 8 + ↑j) % 8 = j by omega]
    rfl
  · simp only [h₁, decide_False, Bool.false_and, Bool.false_eq]
    simp only [show ¬(i < n) by omega, ↓reduceIte, BitVec.getLsb_zero]
  · omega

/--
This is a low level theorem.
Prefer using theorems from `Arm.Separate` that provide higher level theorems
in terms of memory (non)-interference.
-/
theorem write_of_eq {m : Memory} (hix : ix = addr) : m.write addr val ix = val := by
  simp only [write]
  subst ix
  apply store_read_over_write_same

@[memory_rules]
theorem write_of_eq' {m : Memory} : m.write ix val ix = val := write_of_eq rfl

/--
This is a low level theorem.
Prefer using theorems from `Arm.Separate` that provide higher level theorems
in terms of memory (non)-interference.
-/
theorem write_of_neq {m : Memory} (hix : ix ≠ addr) : m.write addr val ix = m ix := by
  simp only [write]
  apply store_read_over_write_different
  assumption

def write_bytes (n : Nat) (addr : BitVec 64)
    (val : BitVec (n * 8)) (m : Memory) : Memory :=
  match n with
  | 0 => m
  | n' + 1 =>
    let byte := BitVec.extractLsb 7 0 val
    let m := m.write addr byte
    let val_rest := BitVec.zeroExtend (n' * 8) (val >>> 8)
    m.write_bytes n' (addr + 1#64) val_rest

/-- Writing zero bytes does not change memory. -/
@[memory_rules]
theorem write_bytes_zero {m : Memory} : m.write_bytes 0 addr val = m := rfl

@[memory_rules]
theorem write_mem_bytes_eq_mem_write_bytes (s : ArmState) :
    write_mem_bytes n addr val s =
    { s with mem := s.mem.write_bytes n addr val } := by
  induction n generalizing addr s
  case zero => simp [write_mem_bytes, write_bytes_zero]
  case succ n' ih =>
    simp [write_mem_bytes, ArmState.read_mem_eq_mem_read, ih,
      write_mem, write_bytes]
    rfl

/--
Writing (n + 1) bytes can be described as writing `n` bytes
and then recursing to write the rest.
-/
theorem write_bytes_succ {mem : Memory} :
    mem.write_bytes (n + 1) addr val =
    let byte := BitVec.extractLsb 7 0 val
    let mem := mem.write addr byte
    let val_rest := BitVec.zeroExtend (n * 8) (val >>> 8)
    mem.write_bytes n (addr + 1#64) val_rest := rfl

theorem write_bytes_eq_of_le  {mem : Memory} {ix base : BitVec 64}
    (hix : ix.toNat < base.toNat) (hnowrap : base.toNat + n ≤ 2^64) :
    mem.write_bytes n base data ix = mem ix := by
  induction n generalizing base mem ix
  case zero => simp only [write_bytes]
  case succ n ih =>
    simp only [write_bytes]
    rcases n with rfl | n
    · rw [write_bytes_zero]
      apply write_of_neq (BitVec.neq_of_lt hix)
    · rw [ih]
      · apply write_of_neq (BitVec.neq_of_lt hix)
      · rw [BitVec.toNat_add_eq_toNat_add_toNat]
        · omega
        · simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      · rw [BitVec.toNat_add_eq_toNat_add_toNat]
        · simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
        · simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega

theorem write_bytes_eq_of_ge {mem : Memory} {ix base : BitVec 64}
    (hix : ix.toNat ≥ base.toNat + n)
    (hnowrap : base.toNat + n ≤ 2^64) :
    mem.write_bytes n base data ix = mem ix := by
  induction n generalizing base mem ix
  case zero => simp [write_bytes]
  case succ n ih =>
    simp only [write_bytes]
    rw [ih]
    · have hix : ix.toNat > base.toNat := by omega
      obtain hix : ix.toNat ≠ base.toNat := by omega
      apply write_of_neq (by apply BitVec.neq_of_toNat_neq hix)
    · rw [BitVec.toNat_add_eq_toNat_add_toNat
        (by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ge_iff_le]; omega
    · rw [BitVec.toNat_add_eq_toNat_add_toNat
        (by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega

theorem extractLsByte_zeroExtend_shiftLeft (data : BitVec ((n + 1) * 8)) (hi : i > 0):
    (BitVec.zeroExtend (n * 8) (data >>> 8)).extractLsByte (i - 1) = data.extractLsByte i := by
  rcases i with rfl | i
  · simp at hi
  · apply BitVec.eq_of_getLsb_eq
    intros j
    simp only [Nat.add_one_sub_one, BitVec.getLsb_extractLsByte, BitVec.getLsb_zeroExtend,
      BitVec.getLsb_ushiftRight]
    by_cases hj : (j : Nat) ≤ 7
    · simp only [hj, decide_True, Bool.true_and]
      by_cases hi' : i * 8 + ↑j < n * 8
      · simp only [hi', decide_True, Bool.true_and]
        simp only at hi' ⊢
        congr 1
        omega
      · by_cases hi' : i * 8 + ↑j < n * 8
        · simp only [hi', decide_True, Bool.true_and]
          congr 1
          rw [Nat.add_mul]
          omega
        · simp only [hi', decide_False, Bool.false_and, Bool.false_eq]
          apply BitVec.getLsb_ge
          rw [Nat.add_mul, Nat.add_mul]
          omega
    · simp only [hj, decide_False, Bool.false_and]

/--
The byte at location `ix` in memory, such that `base ≤ ix ≤ base + ix` will be the `ix - base` byte of `data`.
-/
theorem write_bytes_eq_extractLsByte {ix base : BitVec 64} {m : Memory}
  (lo : ix.toNat ≥ base.toNat)
  (hi : ix.toNat < base.toNat + n) (hnowrap : base.toNat + n ≤ 2^64) :
    m.write_bytes n base data ix = data.extractLsByte (ix - base).toNat := by
  induction n generalizing base m ix
  case zero => omega
  case succ n ih =>
    simp only [write_bytes]
    by_cases hix : ix.toNat = base.toNat
    · obtain hix : ix = base := by apply BitVec.eq_of_toNat_eq hix
      subst hix
      simp only [BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
      rcases n with rfl | n
      · simp only [Nat.reduceAdd, Nat.reduceMul, write_bytes_zero,
          write_of_eq (ix := ix) rfl]
        rfl
      · rw [write_bytes_eq_of_le (by bv_omega) (by bv_omega)]
        simp only [write_of_eq rfl, BitVec.extractLsByte_def, Nat.reduceAdd, Nat.reduceMul,
          Nat.add_one_sub_one, Nat.sub_zero, BitVec.cast_eq]
    · rw [ih (by bv_omega) (by bv_omega) (by bv_omega)]
      rw [show (ix - (base + 1#64)).toNat = ix.toNat - (base + 1#64).toNat by
        bv_omega]
      rw [show (base + 1#64).toNat = base.toNat + 1 by bv_omega]
      rw [show (ix - base).toNat = ix.toNat - base.toNat by bv_omega]
      rw [Nat.sub_add_eq,
        show ix.toNat - base.toNat - 1 = (ix.toNat - base.toNat) - 1 by omega]
      apply extractLsByte_zeroExtend_shiftLeft
      omega

/--
This is a low level theorem.
Prefer using theorems from `Arm.Separate` that provide higher level theorems
in terms of memory (non)-interference.
-/
theorem write_bytes_eq {mem : Memory} (hoverflow : base.toNat + n ≤ 2 ^ 64) :
  ((write_bytes n base data mem) ix) =
    if ix < base
    then mem ix
    else if ix.toNat ≥ base.toNat + n then mem ix
    else data.extractLsByte (ix - base).toNat := by
  by_cases h : ix < base
  · simp only [h, ↓reduceIte]
    apply write_bytes_eq_of_le h hoverflow
  · simp only [h, ↓reduceIte]
    by_cases h₂ : ix.toNat ≥ base.toNat + n
    · simp only [ge_iff_le, h₂, ↓reduceIte]
      apply write_bytes_eq_of_ge h₂ hoverflow
    · simp only [ge_iff_le, h₂, ↓reduceIte]
      apply write_bytes_eq_extractLsByte
      · simp only [BitVec.not_lt] at h
        rw [BitVec.le_def] at h
        omega
      · omega
      · omega

/--
This is a low level theorem.
Prefer using theorems from `Arm.Separate` that provide higher level theorems
in terms of memory (non)-interference.
-/
theorem getLsb_write_bytes (hoverflow : base.toNat + n ≤ 2 ^ 64) :
  ((write_bytes n base data mem) ix).getLsb i =
  if ix < base
  then (mem ix).getLsb i
  else if ix.toNat ≥ base.toNat + n then (mem ix).getLsb i
  else (data.extractLsByte (ix - base).toNat).getLsb i := by
rw [write_bytes_eq hoverflow]
by_cases h : ix < base
· simp only [h, ↓reduceIte]
· simp only [h, ↓reduceIte, ge_iff_le, BitVec.toNat_sub, Nat.reducePow, BitVec.getLsb_extractLsByte]
  by_cases h₂ : base.toNat + n ≤ ix.toNat
  · simp only [h₂, ↓reduceIte]
  · simp only [h₂, ↓reduceIte, BitVec.getLsb_extractLsByte]

end Memory
