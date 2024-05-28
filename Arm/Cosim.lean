/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec

namespace Cosim

open BitVec

/-- A default concrete state to begin co-simulations. -/
def init_cosim_state : ArmState :=
  { gpr := (fun (_ : BitVec 5) => 0#64),
    sfp := (fun (_ : BitVec 5) => 0#128),
    pc  := 0#64,
    pstate := zero_pstate,
    mem := (fun (_ : BitVec 64) => 0#8),
    program := Map.empty,
    error := StateError.None }

/-- A structure to hold both the input and output values for a
co-simulation test. -/
structure regState where
  inst  : BitVec 32
  gpr   : List (BitVec 64)
  nzcv  : BitVec 4
  sfp   : List (BitVec 64)
deriving DecidableEq, Repr

instance : ToString regState where toString a := toString (repr a)

/-- Collect `n` calls of `f` in a list. -/
def collect [Monad m] (n : Nat) (f : m α) : m (List α) := do
  let mut acc := []
  for _ in [0:n] do
    let inst ← f
    acc := acc ++ [inst]
  pure acc

/-- Initialize a regState with random values. -/
def input_regState (inst : BitVec 32) : IO regState := do
  let gpr  ← collect (m := IO) 31 (BitVec.rand 64)
  let nzcv ← BitVec.rand 4
  let sfp  ← collect (m := IO) 64 (BitVec.rand 64)
  pure { inst, gpr, nzcv, sfp }

/-- Populate the general-purpose registers in the ArmState s with
`gprs`. -/
def init_gprs (gprs : List (BitVec 64)) (s : ArmState) : ArmState := Id.run do
  let mut s := s
  for i in [0:31] do
    s := write_gpr 64 (BitVec.ofNat 5 i) gprs[i]! s
  pure s

/-- Populate the SIMD/FP registers in the ArmState s with `sfps`. Note
that the `sfps` contain 64-bit values, with the low 64-bit value of a
128-bit register appearing before the high 64-bit value. -/
def init_sfps (sfps : List (BitVec 64)) (s : ArmState) : ArmState := Id.run do
  let mut s := s
  for i in [0:32] do
      s := write_sfp 128 (BitVec.ofNat 5 i) (sfps[2*i+1]! ++ sfps[2*i]!) s
  pure s

/-- Populate the PState in the ArmState s. -/
def init_flags (flags : BitVec 4) (s : ArmState) : ArmState := Id.run do
  let s := write_flag PFlag.N (lsb flags 3) s
  let s := write_flag PFlag.Z (lsb flags 2) s
  let s := write_flag PFlag.C (lsb flags 1) s
  let s := write_flag PFlag.V (lsb flags 0) s
  pure s

/-- Initialize an ArmState for cosimulation from a given regState. -/
def regState_to_armState (r : regState) : ArmState :=
  let s := init_gprs r.gpr (init_flags r.nzcv (init_sfps r.sfp init_cosim_state))
  let s := { s with program := def_program [(0x0#64, r.inst)] }
  s

def bitvec_to_hex (x : BitVec n) : String :=
  "0x" ++ x.toHex

def bitvec_to_hex_list (xs : List (BitVec n)) : List String :=
  List.map bitvec_to_hex xs

example : String.toNat! "0x123" = 0 := by rfl

/-- Populate regState with the parsed output from the `armsimulate`
script. -/
def machine_to_regState (inst : BitVec 32) (str : String) : regState :=
  let strs := String.split (String.trim str) (fun c => c = ' ')
  -- Important: the assumption here, because of the use of
  -- String.toNat!, is that the machine output will be in base
  -- 10. This is consistent with simulator.c.
  let gpr := List.map (fun x => (BitVec.ofNat 64 x.toNat!)) (strs.take 31)
  let strs := strs.drop 31
  let flags := List.map (fun x => (BitVec.ofNat 4 x.toNat!)) (strs.take 1)
  let strs := strs.drop 1
  let sfp := List.map (fun x => (BitVec.ofNat 64 x.toNat!)) (strs.take 64)
  { inst, gpr, nzcv := flags[0]!, sfp }

/-- Call the `armsimulate` script. -/
def arm_cosim_test (input : regState) : IO String :=
  -- Input args for the armsimulate script:
  --  first, the 32-bit instruction
  --  then 31 64-bit GPRs (no SP)
  --  then 1 4-bit Flags
  --  then 32*2 64-bit SPFs
  let inst'   := bitvec_to_hex input.inst
  let gprs'   := bitvec_to_hex_list input.gpr
  let flags'  := bitvec_to_hex input.nzcv
  let sfps'   := bitvec_to_hex_list input.sfp
  let args    := ([inst'] ++ gprs' ++ [flags'] ++ sfps').toArray
  -- (FIXME): catch exception nicely
  IO.Process.run
  { cmd := "Arm/Insts/Cosim/armsimulate", args := args }

/-- Call Arm/Insts/Cosim/disasm.sh to get the disassembly of the
instruction under test. -/
def get_disasm : IO String := do
  let disasm ← IO.Process.output { cmd := "Arm/Insts/Cosim/disasm.sh" }
  if disasm.exitCode == 0 then
    pure disasm.stdout
  else
    throw (IO.userError disasm.stderr)

/-- Get the general-purpose registers in an ArmState as a list of
bitvector values.-/
def gpr_list (s : ArmState) : List (BitVec 64) := Id.run do
  let mut acc := []
  for i in [0:31] do
    acc :=  acc ++ [(s.gpr (BitVec.ofNat 5 i))]
  pure acc

/-- Get the SIMD/FP registers in an ArmState as a list of bitvector
values.-/
def sfp_list (s : ArmState) : List (BitVec 64) := Id.run do
  let mut acc := []
  for i in [0:32] do
    let reg := s.sfp (BitVec.ofNat 5 i)
    acc := acc ++ [(extractLsb 63 0 reg), (extractLsb 127 64 reg)]
  pure acc

/-- Get the flags in an ArmState as a 4-bit bitvector.-/
def nzcv (s : ArmState) : BitVec 4 :=
  let n := read_flag PFlag.N s
  let z := read_flag PFlag.Z s
  let c := read_flag PFlag.C s
  let v := read_flag PFlag.V s
  n ++ z ++ c ++ v

/-- Convert an ArmState's contents to a regState. -/
def model_to_regState (inst : BitVec 32) (s : ArmState) : regState :=
  { inst,
    gpr  := gpr_list s,
    nzcv := nzcv s,
    sfp  := sfp_list s }

def gpr_mismatch (x1 x2 : List (BitVec 64)) : IO String := do
  let mut acc := ""
  for i in [0:31] do
    if x1[i]! == x2[i]! then
      continue
    else
      acc := acc ++ s!"GPR{i} machine {x1[i]!} model {x2[i]!}"
  pure acc

def sfp_mismatch (x1 x2 : List (BitVec 64)) : IO String := do
  let mut acc := ""
  for i in [0:32] do
    let v1 := x1[2*i+1]! ++ x1[2*i]!
    let v2 := x2[2*i+1]! ++ x2[2*i]!
    if v1 == v2 then
      continue
    else
      acc := acc ++ s!"SFP{i} machine {v1} model {v2}"
  pure acc

def nzcv_mismatch (x1 x2 : BitVec 4) : IO String := do
  let mut acc := ""
  for i in [0:4] do
    let f1 := lsb x1 i
    let f2 := lsb x2 i
    if f1 == f2 then
      continue
    else
      let flag := match i with | 0 => "N" | 1 => "Z" | 2 => "C" | _ => "V"
      acc := acc ++ s!"Flag{flag} machine {f1} model {f2}"
  pure acc

def regStates_match (input o1 o2 : regState) : IO Bool := do
  if o1 == o2 then
     pure true
  else
     let gpr_mismatch ← gpr_mismatch o1.gpr o2.gpr
     let nzcv_mismatch ← nzcv_mismatch o1.nzcv o2.nzcv
     let sfp_mismatch  ← sfp_mismatch o1.sfp o2.sfp
     IO.println s!"Instruction: {decode_raw_inst input.inst}"
     IO.println s!"input: {toString input}"
     IO.println s!"Mismatch found: {gpr_mismatch} {nzcv_mismatch} {sfp_mismatch}"
     pure false

/-- Run one random test for the instruction `inst`. -/
def one_test (inst : BitVec 32) : IO Bool := do
  let input      ← input_regState inst
  let machine    ← arm_cosim_test input
  let machine_st := machine_to_regState inst machine
  let model      := run 1 (regState_to_armState input)
  let model_st := model_to_regState inst model
  regStates_match input machine_st model_st

/-- Test n random instructions, each generated by `fn`. -/
def run_n_tests (verbose : Bool) (n : Nat) (fn : IO (Option (BitVec 32)))  : IO Bool := do
  for _ in [0:n] do
    let maybe_inst ← fn
    if maybe_inst.isNone then
    -- When the underlying platform does not support the instruction
    -- under test, maybe_inst is none and we simply return true.
      return true
    else
      let inst := maybe_inst.get!
      let ret ← one_test inst
      let disasm ← get_disasm
      if verbose then IO.println s!"Instruction: {disasm}"
      if ret == false then
        throw (IO.userError "Mismatch found!")
  pure true

/-- Run n random tests for each random instruction generator in
`Insts.rand`. -/
def run_all_tests (verbose : Bool) (n : Nat) : IO UInt32 := do
  IO.println s!"Performing conformance testing..."
  let machine_check ←
    IO.Process.output
    { cmd  := "Arm/Insts/Cosim/platform_check.sh",
      args := #["-m"] }
  if machine_check.exitCode == 0 then
    -- We are on an Aarch64 machine.
    let mut acc := true
    -- Insts.rand is a list of functions of each class of instructions
    -- that generate legal, random 32-bit instructions.
    for inst_fn in Insts.rand do
        let ret ← run_n_tests verbose n inst_fn
        acc := acc && ret
    if acc then
      IO.println s!"[Conformance Testing] All tests passed!"
      pure 0
    else
      IO.println s!"[Conformance Testing] Some test FAILED."
      pure 1
  else
    IO.println s!"[Conformance Testing] Skipping; Aarch64 host not detected."
    pure 0

end Cosim
