/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat
-/
import Arm.Exec

namespace Cosim

/-
NOTE: Considerations for running cosimulations on Arm-based Apple platforms:

On Arm-based Apple platforms, we completely avoid using the register
`x18`. It is not allowed to be a source or a destination operand --
see `GPRIndex.rand`. Even with these restrictions, we cannot expect
the value of `x18` to be preserved, even though it is callee-saved --
see Arm/Insts/Cosim/template.S. Here's a quote from "Procedure Call
Standard for the Arm 64-bit Architecture" (the latest version is
available at https://github.com/ARM-software/abi-aa/releases) that
informs this choice:

"The role of register r18 is platform specific. If a platform ABI has
need of a dedicated general-purpose register to carry inter-procedural
state (for example, the thread context) then it should use this
register for that purpose. If the platform ABI has no such
requirements, then it should use r18 as an additional temporary
register. The platform ABI specification must document the usage for
this register...

Software developers creating platform-independent code are advised to
avoid using r18 if at all possible. Most compilers provide a mechanism
to prevent specific registers from being used for general allocation;
portable hand-coded assembler should avoid it entirely...

It should not be assumed that treating the register as callee-saved
will be sufficient to satisfy the requirements of the platform."

Our conformance testing framework is parallelized -- we spawn a task
for each random test. This is why we cannot expect the contents of
`x18` to be preserved -- `x18` is reserved on Apple's Arm machines and
probably carries thread context (though we haven't actually found a
reference for the latter). See
https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms#Respect-the-purpose-of-specific-CPU-registers
for details.

As such, when we check whether our model's state matches the machine
after every instruction test, we ignore the contents of `x18` only on
Arm-based Apple machines -- `x18` is still checked on other Arm
machines. See `gpr_mismatch` and `regStates_match` for details.
-/

open BitVec

/-- A default concrete state to begin co-simulations. -/
def init_cosim_state : ArmState :=
  { gpr := (fun (_ : BitVec 5) => 0#64),
    sfp := (fun (_ : BitVec 5) => 0#128),
    pc  := 0#64,
    pstate := PState.zero,
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
  let s := set_program s (def_program [(0x0#64, r.inst)])
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

/--
Call the `armsimulate <uniqueBaseName> <input>` script to
build an executable and report the results of executing <input>.
The <uniqueBaseName> is used to produce a unique object file per test case.
The object file is used to report the disassembled instruction.
Therefore, we need a  unique base name per test.
-/
def arm_cosim_test (input : regState) (uniqueBaseName : String) : IO String := do
  -- Input args for the armsimulate script:
  --  first, the 32-bit instruction
  --  then 31 64-bit GPRs (no SP)
  --  then 1 4-bit Flags
  --  then 32*2 64-bit SPFs
  let inst'   := bitvec_to_hex input.inst
  let gprs'   := bitvec_to_hex_list input.gpr
  let flags'  := bitvec_to_hex input.nzcv
  let sfps'   := bitvec_to_hex_list input.sfp
  let args    := [uniqueBaseName] ++ [inst'] ++ gprs' ++ [flags'] ++ sfps' |>.toArray
  let sargs := { cmd := "Arm/Insts/Cosim/armsimulate", args }
  -- Copied from IO.Process.run:
  let out ← IO.Process.output sargs
  if out.exitCode != 0 then
    throw
      <| IO.userError
      <| s!"Process '{sargs.cmd}' exited with code {out.exitCode}\nStdErr: {out.stderr}" ++
          (if out.stdout.isEmpty then "" else s!"\nStdOut:\n{out.stdout}")
  pure out.stdout

/--
Call Arm/Insts/Cosim/disasm.sh
to get the disassembly of the instruction under test.
We give it the base name of the test to find the object file to disassemble.
-/
def get_disasm (uniqueBaseName : String) : IO String := do
  let disasm ← IO.Process.output {
    cmd := "Arm/Insts/Cosim/disasm.sh",
    args := #[toString uniqueBaseName]
  }
  if disasm.exitCode == 0 then
    pure disasm.stdout
  else
    throw (IO.userError disasm.stderr)

/-- Get the general-purpose registers in an ArmState as a list of
bitvector values.-/
def gpr_list (s : ArmState) : List (BitVec 64) := Id.run do
  let mut acc := []
  for i in [0:31] do
    acc :=  acc ++ [read_gpr 64 (BitVec.ofNat 5 i) s]
  pure acc

/-- Get the SIMD/FP registers in an ArmState as a list of bitvector
values.-/
def sfp_list (s : ArmState) : List (BitVec 64) := Id.run do
  let mut acc := []
  for i in [0:32] do
    let reg := read_sfp 128 (BitVec.ofNat 5 i) s
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

/-- Check whether the machine and model GPRs match. We ignore register
`x18` on Arm-based Apple platforms because `x18` cannot be guaranteed
to be preserved there. -/
def gpr_mismatch (isDarwin : Bool) (x1 x2 : List (BitVec 64)) : IO String := do
  let mut acc := ""
  for i in [0:31] do
    if isDarwin && i == 18 then
      -- Ignore x18 contents.
      continue
    else if x1[i]! == x2[i]! then
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

def regStates_match (uniqueBaseName : String) (input o1 o2 : regState) :
  IO Bool := do
  if o1 == o2 then
      pure true
  else
    let darwin_check ←
    IO.Process.output
      { cmd  := "Arm/Insts/Cosim/platform_check.sh",
        args := #["-d"] }
    let isDarwin := (darwin_check.exitCode == 1)
     let gpr_mismatch ← gpr_mismatch isDarwin o1.gpr o2.gpr
     let nzcv_mismatch ← nzcv_mismatch o1.nzcv o2.nzcv
     let sfp_mismatch  ← sfp_mismatch o1.sfp o2.sfp
     if gpr_mismatch.isEmpty &&
        nzcv_mismatch.isEmpty &&
        sfp_mismatch.isEmpty then
        -- If we are on an Arm-based Apple platform where only the
        -- value of `x18` differs between the model and the machine,
        -- then we don't flag a mismatch. This register is not
        -- expected to be preserved on this platform.
        pure true
     else
       -- TODO: also print the instruction class and sample.
       IO.println s!"ID: {uniqueBaseName}"
       IO.println s!"Instruction: {decode_raw_inst input.inst}"
       IO.println s!"input: {toString input}"
       IO.println s!"Mismatch found: {gpr_mismatch} {nzcv_mismatch} {sfp_mismatch}"
       pure false

/-- Run one random test for the instruction `inst`. -/
def one_test (inst : BitVec 32) (uniqueBaseName : String) : IO Bool := do
  let input      ← input_regState inst
  let machine    ← arm_cosim_test input uniqueBaseName
  let machine_st := machine_to_regState inst machine
  let model      := run 1 (regState_to_armState input)
  let model_st := model_to_regState inst model
  regStates_match uniqueBaseName input machine_st model_st

/--
Make a task for running a single test.
Use a `uniqueBaseName` to create unique files to ensure that tests do not
clobber each other's state.
Return `some t` if a test can be produced, and `none` if not.
- Uses `IO` to try produce a random test that shall be run in a task.
- Returns `.none` if the instruction does not exist on the given architecture.
- Returns `.some task` upon successful creation of the task to randomly test one instruction instance.
-/
def mk_one_test_task (verbose : Bool) (logPrefix : String)
    (fn : IO (Option (BitVec 32))) (uniqueBaseName : String) :
    IO (Option (Task (Except IO.Error Bool))) := do
  let maybe_inst ← fn
  match maybe_inst with
  | .none => return .none
  | .some inst => IO.asTask do
    let ret ← one_test inst uniqueBaseName
    let disasm ← get_disasm uniqueBaseName
    if verbose then
      IO.println s!"{logPrefix}: {disasm}"
    if ret == false then
      throw (IO.userError "Mismatch found!")
      return false
     else
       return true


/-- Test n random instructions, each generated by `fn`. -/
def run_n_tests (verbose : Bool) (logPrefix : String)
    (n : Nat) (fn : IO (Option (BitVec 32)))
    (tasks : Array (Task (Except IO.Error Bool))) :
    IO (Array (Task (Except IO.Error Bool))) := do
  let mut tasks := tasks
  for i in [0:n] do
    let logPrefix := s!"{logPrefix} Sample ({i+1}/{n})"
    if let .some t ← mk_one_test_task verbose logPrefix fn s!"test{(1 + tasks.size)}" then
      tasks := tasks.push t
  return tasks

/-- Run n random tests for each random instruction generator in
`Insts.rand`. -/
def run_all_tests (verbose : Bool) (n : Nat) : IO UInt32 := do
  IO.println s!"Performing conformance testing..."
  let machine_check ←
    IO.Process.output
    { cmd  := "Arm/Insts/Cosim/platform_check.sh",
      args := #["-m"] }
  let mut tasks := #[]
  if machine_check.exitCode == 1 then
    -- We are on an Aarch64 machine.
    -- Insts.rand is a list of functions of each class of instructions
    -- that generate legal, random 32-bit instructions.
    for (i, inst_fn) in Insts.rand.enum do
      let logPrefix := s!"Instruction Class ({i + 1}/{Insts.rand.length})"
      tasks ← run_n_tests verbose logPrefix n inst_fn tasks

    let taskResults ← tasks.mapM (fun t => IO.wait t) -- wait on all tasks
    let mut allSucceeded? := true  -- accumulator of all task results
    for result in taskResults do
      match result with
      | .error e =>
        IO.println s!"[Conformance Testing] Test failed with runtime error:\n '{e}'"
        allSucceeded? := false
      | .ok false =>
        IO.println s!"[Conformance Testing] Test failed with mismatch."
        allSucceeded? := false
      | .ok true => pure ()

    if allSucceeded? then
      IO.println s!"[Conformance Testing] All tests passed!"
      pure 0
    else
      IO.println s!"[Conformance Testing] Some test FAILED."
      pure 1
  else
    IO.println s!"[Conformance Testing] Skipping; Aarch64 host not detected."
    pure 0

end Cosim
