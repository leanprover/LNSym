/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

-- Some utilities for debugging concrete simulations

import Arm.Exec

section Debug

open BitVec

/-- `trace_run`: Print `(debug s)` before simulating each instruction. -/
def trace_run (debug : ArmState → String) (n : Nat) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 =>
    dbg_trace (debug s)
    let s' := stepi s
    trace_run debug n' s'

/-- `log_run`: Log `(debug s)` to a file `filename` before
     simulating each instruction. Note that we append to file, so
     any old contents are not overwritten. -/
def log_run (filename : System.FilePath) (debug : ArmState → String)
  (n : Nat) (s : ArmState) : IO ArmState := do
  let h ← IO.FS.Handle.mk filename IO.FS.Mode.append
  h.putStrLn (debug s)
  match n with
  | 0 => pure s
  | n' + 1 =>
    let s' := stepi s
    log_run filename debug n' s'

/-- `run_until`: Run until `cond` is true or `n` instructions are simulated,
  whichever comes first. -/
def run_until (cond : ArmState → Bool) (n : Nat) (s : ArmState) : ArmState :=
  match n with
  | 0 => s
  | n' + 1 =>
    if (cond s) then
      dbg_trace "Stopping condition reached!"
      s
    else
      let s' := stepi s
      run_until cond n' s'

-- Examples of debug functions for use in `trace_run` and `log_run`:

/-- `pc_trace`: Unconditionally trace the program counter. -/
def pc_trace (s : ArmState) : String :=
  "pc: " ++ (read_pc s).toHex

/-- `non_zero_x2_trace`: Trace the program counter if x2 != 0#64. -/
def non_zero_x2_trace (s : ArmState) : String :=
  if (read_gpr 64 2 s) != 0#64 then
    "pc: " ++ (read_pc s).toHex ++ ": x2 != 0"
  else
    ""

end Debug
