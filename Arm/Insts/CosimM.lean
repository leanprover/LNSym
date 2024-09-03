/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

We define a utility monad for generating random instructions.
This is used for cosimulation testing.
-/

import Std.Tactic.BVDecide
import Arm.BitVec
import Arm.State

namespace Cosim
/-- Information about our current platform. -/
structure Context where private mk ::
  aarch64? : Bool
  darwin? : Bool
  sha3? : Bool
  sha512? : Bool

/--
Monad for cosimulation to run in. This acts as a cache for platform information.
-/
abbrev CosimM := ReaderT Context IO


/-- Run `platform_check.sh` to gather platform details -/
private def getPlatformCheckExitCode (args : Array String) : IO UInt32 := do
  let machine_check ←
    IO.Process.output {
      cmd  := "Arm/Insts/Cosim/platform_check.sh",
      args := args
    }
  return machine_check.exitCode

/-- Make a new Context by reading platform information. -/
def Context.new : IO Context := do
  let darwin? := (← getPlatformCheckExitCode #["-d"]) == 1
  let aarch64? := (← getPlatformCheckExitCode #["-m"]) == 1
  let sha3? := (← getPlatformCheckExitCode #["-f", "sha3"]) == 1
  let sha512? := (← getPlatformCheckExitCode #["-f", "sha512"]) == 1
  return { darwin?, aarch64?, sha3?, sha512? }

def aarch64? : CosimM Bool := do return (← read).aarch64?

def darwin? : CosimM Bool := do return (← read).aarch64?

def sha3? : CosimM Bool := do return (← read).sha3?

def sha512? : CosimM Bool := do return (← read).sha512?

def CosimM.run (m : CosimM α) : IO α := do ReaderT.run m (← Context.new)
end Cosim
