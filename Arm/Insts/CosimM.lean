/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

We define a utility monad for generating random instructions.
This is used for cosimulation testing.
-/

import LeanSAT
import Arm.BitVec
import Arm.State

namespace Cosim
/-- Information about our current platform. -/
structure Context where private mk ::
  aarch64? : Bool
  darwin? : Bool

/--
Monad for cosimulation to run in. This acts as a cache for platform information.
-/
abbrev CosimM := ReaderT Context IO


/-- Run `platform_check.sh` to gather platform details -/
private def getPlatformCheckExitCode (arg : String) : IO UInt32 := do
  let machine_check ←
    IO.Process.output {
      cmd  := "Arm/Insts/Cosim/platform_check.sh",
      args := #[arg]
    }
  return machine_check.exitCode

/-- Make a new Context by reading platform information. -/
def Context.new : IO Context := do
  let darwin? := (← getPlatformCheckExitCode "-d") == 1
  let aarch64? := (← getPlatformCheckExitCode "-m") == 1
  return { darwin? := darwin?, aarch64? := aarch64? }

def aarch64? : CosimM Bool := do return (← read).aarch64?

def darwin? : CosimM Bool := do return (← read).aarch64?

def CosimM.run (m : CosimM α) : IO α := do ReaderT.run m (← Context.new)
end Cosim
