/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel

Specializing the Correctness module for use with our specification of
the Arm ISA.
-/

import Arm.Exec
import Correctness.Correctness

namespace Correctness

/-- State machine for the Arm ISA. -/
instance : Sys ArmState where
  some := ArmState.default
  next := stepi

/-- Interpret `Sys.run` as `run` for the Arm state machine. -/
theorem arm_run (n : Nat) (s : ArmState) :
  Sys.run s n = run n s := by
  induction n generalizing s
  case zero => simp only [Sys.run, run]
  case succ =>
    rename_i n h
    simp only [Sys.run, Sys.next, run]
    rw [h]

/-
-- (TODO) Move to Arm/BitVec.lean?
/-- Unexpander to represent bitvector literals in hexadecimal -- this overrides
  the unexpander in the Lean BitVec library. -/
@[app_unexpander BitVec.ofNat] def unexpandBitVecOfNatToHex : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:num $i:num) =>
      let i' := i.getNat
      let n' := n.getNat
      let trimmed_hex := -- Remove leading zeroes...
        String.dropWhile (BitVec.ofNat n' i').toHex
                         (fun c => c = '0')
                         -- ... but keep one if the literal is all zeros.
      let trimmed_hex := if trimmed_hex.isEmpty then "0" else trimmed_hex
      let bv := Lean.Syntax.mkNumLit s!"0x{trimmed_hex}#{n'}"
      `($bv:num)
  | _ => throw ()
-/

end Correctness
