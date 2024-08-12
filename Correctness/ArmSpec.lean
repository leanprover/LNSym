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

end Correctness
