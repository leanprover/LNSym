import Arm.State
import Tactics.Sym
import Tactics.StepThms

/-!
## Sum example program

This file shows a full end-to-end example:
* We define the `sum` program
* We then pre-generate the step-theorems
* And finally proof that `sum` indeed sums four registers
-/

/-- a program that sums registers `x0`, `x1`, `x2` and `x3`,
storing the result in `x0` -/
def sum : Program :=
  def_program [
      (0x4000, 0x8b010000), --     	add	x0, x0, x1
      (0x4004, 0x8b020000), --     	add	x0, x0, x2
      (0x4008, 0x8b030000), --     	add	x0, x0, x3
      (0x400c, 0xd65f03c0) --     	ret
  ]

/- pre-generate theorems -/
#genStepEqTheorems sum

/- prove that `sum` is correct using symbolic simulation -/
example
    (s0 sf : ArmState)
    (h_program : s0.program = sum)
    (h_pc : read_pc s0 = 0x4000)
    (h_err : read_err s0 = .None)
    (h_run : sf = run 4 s0) :
    read_gpr 64 0 sf = read_gpr 64 0 s0 + read_gpr 64 1 s0
                        + read_gpr 64 2 s0 + read_gpr 64 3 s0 := by
  sym_n 4
