/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
Taken from: https://github.com/leanprover-community/mathlib4/blob/318082b0bccc3abd9d654496f7b60267f277d5fd/Mathlib/Util/Time.lean#L28-L33
-/
import Lean

/-!
# Defines `#time` command.

Time the elaboration of a command, and print the result (in milliseconds).
-/

section
open Lean Elab Command

/--
Time the elaboration of a command, and print the result (in milliseconds).

Example usage:
```
set_option maxRecDepth 100000 in
#time example : (List.range 500).length = 500 := rfl
```
-/
elab "#time " cmd:many1Indent(command) : command => do
  let start ← IO.monoMsNow
  for stx in cmd.raw.getArgs do
    elabCommand stx
  logInfo m!"time: {(← IO.monoMsNow) - start}ms"

end
