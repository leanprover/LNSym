import Lake
open Lake DSL

package «lnsym» where
  -- add package configuration options here

lean_lib «Arm» where
  -- add library configuration options here

lean_lib «Specs» where
  -- add library configuration options here

lean_lib «Tests» where
  -- add library configuration options here

lean_lib «Proofs» where
  -- add library configuration options here

lean_lib «Tactics» where
  -- add library configuration options here

@[default_target]
lean_exe «lnsym» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  -- supportInterpreter := true

require std from git "https://github.com/leanprover/std4" @ "main"
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "main"
