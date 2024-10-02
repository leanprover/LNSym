/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Lake
open Lake DSL

package «lnsym» where
  -- add package configuration options here

lean_lib «Arm» where
  -- add library configuration options here

lean_lib «Correctness» where

lean_lib «Specs» where
  -- add library configuration options here

lean_lib «Tests» where
  -- add library configuration options here

lean_lib «AWSLCELFTests» where
  -- add library configuration options here

lean_lib «Proofs» where
  -- add library configuration options here

lean_lib «Tactics» where
  -- add library configuration options here

lean_lib «Doc» where
  -- add library configuration options here

lean_lib «Benchmarks» where
  /- We want `lake build Benchmarks` to build all dependencies needed to run
  benchmarks, but not run the actual benchmarks themselves.
  To ensure we build all dependencies, we build the actual benchmark files,
  but to prevent the benchmarks from running, we set the `benchmark.runs` option
  to `0`.

  Note that regular options (without the `weak` prefix) are checked to exist,
  but not all files will have imported the `benchmark.runs` option, so we have
  to set the option with the `weak` prefix. As a result, the option will be
  silently ignored when compiling files where the option hasn't been defined -/
  leanOptions := #[⟨`weak.benchmark.runs, (0 : Nat)⟩]
  -- add library configuration options here

@[default_target]
lean_exe «lnsym» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  -- supportInterpreter := true

require ELFSage from git "https://github.com/draperlaboratory/ELFSage.git" @ "main"
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
