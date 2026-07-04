/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Lake
open Lake DSL

package «lnsym» where
  -- (v4.30) v4.30 promotes the `unusedSimpArgs` linter from firing only inside
  -- `#guard_msgs` (its v4.22 scope) to firing across ALL library code: ~264 sites in
  -- 16 files, almost all in `simp only [...]` lists inside proofs the port keeps
  -- byte-identical to upstream `main`. No `#guard_msgs` test expects an
  -- `unusedSimpArgs` warning, so silencing the linter package-wide is test-safe and
  -- keeps every proof body identical to `main` (the alternative — deleting 264
  -- "redundant" args — would diverge LNSym from upstream for no behavioural gain).
  -- Per-block silencers remain in CSE.lean/Sym.lean for their `#guard_msgs` captures.
  leanOptions := #[⟨`linter.unusedSimpArgs, false⟩]

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

-- TEMPORARY (toolchain-stepping only): both external git deps are detached while
-- stepping through intermediate Lean versions; reattach at pinned, compatible revs
-- at the final version step.
--
-- `ELFSage` has no Lean v4.14-compatible revision: its history sat at
-- nightly-2024-10-07 (`main` head `18c69c9`) and then jumped toward modern Lean, so
-- there is no rev that compiles under v4.14 (`ELFSage/Util/ByteArray` and its `Cli`
-- dep both fail). ELFSage is used only by `Tests/ELFParser/*` (via
-- `import ELFSage`); LNSym's own libraries and the `lnsym` exe never import it. We
-- therefore detach it and exclude only the `ELFParser` import from `Tests/Tests.lean`
-- (see the note there) so the rest of `Tests` stays green.
--
-- `doc-gen4` is only needed by `Doc.lean`, which is not part of `make all`
-- (specs/correctness/proofs/tests/cosim) nor the per-version done-list. Its
-- transitive deps (UnicodeBasic/MD4Lean/BibtexQuery) float on `@main`/`@master` and
-- their lakefiles fail to elaborate under intermediate Lean versions; since Lake
-- configures every package before building anything, leaving it attached would
-- block even `lake build Arm`.
-- require ELFSage from git "https://github.com/draperlaboratory/ELFSage.git" @ "main"
-- require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
