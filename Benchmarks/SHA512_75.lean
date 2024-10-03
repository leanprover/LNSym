/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tactics.Sym
import Benchmarks.Command
import Benchmarks.SHA512

open Benchmarks

benchmark sha512_75 : SHA512Bench 75 := fun s0 _ h => by
  intros
  sym_n 75
  simp only [h, bitvec_rules]
  · exact (sorry : Aligned ..)
  done
