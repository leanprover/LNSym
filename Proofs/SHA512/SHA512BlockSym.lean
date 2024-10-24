/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Proofs.SHA512.SHA512LoopBlocks
import Tactics.SymBlock

open BitVec

namespace SHA512

#time
-- set_option trace.Tactic.sym.info true in
-- set_option trace.Tactic.sym true in
set_option pp.maxSteps 100 in
theorem sha512_loop_sym {s0 sf : ArmState}
  (h_program : s0.program = program)
  (h_pc : r StateField.PC s0 = 0x126500#64)
  (h_err : r StateField.ERR s0 = StateError.None)
  (h_run : sf = run 485 s0) :
  r .ERR sf = .None ∧
  r .PC sf = (if ¬r (StateField.GPR 0x2#5) s0 - 0x1#64 = 0x0#64 then 0x126500#64 else 0x126c94#64) := by
  sym_block 485 (block_size := 20) -- ceiling|485/20| blocks
  done
