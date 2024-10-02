/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.Aggregate
import Tactics.StepThms
import Tactics.CSE
import Arm.Memory.SeparateAutomation
import Arm.Syntax

namespace GCMGmultV8Program
open ArmStateNotation

#genStepEqTheorems gcm_gmult_v8_program


set_option trace.simp_mem.info true in
theorem min_repro (s0 : ArmState)
  (h_HTable : Memory.read_bytes 256 100 s0.mem = HTable)
  (h_htableSep : mem_separate' 100 256 500 256) :
  Memory.read_bytes 256 100 (Memory.write_bytes 256 500 (Memory.read_bytes 256 100 s0.mem) s0.mem) = HTable := by
  simp_mem

/-
xxx: GCMGmultV8 Xi HTable
-/

set_option pp.deepTerms false in
set_option pp.deepTerms.threshold 50 in
set_option trace.simp_mem.info true in
theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_Xi : Xi = s0[read_gpr 64 0#5 s0, 16])
    (h_HTable : HTable = s0[read_gpr 64 1#5 s0, 256])
    (h_mem_sep : Memory.Region.pairwiseSeparate
                 [(read_gpr 64 0#5 s0, 16),
                  (read_gpr 64 1#5 s0, 256)])
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    -- The final state is error-free.
    read_err sf = .None ∧
    -- The program is unmodified in `sf`.
    sf.program = gcm_gmult_v8_program ∧
    -- The stack pointer is still aligned in `sf`.
    CheckSPAlignment sf ∧
    -- The final state returns to the address in register `x30` in `s0`.
    read_pc sf = r (StateField.GPR 30#5) s0 ∧
    -- HTable is unmodified.
    sf[read_gpr 64 1#5 s0, 256] = HTable ∧
    -- Frame conditions.
    -- Note that the following also covers that the Xi address in .GPR 0
    -- is unmodified.
    REGS_UNCHANGED_EXCEPT [.SFP 0, .SFP 1, .SFP 2, .SFP 3,
                           .SFP 17, .SFP 18, .SFP 19, .SFP 20,
                           .SFP 21, .PC]
                          (sf, s0) ∧
    -- Memory frame condition.
    MEM_UNCHANGED_EXCEPT [(r (.GPR 0) s0, 128)] (sf, s0) := by
  simp_all only [state_simp_rules, -h_run] -- prelude
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 27
  -- Epilogue
  simp only [←Memory.mem_eq_iff_read_mem_bytes_eq] at *
  simp only [memory_rules] at *
  sym_aggregate
  -- Split conjunction
  repeat' apply And.intro
  · -- Aggregate the memory (non)effects.
    -- (FIXME) This will be tackled by `sym_aggregate` when `sym_n` and `simp_mem`
    -- are merged.
    simp only [*]
    clear h_HTable
    simp_mem; rfl
    /-
    (FIXME @bollu) `simp_mem; rfl` creates a malformed proof here. The tactic produces
    no goals, but we get the following error message:

    application type mismatch
    Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset'
      (Eq.mp (congrArg (Eq HTable) (Memory.State.read_mem_bytes_eq_mem_read_bytes s0))
        (Eq.mp (congrArg (fun x => HTable = read_mem_bytes 256 x s0) zeroExtend_eq_of_r_gpr) h_HTable))
    argument has type
      HTable = Memory.read_bytes 256 (r (StateField.GPR 1#5) s0) s0.mem
    but function has type
      Memory.read_bytes 256 (r (StateField.GPR 1#5) s0) s0.mem = HTable →
      mem_subset' (r (StateField.GPR 1#5) s0) 256 (r (StateField.GPR 1#5) s0) 256 →
        Memory.read_bytes 256 (r (StateField.GPR 1#5) s0) s0.mem =
          HTable.extractLsBytes (BitVec.toNat (r (StateField.GPR 1#5) s0) - BitVec.toNat (r (StateField.GPR 1#5) s0)) 256

    simp_mem; rfl
    -/
    -- rw [Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate']
    -- simp_mem
  · simp only [List.mem_cons, List.mem_singleton, not_or, and_imp]
    sym_aggregate
  · intro n addr h_separate
    simp_mem (config := { useOmegaToClose := false })
    -- Aggregate the memory (non)effects.
    simp only [*]
  done

def consumeRewriteFuel : Id Unit := ()
def outofRewriteFuel? : Id Bool := false

def someVal : Option Bool := some true
def noneVal : Option Bool := none

def someMonadicVal (arg : Bool) : Id (Option Bool) := some true

def ReadBytesExpr.ofExpr? (e : Expr) : Option Expr := none
def WriteBytesExpr.ofExpr? (e : Expr) : Option Expr := none
open Lean in
partial def foo (e : Expr) (hyps : Array Int) : Id Bool := do
  consumeRewriteFuel
  if ← outofRewriteFuel? then
    return false

  -- if e.isSort then
  --   return false

  if let .some er := someVal then
    if let .some ew := someVal then

      -- let separate := MemSeparateProp.mk er.span ew.span
      -- let subset := MemSubsetProp.mk er.span ew.span
      -- if let .some separateProof ← proveWithOmega? separate hyps then do
      if let .some separateProof ← someMonadicVal ew then do
        dbg_trace "{checkEmoji} separate {separateProof}"
        return true
      else
        dbg_trace "{crossEmoji} separate"
        if let .some subsetProof ← someMonadicVal ew then do
          dbg_trace "{checkEmoji} subset {subsetProof}"
          return true
        else
          dbg_trace "{crossEmoji} subset"
          dbg_trace "{crossEmoji} Could not prove er ⟂/⊆ ew"
          return false
    else do
      dbg_trace "{crossEmoji} found no read of write, searching for overlapping read in hyp."
      -- TODO: we don't need a separate `subset` branch for the writes: instead, for the write,
      -- we can add the theorem that `(write region).read = write val`.
      -- Then this generic theory will take care of it.
      -- let changedInCurrentIter? ← withTraceNode m!"Searching for overlapping read {er.span}." do
      --   let mut changedInCurrentIter? := false
      --   for hyp in hyps do
      --     if let Hypothesis.read_eq hReadEq := hyp then do
      --       changedInCurrentIter? := changedInCurrentIter? ||
      --         (← withTraceNode m!"{processingEmoji} ... ⊆ {hReadEq.read.span} ? " do
      --           -- the read we are analyzing should be a subset of the hypothesis
      --           let subset := (MemSubsetProp.mk er.span hReadEq.read.span)
      --           if let some hSubsetProof ← proveWithOmega? subset hyps then
      --             trace[simp_mem.info] "{checkEmoji}  ... ⊆ {hReadEq.read.span}"
      --             rewriteReadOfSubsetRead er hReadEq hSubsetProof
      --             pure true
      --           else
      --             trace[simp_mem.info] "{crossEmoji}  ... ⊊ {hReadEq.read.span}"
      --             pure false)
      --   pure changedInCurrentIter?
      -- return changedInCurrentIter?
      return true
  else
    return false
    -- if e.isForall then
    --   Lean.Meta.forallTelescope e fun xs b => do
    --     let mut changedInCurrentIter? := false
    --     for x in xs do
    --       changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr x hyps)
    --       -- we may have a hypothesis like
    --       -- ∀ (x : read_mem (read_mem_bytes ...) ... = out).
    --       -- we want to simplify the *type* of x.
    --       changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr (← inferType x) hyps)
    --     changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr b hyps)
    --     return changedInCurrentIter?
    -- else if e.isLambda then
    --   Lean.Meta.lambdaTelescope e fun xs b => do
    --     let mut changedInCurrentIter? := false
    --     for x in xs do
    --       changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr x hyps)
    --       changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr (← inferType x) hyps)
    --     changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr b hyps)
    --     return changedInCurrentIter?
    -- else
    --   -- check if we have expressions.
    --   match e with
    --   | .app f x =>
    --     let mut changedInCurrentIter? := false
    --     changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr f hyps)
    --     changedInCurrentIter? := changedInCurrentIter? || (← SimpMemM.simplifyExpr x hyps)
    --     return changedInCurrentIter?
    --   | _ => return false

open Lean in
#eval foo (mkConst `foo) #[]
