/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

In this file, we define proof automation for separation conditions of memory.

References:
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/OmegaM.lean
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/Frontend.lean
-/
import Arm
import Arm.Memory.MemoryProofs
import Arm.BitVec
import Arm.Memory.Attr
import Lean
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Conv.Basic

/- # Features Wanted List
- `at` syntax for `simp_mem at h₁ h₂ ⊢`.
-/
open Lean Meta Elab Tactic

section Theorems
abbrev Memory := Store (BitVec 64) (BitVec 8)

def read_mem' (addr : BitVec 64) (s : Memory) : BitVec 8 :=
  read_store addr s

@[simp]
theorem read_mem_eq_read_mem' : read_mem addr s = read_mem' addr s.mem := rfl

@[simp]
theorem getLsb_read_mem' : (read_mem' addr s).getLsb i = (s addr).getLsb i := rfl

def read_mem_bytes' (n : Nat) (addr : BitVec 64) (s : Memory) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := read_mem' addr s
    let rest := read_mem_bytes' n' (addr + 1#64) s
    have h: n' * 8 + 8 = (n' + 1) * 8 := by simp_arith
    BitVec.cast h (rest ++ byte)

@[simp]
theorem read_mem_bytes_eq_read_mem_bytes' (s : ArmState) :
    read_mem_bytes n addr s = read_mem_bytes' n addr s.mem := by
  induction n generalizing addr s
  case zero => simp [read_mem_bytes, read_mem_bytes']
  case succ n' ih =>
    simp [read_mem_bytes, read_mem_bytes', ih]


@[simp]
theorem read_mem_bytes'_zero_eq : read_mem_bytes' 0 addr s = 0#0 := rfl

theorem read_mem_bytes'_succ_eq :
  read_mem_bytes' (n' + 1) addr s = ((read_mem_bytes' n' (addr + 1) s) ++ read_mem' addr s).cast (by omega) := rfl

theorem getLsb_read_mem_bytes' {n i : Nat} {addr : BitVec 64} {s : Memory} (hn : n ≤ 2^64) :
    (read_mem_bytes' n addr s).getLsb i =
    (decide (i < n * 8) && (s (addr + BitVec.ofNat 64 (i / 8))).getLsb (i % 8)) := by
  induction n generalizing i addr s
  case zero =>
    simp
  case succ n' ih =>
    simp [read_mem_bytes'_succ_eq]
    rw [Nat.succ_mul]
    by_cases h₁ : (i < 8)
    · simp [h₁]
      simp [show i < n' * 8 + 8 by omega]
      have hdiv : i / 8 = 0 :=  Nat.div_eq_of_lt h₁
      rw [hdiv]
      simp
      have hmod : i % 8 = i := Nat.mod_eq_of_lt h₁
      simp [hmod]
    · simp [h₁]
      rw [ih]
      by_cases h₂ : i - 8 < n' * 8
      · simp [h₂]
        simp [show (i < n' * 8 + 8) by omega]
        have hi' : ∃ i', i = i' + 8 := by
          apply Classical.byContradiction
          intros h
          simp at h
          specialize h (i - 8)
          omega
        obtain ⟨i', hi'⟩ := hi'
        subst hi'
        simp
        congr 2
        rw [BitVec.add_assoc]
        congr
        rw [BitVec.add_def]
        congr 1
        simp
        rw [Nat.mod_eq_of_lt]
        · omega
        · omega
      · simp [h₂]
        intros h₃
        omega
      · omega

/-- info: 'getLsb_read_mem_bytes'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms getLsb_read_mem_bytes'

-- (FIXME) Make write_mem private.
-- We export write_mem_bytes, not write_mem.
def write_mem' (addr : BitVec 64) (val : BitVec 8) (s : Memory) : Memory :=
  write_store addr val s

theorem write_mem'_of_eq (hix : ix = addr) : write_mem' addr val s ix = val := by
  simp only [write_mem']
  subst ix
  apply store_read_over_write_same

theorem write_mem'_of_neq (hix : ix ≠ addr) : write_mem' addr val s ix = s ix := by
  simp only [write_mem']
  apply store_read_over_write_different
  assumption

@[simp]
theorem write_mem_eq_write_mem' :  (write_mem addr val s).mem = write_mem' addr val s.mem := rfl

def write_mem_bytes' (n : Nat) (addr : BitVec 64)
    (val : BitVec (n * 8)) (s : Memory) : Memory :=
  match n with
  | 0 => s
  | n' + 1 =>
    let byte := BitVec.extractLsb 7 0 val
    let s := write_mem' addr byte s
    let val_rest := BitVec.zeroExtend (n' * 8) (val >>> 8)
    write_mem_bytes' n' (addr + 1#64) val_rest s

@[simp]
theorem write_mem_bytes_eq_write_mem_bytes' (s : ArmState) :
    write_mem_bytes n addr val s =
    { s with mem := write_mem_bytes' n addr val s.mem } := by
  induction n generalizing addr s
  case zero => simp [write_mem_bytes, write_mem_bytes']
  case succ n' ih =>
    simp [write_mem_bytes, write_mem_bytes', ih]
    simp [write_mem]

/-- Writing zero bytes does not change memory. -/
theorem write_mem_bytes'_zero : write_mem_bytes' 0 addr val s = s := rfl

/-- Writing (n + 1) bytes can be described as writing `n` bytes and then recursing to write the rest. -/
theorem write_mem_bytes'_succ :
    write_mem_bytes' (n + 1) addr val s =
    let byte := BitVec.extractLsb 7 0 val
    let s := write_mem' addr byte s
    let val_rest := BitVec.zeroExtend (n * 8) (val >>> 8) -- TODO: rewrite this as 'truncate'.
    write_mem_bytes' n (addr + 1#64) val_rest s := rfl

theorem write_mem_bytes'_eq_of_le {ix base : BitVec 64}
    (hix : ix.toNat < base.toNat) (hnowrap : base.toNat + n ≤ 2^64) :
    write_mem_bytes' n base data mem ix = mem ix := by
  induction n generalizing base mem ix
  case zero => simp [write_mem_bytes']
  case succ n ih =>
    simp [write_mem_bytes']
    rcases n with rfl | n
    · rw [write_mem_bytes'_zero]
      apply write_mem'_of_neq (BitVec.neq_of_lt hix)
    · rw [ih]
      · apply write_mem'_of_neq (BitVec.neq_of_lt hix)
      · rw [BitVec.toNat_add_eq_toNat_add_toNat]
        · omega
        · simp
          omega
      · rw [BitVec.toNat_add_eq_toNat_add_toNat (by simp; omega)]
        simp; omega

theorem write_mem_bytes'_eq_of_ge {ix base : BitVec 64}
    (hix : ix.toNat ≥ base.toNat + n)
    (hnowrap : base.toNat + n ≤ 2^64) :
    write_mem_bytes' n base data mem ix = mem ix := by
  induction n generalizing base mem ix
  case zero => simp [write_mem_bytes']
  case succ n ih =>
    simp [write_mem_bytes']
    rw [ih]
    · have hix : ix.toNat > base.toNat := by omega
      obtain hix : ix.toNat ≠ base.toNat := by omega
      apply write_mem'_of_neq (by apply BitVec.neq_of_toNat_neq hix)
    · rw [BitVec.toNat_add_eq_toNat_add_toNat (by simp; omega)]
      simp; omega
    · rw [BitVec.toNat_add_eq_toNat_add_toNat (by simp; omega)]
      simp; omega

theorem extractLsB_zeroExtend_shiftLeft (data : BitVec ((n + 1) * 8)) (hi : i > 0):
    (BitVec.zeroExtend (n * 8) (data >>> 8)).extractLsB (i - 1) = data.extractLsB i := by
  rcases i with rfl | i
  · simp at hi
  · apply BitVec.eq_of_getLsb_eq
    intros j
    simp
    by_cases hj : (j : Nat) ≤ 7
    · simp [hj]
      by_cases hi' : i * 8 + ↑j < n * 8
      · simp [hi']
        simp at hi' ⊢
        congr 1
        omega
      · by_cases hi' : i * 8 + ↑j < n * 8
        · simp [hi']
          congr 1
          rw [Nat.add_mul]
          omega
        · simp [hi']
          apply BitVec.getLsb_ge
          rw [Nat.add_mul, Nat.add_mul]
          omega
    · simp [hj]

/--
The byte at location `ix` in memory, such that `base ≤ ix ≤ base + ix` will be the `ix - base` byte of data.
-/
theorem write_mem_bytes'_eq_extractLsB {ix base : BitVec 64}
  (lo : ix.toNat ≥ base.toNat)
  (hi : ix.toNat < base.toNat + n) (hnowrap : base.toNat + n ≤ 2^64) :
    write_mem_bytes' n base data mem ix = data.extractLsB (ix - base).toNat := by
  induction n generalizing base mem ix
  case zero => omega
  case succ n ih =>
    simp only [write_mem_bytes']
    by_cases hix : ix.toNat = base.toNat
    · obtain hix : ix = base := by
        apply BitVec.eq_of_toNat_eq hix
      subst hix
      simp
      rcases n with rfl | n
      · simp [write_mem_bytes'_zero]
        rw [write_mem'_of_eq rfl]
        rfl
      · rw [write_mem_bytes'_eq_of_le]
        · simp [write_mem'_of_eq rfl, BitVec.extractLsB_def]
        · rw [BitVec.toNat_add_eq_toNat_add_toNat]
          · simp
          · simp; omega
        · rw [BitVec.toNat_add_eq_toNat_add_toNat (by simp; omega)]
          simp
          omega
    · rw [ih]
      -- | TODO: make these into some kind of proof automation.
      · have h_base_plus_1 : (base + 1#64).toNat = base.toNat + 1 := by
          simp [BitVec.toNat_add_eq_toNat_add_toNat]
          rw [Nat.mod_eq_of_lt]
          omega
        have h_ix_sub_base_plus_1 : (ix - (base + 1#64)).toNat = ix.toNat - (base + 1#64).toNat := by
          rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le]
          simp [BitVec.le_def]
          omega
        have h_ix_sub_base : (ix - base).toNat = ix.toNat - base.toNat := by
          rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le]
          rw [BitVec.le_def]
          omega
        rw [h_ix_sub_base_plus_1, h_base_plus_1, h_ix_sub_base]
        rw [Nat.sub_add_eq]
        rw [show ix.toNat - base.toNat - 1 = (ix.toNat - base.toNat) - 1 by omega]
        apply extractLsB_zeroExtend_shiftLeft
        omega
      · rw [BitVec.toNat_add_eq_toNat_add_toNat (by simp; omega)]
        simp;
        omega
      · rw [BitVec.toNat_add_eq_toNat_add_toNat (by simp; omega)]
        simp; omega
      · rw [BitVec.toNat_add_eq_toNat_add_toNat (by simp; omega)]
        simp; omega

/-- info: 'write_mem_bytes'_eq_extractLsB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms write_mem_bytes'_eq_extractLsB

theorem write_mem_bytes'_eq (hoverflow : base.toNat + n ≤ 2 ^ 64) :
  ((write_mem_bytes' n base data mem) ix) =
    if ix < base
    then mem ix
    else if ix.toNat ≥ base.toNat + n then mem ix
    else data.extractLsB (ix - base).toNat := by
  by_cases h : ix < base
  · simp only [h, ↓reduceIte]
    apply write_mem_bytes'_eq_of_le h hoverflow
  · simp only [h, ↓reduceIte]
    by_cases h₂ : ix.toNat ≥ base.toNat + n
    · simp [h₂]
      apply write_mem_bytes'_eq_of_ge h₂ hoverflow
    · simp only [ge_iff_le, h₂, ↓reduceIte]
      apply write_mem_bytes'_eq_extractLsB
      · simp at h
        rw [BitVec.le_def] at h
        omega
      · omega
      · omega

theorem getLsb_write_mem_bytes' (hoverflow : base.toNat + n ≤ 2 ^ 64) :
  ((write_mem_bytes' n base data mem) ix).getLsb i =
  if ix < base
  then (mem ix).getLsb i
  else if ix.toNat ≥ base.toNat + n then (mem ix).getLsb i
  else (data.extractLsB (ix - base).toNat).getLsb i := by
rw [write_mem_bytes'_eq hoverflow]
by_cases h : ix < base
· simp [h]
· simp [h]
  by_cases h₂ : base.toNat + n ≤ ix.toNat
  · simp [h₂]
  · simp [h₂]

/- value of read_mem_bytes when separate. -/
theorem read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate'
  (hsep : mem_separate' x xn y yn) -- separation
  (val : BitVec (yn * 8)) :
    read_mem_bytes xn x (write_mem_bytes yn y val state) =
    read_mem_bytes xn x state := by
  simp only [Nat.reduceMul, write_mem_bytes_eq_write_mem_bytes', read_mem_bytes_eq_read_mem_bytes',
  Nat.reduceAdd, BitVec.ofNat_eq_ofNat, read_mem_bytes'_zero_eq,
  BitVec.cast_eq]
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain ⟨hsrc, hdest, hsplit⟩ := hsep
  rw [getLsb_read_mem_bytes']
  rw [getLsb_write_mem_bytes']
  rw [getLsb_read_mem_bytes']
  simp only [i.isLt]
  simp only [decide_True, ite_eq_left_iff, Bool.true_and]
  intros h₁
  intros h₂
  -- we need to make use of mem_separate to show that src_addr + i / 8 < dest_addr | src_addr + i/7 ≥ dest_addr + 16
  exfalso
  · rcases hsplit with this | this
    · simp [BitVec.le_def] at h₁
      omega
    · have hcontra_h2 : x.toNat + 16 < y.toNat + 16 := by
        simp at this
        have hi : (i : Nat) / 8 < xn := by
          apply Nat.div_lt_of_lt_mul
          simp [Nat.mul_comm]
        rw [BitVec.toNat_add_eq_toNat_add_toNat] at h₂
        · omega
        · have := mem_legal'_def hsrc
          apply Nat.lt_of_lt_of_le _ this
          apply Nat.add_lt_add_iff_left.mpr
          simp
          rw [Nat.mod_eq_of_lt]
          omega
          omega
      omega
  · have := hsrc.size_le_two_pow
    omega
  · have := mem_legal'_def hdest
    omega
  · have := hsrc.size_le_two_pow
    omega

/- value of `read_mem_bytes'` when subset. -/
/-
theorem read_mem_bytes_write_mem_bytes_eq_extract_LsB_of_mem_subset
  (hsep : mem_subset' x xn y yn) -- subset relation.
  (val : BitVec (yn * 8)) :
    read_mem_bytes' xn x (write_mem_bytes' yn y val state) =
      val.extractLsBs (y.toNat - x.toNat) xn := by
  apply BitVec.eq_of_getLsb_eq
  intros i
  obtain ⟨hx, hy, hstart, hend⟩ := hsep
  rw [getLsb_read_mem_bytes' hx.size_le_two_pow]
  rw [getLsb_write_mem_bytes' hy]
  rw [BitVec.getLsb_extractLsB]
  rw [BitVec.getLsb_extractLsBs]
  by_cases hxn : xn = 0
  · subst hxn
    exfalso
    have h := i.isLt
    simp at h
  · simp only [show (0 < xn) by omega]
    simp only [show ((y.toNat - x.toNat) * 8 + xn * 8 - 1 - (y.toNat - x.toNat) * 8) = xn * 8 - 1 by omega]
    by_cases h₁ : ↑i < xn * 8
    · simp only [h₁]
      simp only [show (i ≤ xn * 8 - 1) by omega]
      simp only [decide_True, Bool.true_and]
      -- TODO: change defn of mem_legal' to use `xn * 8`.
      sorry
    · simp [h₁]
      intros h
      apply BitVec.getLsb_ge
      omega
-/

end Theorems


namespace SeparateAutomation

structure SimpMemConfig where

/-- Context for the `SimpMemM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `simp_mem`. -/
  cfg : SimpMemConfig

def Context.init (cfg : SimpMemConfig) : Context where
  cfg := cfg

inductive Hypothesis
| separate (h : Expr) (a na b nb : Expr)
| subset (h : Expr)

def Hypothesis.expr : Hypothesis → Expr
| .separate h .. => h
| .subset h .. => h

instance : ToMessageData Hypothesis where
  toMessageData
  | .subset h => toMessageData h
  | .separate h _a _na _b _nb => toMessageData h

/-- The internal state for the `SimpMemM` monad, recording previously encountered atoms. -/
structure State where
  hypotheses : Array Hypothesis := #[]

def State.init : State := {}

abbrev SimpMemM := StateRefT State (ReaderT Context TacticM)

def SimpMemM.run (m : SimpMemM α) (cfg : SimpMemConfig) : TacticM α :=
  m.run' State.init |>.run (Context.init cfg)

/-- Add a `Hypothesis` to our hypothesis cache. -/
def SimpMemM.addHypothesis (h : Hypothesis) : SimpMemM Unit :=
  modify fun s => { s with hypotheses := s.hypotheses.push h }

def processingEmoji : String := "⚙️"

/-- Match an expression `h` to see if it's a useful hypothesis. -/
def processHypothesis (h : Expr) : MetaM (Option Hypothesis) := do
  -- trace[simp_mem] "processing hyp '{(← inferType h)}'"
  let ht ← inferType h
  trace[simp_mem.info] "{processingEmoji} Processing '{h}' : '{toString ht}'"
  match_expr ht with
  | mem_separate' a ha b hb => return .some (.separate h a ha b hb)
  | _ => return .none

/--
info: read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate' {x : BitVec 64} {xn : Nat} {y : BitVec 64} {yn : Nat}
  {state : ArmState} (hsep : mem_separate' x xn y yn) (val : BitVec (yn * 8)) :
  read_mem_bytes xn x (write_mem_bytes yn y val state) = read_mem_bytes xn x state
-/
#guard_msgs in #check read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate'

partial def SimpMemM.rewrite (g : MVarId) : SimpMemM Unit := do
  trace[simp_mem.info] "{processingEmoji} Matching on ⊢ {← g.getType}"
  let some (_, lhs, rhs) ← matchEq? (← g.getType) | throwError "invalid goal, expected 'lhs = rhs'."
  -- TODO: do this till fixpoint.
  for h in (← get).hypotheses do
    let x ← mkFreshExprMVar .none
    let xn ← mkFreshExprMVar .none
    let y ← mkFreshExprMVar .none
    let yn ← mkFreshExprMVar .none
    let state ← mkFreshExprMVar .none
    let f := (Expr.const ``read_mem_bytes_write_mem_bytes_eq_read_mem_bytes_of_mem_separate' [])
    let result : Option RewriteResult ←
      try
        pure <| some (← g.rewrite (← g.getType) (mkAppN f #[x, xn, y, yn, state, h.expr]) false)
      catch _ =>
        pure <| none
    match result with
    | .none =>
      trace[simp_mem.info] "{crossEmoji} rewrite did not fire"
    | .some r =>
      let mvarId' ← g.replaceTargetEq r.eNew r.eqProof
      -- | TODO: dispatch other goals that occur proof automation.
      Tactic.setGoals <| mvarId' :: r.mvarIds

def SimpMemM.analyzeLoop : SimpMemM Unit := do
    (← getMainGoal).withContext do
      let hyps := (← getLocalHyps)
      trace[simp_mem] "analyzing {hyps.size} hypotheses:\n{← hyps.mapM (liftMetaM ∘ inferType)}"
      for h in hyps do
        if let some hyp ← processHypothesis h then
          trace[simp_mem.info] "{checkEmoji} Found '{h}'"
          SimpMemM.addHypothesis hyp
        else
          trace[simp_mem.info] "{crossEmoji} Rejecting '{h}'"
      SimpMemM.rewrite (← getMainGoal)

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def simpMem (cfg : SimpMemConfig := {}) : TacticM Unit :=
  SimpMemM.run SimpMemM.analyzeLoop cfg


/-- The `simp_mem` tactic, for simplifying away statements about memory. -/
def simpMemTactic (cfg : SimpMemConfig) : TacticM Unit := simpMem cfg

end SeparateAutomation

/--
Allow elaboration of `SimpMemConfig` arguments to tactics.
-/
declare_config_elab elabSimpMemConfig SeparateAutomation.SimpMemConfig


/--
Implement the simp_mem tactic frontend.
-/
elab "simp_mem" : tactic => do
  SeparateAutomation.simpMemTactic {}

-- def evalSimpMem : Tactic := fun
--   | `(tactic| simp_mem $[$cfg]?) => do
--     let cfg ← elabSimpMemConfig (mkOptionalNode cfg)
--     SeparateAutomation.simpMemTactic cfg
--   | _ => throwUnsupportedSyntax
