/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

In this file, we define the simp_mem tactic which simplifies expressions by discharging
memory (non-)interference side conditions.

References:
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/OmegaM.lean
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/Frontend.lean
-/
import Arm
import Arm.Memory.MemoryProofs
import Arm.BitVec
import Arm.Memory.Attr
import Arm.Memory.AddressNormalization
import Lean
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Conv.Basic
import Tactics.Simp
import Tactics.BvOmegaBench
import Arm.Memory.Common
import Arm.Memory.MemOmega
import Lean.Elab.Tactic.Location
import Init.Tactics

open Lean Meta Elab Tactic Memory

/-! ## Memory Separation Automation

##### A Note on Notation

- `[a..an)`: a range of memory starting with base address `a` of length `an`.
  aka `mem_legal' a an`.
- `[a..an) ⟂ [b..bn)`: `mem_disjoint' a an b bn`.
- `[a..an] ⊆ [b..bn)`: `mem_subset' a an b bn`

##### Tactic Loop

The core tactic tries to simplify expressions of the form:
`mem.write_bytes [b..bn) val |>. read_bytes [a..an)`
by case splitting:

1. If `[a..an) ⟂ [b..bn)`, the write does not alias the read,
  and can be replaced with ` mem.read_bytes [a..an) `
2. If `[a..an] ⊆ [b..bn)`, the write aliases the read, and can be replaced with
  `val.extractLsBs adjust([a..an), [b..bn))`. Here, `adjust` is a function that
  adjusts the read indices `[a..an)` with respect to the write indices `[b..bn)`,
  to convert a read from `mem` into a read from `val`.

The tactic shall be implemented as follows:
1. Search the goal state for `mem.write_bytes [b..bn) val |>.read_bytes [a..an)`.
2. Try to prove that either `[a..an) ⟂ [b..bn)`, or `[a..an) ⊆ [b..bn)`.
    2a. First search the local context for assumptions of this type.
    2b. Try to deduce `[a..an) ⟂ [b..bn)` from the fact that
        subsets of disjoint sets are disjoint.
        So try to find `[a'..an')`, `[b'...bn')` such that:
          (i) `[a..an) ⊆ [a'..an')`.
          (ii) `[b..bn) ⊆ [b'..bn')`.
          (iii) and `[a'..an') ⟂ [b'...bn')`.
    2b. Try to deduce `[a..an) ⊆ [b..bn)` from transitivity of subset.
        So try to find `[c..cn)` such that:
        (i) `[a..an) ⊆ [c..cn)`
        (ii) `[c..cn) ⊆ [b..bn)`
    2c. If this also fails, then reduce all hypotheses to
        linear integer arithmetic, and try to invoke `omega` to prove either
        `[a..an) ⟂ [b..bn)` or `[a..an) ⊆ [b..bn)`.
3. Given a proof of either `[a..an) ⟂ [b..bn)` or `[a..an) ⊆ [b..bn)`,
  simplify using the appropriate lemma from `Mem/Separate.lean`.
4. If we manage to prove *both* `[a..an) ⟂ [b..bn)` *and* `[a..an) ⊆ [b..bn)`,
   declare victory as this is a contradiction. This may look useless,
   but feels like it maybe useful to prove certain memory states as impossible.

##### Usability

- If no mem separate/subset assumptions are present,
  then throw an error to tell the user that we expect them to
  specify such assumptions for all memory regions of interest.
  LNSym doesn't support automated verification of programs that
  do dynamic memory allocation.

-  If any non-primed separate/subset assumptions are detected,
  error out to tell the user that no automation is supported in this case.

##### Future Work

- Add support for disjoint constraints amongst $n$ memory regions.
  This will perform proof search for `List.pairwise ⟂ mems`.
- Create a new concept, `MemRegion`, which we currently call `MemSpan`.
-/

section BvOmega

/- We tag `mem_legal'` as `bv_toNat` here, since we want to actually lazily unfold this.
Doing it here lets us remove it from `bv_toNat` simp-set as a change to `SeparateAutomation.lean`,
without needing us to modify the core definitions file which incurs a recompile cost,
making experimentation annoying.
-/
attribute [bv_toNat] mem_legal'

end BvOmega

namespace SeparateAutomation

structure SimpMemConfig where
  /-- number of times rewrites must be performed. -/
  rewriteFuel : Nat := 1000
  /-- whether an error should be thrown if the tactic makes no progress. -/
  failIfUnchanged : Bool := true

/-- Context for the `SimpMemM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `simp_mem`. -/
  cfg : SimpMemConfig
  /-- Cache of `bv_toNat` simp context. -/
  bvToNatSimpCtx : Simp.Context
  /-- Cache of `bv_toNat` simprocs. -/
  bvToNatSimprocs : Array Simp.Simprocs

def Context.init (cfg : SimpMemConfig) : MetaM Context := do
  let (bvToNatSimpCtx, bvToNatSimprocs) ←
    LNSymSimpContext
      (config := {failIfUnchanged := false})
      (simp_attrs := #[`bv_toNat])
      (useDefaultSimprocs := false)
  return {cfg, bvToNatSimpCtx, bvToNatSimprocs}

/-- The internal state for the `SimpMemM` monad, recording previously encountered atoms. -/
structure State where
  hypotheses : Array Memory.Hypothesis := #[]
  rewriteFuel : Nat
  changed : Bool

def State.init (cfg : SimpMemConfig) : State :=
  { rewriteFuel := cfg.rewriteFuel, changed := false }

abbrev SimpMemM := StateRefT State (ReaderT Context TacticM)

def SimpMemM.run (m : SimpMemM α) (cfg : SimpMemConfig) : TacticM α := do
  m.run' (State.init cfg) |>.run (← Context.init cfg)

/-- Add a `Hypothesis` to our hypothesis cache. -/
def SimpMemM.addHypothesis (h : Memory.Hypothesis) : SimpMemM Unit :=
  modify fun s => { s with hypotheses := s.hypotheses.push h }

def SimpMemM.withMainContext (ma : SimpMemM α) : SimpMemM α := do
  (← getMainGoal).withContext ma

def SimpMemM.withContext (g : MVarId) (ma : SimpMemM α) : SimpMemM α := do
  g.withContext ma

/-- create a trace node in trace class (i.e. `set_option traceClass true`),
with header `header`, whose default collapsed state is `collapsed`. -/
def SimpMemM.withTraceNode (header : MessageData) (k : SimpMemM α)
    (collapsed : Bool := true)
    (traceClass : Name := `simp_mem.info) : SimpMemM α :=
  Lean.withTraceNode traceClass (fun _ => return header) k (collapsed := collapsed)

/-- Get the cached simp context for bv_toNat -/
def SimpMemM.getBvToNatSimpCtx : SimpMemM Simp.Context := do
  return (← read).bvToNatSimpCtx

/-- Get the cached simpprocs for bv_toNat -/
def SimpMemM.getBvToNatSimprocs : SimpMemM (Array Simp.Simprocs) := do
  return (← read).bvToNatSimprocs

def processingEmoji : String := "⚙️"

def consumeRewriteFuel : SimpMemM Unit :=
  modify fun s => { s with rewriteFuel := s.rewriteFuel - 1 }

def setChanged : SimpMemM Unit := modify fun s => { s with changed := true }

def resetChanged : SimpMemM Unit := modify fun s => { s with changed := false }

def outofRewriteFuel? : SimpMemM Bool := do
  return (← get).rewriteFuel == 0

/-- Create a trace note that folds `header` with `(NOTE: can be large)`,
and prints `msg` under such a trace node.
-/
def SimpMemM.traceLargeMsg (header : MessageData) (msg : MessageData) : SimpMemM Unit :=
    withTraceNode m!"{header} (NOTE: can be large)" do
      trace[simp_mem.info] msg

def getConfig : SimpMemM SimpMemConfig := do
  let ctx ← read
  return ctx.cfg

/-- info: state_value (fld : StateField) : Type -/
#guard_msgs in #check state_value


def SimpMemM.findOverlappingReadHypAux (hyps : Array Memory.Hypothesis) (er : ReadBytesExpr)  (hReadEq : ReadBytesEqProof) :
    SimpMemM <| Option (MemSubsetProof { sa := er.span, sb := hReadEq.read.span }) := do
  withTraceNode m!"{processingEmoji} ... ⊆ {hReadEq.read.span} ? " do
    -- the read we are analyzing should be a subset of the hypothesis
    let subset := (MemSubsetProp.mk er.span hReadEq.read.span)
    let some hSubsetProof ← proveWithOmega? subset (← getBvToNatSimpCtx) (← getBvToNatSimprocs)  hyps
      | return none
    return some (hSubsetProof)

def SimpMemM.findOverlappingReadHyp (hyps : Array Memory.Hypothesis) (er : ReadBytesExpr) :
    SimpMemM <| Option (Σ (hread : ReadBytesEqProof),  MemSubsetProof { sa := er.span, sb := hread.read.span }) := do
  for hyp in hyps do
    let Hypothesis.read_eq hReadEq := hyp
      | continue
    let some subsetProof ← SimpMemM.findOverlappingReadHypAux hyps er hReadEq
      | continue
    return some ⟨hReadEq, subsetProof⟩
  return none


def Expr.kindStr (e : Expr) : String :=
  match e with
  | Expr.forallE .. => "forall"
  | Expr.letE ..  => "let"
  | Expr.const .. => "const"
  | Expr.sort .. => "sort"
  | Expr.lam .. => "lam"
  | Expr.mdata .. => "mdata"
  | Expr.proj .. => "proj"
  | Expr.app .. => "app"
  | Expr.mvar .. => "mvar"
  | Expr.bvar .. => "bvar"
  | Expr.fvar .. => "fvar"
  | Expr.lit .. => "lit"

mutual

/--
Pattern match for memory patterns, and simplify them.
Close memory side conditions with `simplifyGoal`.
Returns if progress was made.
-/
partial def SimpMemM.simplifyExpr (e : Expr) (hyps : Array Memory.Hypothesis) : SimpMemM (Option SimplifyResult) := do
  consumeRewriteFuel
  if ← outofRewriteFuel? then
    trace[simp_mem.info] "out of fuel for rewriting, stopping."

  let e := e.consumeMData

  if e.isSort then
    trace[simp_mem.info] "skipping sort '{e}'."

  let .some er := ReadBytesExpr.ofExpr? e
    | SimpMemM.walkExpr e hyps

  if let .some ew := WriteBytesExpr.ofExpr? er.mem then
    trace[simp_mem.info] "{checkEmoji} Found read of write."
    trace[simp_mem.info] "read: {er}"
    trace[simp_mem.info] "write: {ew}"
    trace[simp_mem.info] "{processingEmoji} read({er.span})⟂/⊆write({ew.span})"

    let separate := MemSeparateProp.mk er.span ew.span
    let subset := MemSubsetProp.mk er.span ew.span
    if let .some separateProof ← proveWithOmega? separate (← getBvToNatSimpCtx) (← getBvToNatSimprocs) hyps then do
      trace[simp_mem.info] "{checkEmoji} {separate}"
      let result ← MemSeparateProof.rewriteReadOfSeparatedWrite er ew separateProof e
      setChanged
      return result
    else if let .some subsetProof ← proveWithOmega? subset (← getBvToNatSimpCtx) (← getBvToNatSimprocs) hyps then do
      trace[simp_mem.info] "{checkEmoji} {subset}"
      let result ← MemSubsetProof.rewriteReadOfSubsetWrite er ew subsetProof e
      setChanged
      return result
    else
      trace[simp_mem.info] "{crossEmoji} Could not prove {er.span} ⟂/⊆ {ew.span}"
      SimpMemM.walkExpr e hyps
  else
    -- read
    trace[simp_mem.info] "{checkEmoji} Found read {er}."
    -- TODO: we don't need a separate `subset` branch for the writes: instead, for the write,
    -- we can add the theorem that `(write region).read = write val`.
    -- Then this generic theory will take care of it.
    withTraceNode m!"Searching for overlapping read {er.span}." do
      let some ⟨hReadEq, hSubsetProof⟩ ← findOverlappingReadHyp hyps er
        | SimpMemM.walkExpr e hyps
      let out ← MemSubsetProof.rewriteReadOfSubsetRead er hReadEq hSubsetProof e
      setChanged
      return out

partial def SimpMemM.walkExpr (e : Expr) (hyps : Array Memory.Hypothesis) : SimpMemM (Option SimplifyResult) := do
  withTraceNode (traceClass := `simp_mem.expr_walk_trace) m!"🎯 {e} | kind:{Expr.kindStr e}" (collapsed := false) do
  let e ← instantiateMVars e
  match e.consumeMData with
  | .app f x =>
    let fResult ← SimpMemM.simplifyExpr f hyps
    let xResult ← SimpMemM.simplifyExpr x hyps
    -- return (← SimplifyResult.default e)
    match (fResult, xResult) with
    | (none, some xResult) =>
        let outResult ← mkCongrArg f xResult.eqProof
        return some ⟨e.updateApp! f xResult.eNew, outResult⟩
    | (some fResult, none) =>
        let outResult ← mkCongrFun fResult.eqProof x
        return some ⟨e.updateApp! fResult.eNew x, outResult⟩
    | (some fResult, some xResult) =>
        let outResult ← mkCongr fResult.eqProof xResult.eqProof
        return some ⟨e.updateApp! fResult.eNew xResult.eNew, outResult⟩
    | _ => return none
    -- let outResult ← mkCongr fResult.eqProof xResult.eqProof
    -- -- | I think I see where the problem is. here, I should have updated with the other result.
    -- return ⟨e.updateApp! f x, outResult⟩
  | _ => return none


/--
simplify the goal state, closing legality, subset, and separation goals,
and simplifying all other expressions. Returns `true` if an improvement has been made
in the current iteration.
-/
partial def SimpMemM.simplifyGoal (g : MVarId) (hyps : Array Memory.Hypothesis) : SimpMemM Unit := do
  SimpMemM.withContext g do
    let gt ← g.getType
    withTraceNode m!"Simplifying goal." do
        -- TODO: I changed this to WHNF!
        -- let out ← SimpMemM.simplifyExpr (← whnf gt) hyps
        let some out ← SimpMemM.simplifyExpr gt hyps
          | return ()
        check out.eNew
        check out.eqProof
        let newGoal ←  (← getMainGoal).replaceTargetEq out.eNew out.eqProof
        replaceMainGoal [newGoal]
end

/--
The core simplification loop.
We look for appropriate hypotheses, and simplify (often closing) the main goal using them.
-/
partial def SimpMemM.simplifyLoop : SimpMemM Unit := do
  let g ← getMainGoal
  g.withContext do
    let hyps := (← getLocalHyps)
    let foundHyps ← withTraceNode m!"Searching for Hypotheses" do
      let mut foundHyps : Array Memory.Hypothesis := #[]
      for h in hyps do
        foundHyps ← hypothesisOfExpr h foundHyps
      pure foundHyps

    withTraceNode m!"Summary: Found {foundHyps.size} hypotheses" do
      for (i, h) in foundHyps.toList.enum do
        trace[simp_mem.info] m!"{i+1}) {h}"

    -- goal was not closed, try and improve.
    let mut everChanged := false
    while true do
      resetChanged
      if (← outofRewriteFuel?) then break

      withTraceNode m!"Performing Rewrite At Main Goal" do
        let _ ← SimpMemM.simplifyGoal (← getMainGoal) foundHyps
      let changed := (← getThe State).changed
      everChanged := everChanged || changed

      /- we didn't change on this iteration, so we break out of the loop. -/
      if !changed then
        trace[simp_mem.info] "{crossEmoji} No progress made in this iteration. halting."
        break

    /- we haven't changed ever, so we throw an error. -/
    if !everChanged && (← getConfig).failIfUnchanged then
        throwError "{crossEmoji} simp_mem failed to make any progress."

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def simpMem (cfg : SimpMemConfig := {}) : TacticM Unit := do
  -- evalTactic (← `(simp (config := {failIfUnchanged := false}) only [memory_rules]))
  SimpMemM.run SimpMemM.simplifyLoop cfg


/-- The `simp_mem` tactic, for simplifying away statements about memory. -/
def simpMemTactic (cfg : SimpMemConfig) : TacticM Unit := simpMem cfg

end SeparateAutomation

/--
Allow elaboration of `SimpMemConfig` arguments to tactics.
-/
declare_config_elab elabSimpMemConfig SeparateAutomation.SimpMemConfig


/-
This allows users to supply a list of hypotheses that simp_mem should use.
Modeled after `rwRule`.
-/
syntax simpMemRule := term

/-
The kind of simplification that must be performed. If we are told
that we must simplify a separation, a subset, or a read of a write,
we perform this kind of simplification.
-/
syntax simpMemSimplificationKind := "⟂" <|> "⊂w" <|> "⊂r" (term)?


open Lean.Parser.Tactic in
/--
The simp_mem tactic allows simplifying expressions of the form `Memory.read_bytes rbase rn (mem')`.
`simp_mem` attempts to discover the result of the expression by various heuristics,
which can be controlled by the end user:

- (a) If `mem' = Memory.write_bytes wbase wn mem` and we know that `(rbase, rn) ⟂ (wbase, wn)`, then we simplify to `mem.read (rbase, rn)`.
- (b) If `mem' = Memory.write_bytes wbase wn wval mem` and we kow that `(rbase, rn) ⊆ (wbase, wn)`, then we simplify to `wval.extract (rbase, rn) (wbase, wn)`.
- (c) If we have a hypothesis `hr' : mem'.read_bytes  rbase' rn' = rval`, and we know that `(rbase, rn) ⊆ (rbase', rn')`, then we simplify to `rval.extract (rbase, rn) (rbase', rn')`.

These simplifications are performed by reducing the problem to a problem that can be solved by a decision procedure (`omega`) to establish
which hypotheses are at play. `simp_mem` can be controlled along multiple axes:

1. The hypotheses that `simp_mem` will pass along to the decision procedure to discover overlapping reads (like `hr'`),
   and hypotheses to establish memory (non-)interference, such as `(rbase, rn) ⟂ (wbase, wn)`.
  + simp_mem using []: try to perform the rewrite using no hypotheses.
  + simp_mem using [h₁, h₂]: try to perform the rewrite using h₁, h₂, as hypotheses.

2. The kind of rewrite that simp_mem should apply. By default, it explores all possible choices, which might be expensive due to repeated calls to the decision
   procedure. The user can describe which of (a), (b), (c) above happen:
   + `simp_mem ⟂` : Only simplify when read is disjoint from write.
   + `simp_mem ⊂w` : Only simplify when read overlaps the write.
   + `simp_mem ⊂r hr` : Simplify when read overlaps with a known read `hr : mem.read_bytes baseaddr' n' = val`.
                        This is useful for static information such as lookup tables that are at a fixed location and never modified.
   + `simp_mem ⊂r` : Simplify when read overlaps with known read from hypothesis list.

3. The targets where the rewrite must be applied. (This needs some thought: does this even make sense?)
   + `simp_mem at ⊢`
   + `simp_mem at h₁, h₂, ⊢`

-/
syntax (name := simp_mem) "simp_mem" (Lean.Parser.Tactic.config)? (simpMemSimplificationKind)? ("using" "[" withoutPosition(simpMemRule,*,?) "]")? (location)? : tactic

@[tactic simp_mem]
def evalSimpMem : Tactic := fun
  | `(tactic| simp_mem $[$cfg]?) => do
    let cfg ← elabSimpMemConfig (mkOptionalNode cfg)
    SeparateAutomation.simpMemTactic cfg
  | _ => throwUnsupportedSyntax
