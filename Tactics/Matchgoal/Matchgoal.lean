import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import Lean.PrettyPrinter
import Lean.PrettyPrinter.Delaborator
import Lean.Data.Json
import Tactics.Attr
-- import Matchgoal.Trace
-- import Matchgoal.LogicT

namespace MatchGoal

open Lean Elab Meta Tactic Term Std RBMap

/-- pattern of the hypothesis -/
declare_syntax_cat pattern_hyp

/-- pattern of 'term' variable #v -/
declare_syntax_cat pattern_term_var

/-- pattern of hypothesis variable '^H' -/
declare_syntax_cat pattern_hyp_var -- pattern_term_ident maybe?

/-- pattern of expressions -/
declare_syntax_cat pattern_expr

scoped syntax (name := term_var) "#" noWs ident : pattern_term_var
scoped syntax (name := term_var_blank) "#_" : pattern_term_var
scoped syntax (name := hyp_var) "^" noWs ident : pattern_hyp_var
-- scoped syntax (name := hyp_var_blank) "^_" : pattern_term_var


/- Names that are created from `#<name>` syntax. -/
@[reducible]
def PatternName := Name

open Lean Elab in

/-- every unification variable is a term. -/
scoped elab (name := termvar2term) t:pattern_term_var : term => do
  let s : Syntax ←
    match t with
    | `(pattern_term_var| #$i:ident) => pure i
    | _ => throwUnsupportedSyntax
  elabTerm s (expectedType? := .none)


/-- every hypothesis variable is an ident. -/
scoped elab (name := hypvar2ident) t:pattern_hyp_var : term => do
  let s : Syntax ←
    match t with
    | `(pattern_hyp_var| ^$i:ident) => pure i
    | _ => throwUnsupportedSyntax
  elabTerm s (expectedType? := .none)


/--  var -var2term-> term -term2expr-> expr -/
scoped syntax (name := term2expr) (priority := 0)
  term : pattern_expr

scoped syntax (name := hyp)
  "(" pattern_hyp_var ws ":" ws pattern_expr ")" : pattern_hyp

scoped syntax (name := elabUnificationExpr)
  "[pattern_expr|" pattern_expr "]" : term
macro_rules
| `([pattern_expr| $e:term]) => return e

syntax hyps := sepBy(pattern_hyp, "; ")

structure Depth where
  depth : Nat := 0

def Depth.increment (d: Depth) : Depth where
  depth := d.depth + 1

instance : ToString Depth where
  toString d := Id.run do
    let rec go (s : String) : Nat → String 
    | 0 => s
    | n' + 1 =>  go (s ++ " |") n'
    go "" d.depth

instance : ToMessageData Depth where
  toMessageData d := toString d


structure PatternHyp where
  /-- for position information. TODO: pull position out of the raw Tsyntax? -/
  nameStx : Syntax.Ident
  rhs : TSyntax `pattern_expr

-- @[computed_field] TODO: figure out how to use computed fields.
def PatternHyp.name (p : PatternHyp) : Name  := p.nameStx.getId

instance : ToMessageData PatternHyp where
  toMessageData h := m!"{h.nameStx} : {h.rhs}"
def PatternHyp.parse : TSyntax `pattern_hyp →  TacticM PatternHyp
| `(pattern_hyp| (^$i: ident : $e:pattern_expr)) =>
   return { nameStx := i, rhs := e }
| stx => do
  logErrorAt stx <| MessageData.tagged `Tactic.Matchgoal <| m! "unknown hypothesis pattern '{stx}'"
  throwUnsupportedSyntax

structure PatternCtx where
  mvars : Std.HashMap PatternName Syntax := {}
  /-- match hypothesis pattern names to their FVarIds in the local context --/
  hyps : Std.HashMap PatternName (PatternHyp × FVarId) := {}
deriving Inhabited

instance : ToMessageData PatternCtx where
  toMessageData pctx := Id.run do
    let mvars := MessageData.ofList <| pctx.mvars.toList.map (fun (k, v) =>  m!"{k} ↦ {v}")
    let hyps := MessageData.ofList <| pctx.hyps.toList.map fun (k, v) => m!"{k} ↦ {(v.snd.name)}"
    m!"PatternCtx({mvars}, {hyps})"

-- Match the syntax 's' against the syntax 't', where 's' is allowed to have patterns.
partial def stxMatcher (depth : Depth) (pctx : PatternCtx) (s : Syntax) (t : Syntax): TacticM (Option PatternCtx) := do
  trace[Tactic.matchgoal] "{depth}stxMatcher: '{s}' =?= '{t}'"
  match s with 
  | `(pattern_expr| $s':term) =>  do
    trace[Tactic.matchgoal] "{depth}stxMatcher: SUCCESS pattern_expr unwrap."
    stxMatcher depth pctx s' t
  | `(pattern_term_var| #$i:ident) | `(term| #$i:ident) => do
      match pctx.mvars.find? i.getId with
      | .none => 
        trace[Tactic.matchgoal] "{depth}stxMatcher: SUCCESS assigned #{i} := 't'"
        return .some { pctx with mvars := pctx.mvars.insert i.getId t }
      | .some mvarStx =>
        match (← stxMatcher depth.increment pctx mvarStx t) with
        | .none => 
          trace[Tactic.matchgoal] "{depth}stxMatcher: FAILURE"
          return .none
        | .some pctx' =>
          trace[Tactic.matchgoal] "{depth}stxMatcher: SUCCESS"
          return .some pctx'
  | _ =>
    match s, t with
    | Syntax.missing, Syntax.missing => do 
      trace[Tactic.matchgoal] "{depth}stxMatcher: SUCCESS"
      return .some pctx
    | Syntax.atom  (val := sval) ..  , Syntax.atom (val := tval) .. =>
      let sval := sval.trim
      let tval := tval.trim
      if sval = tval then
        trace[Tactic.matchgoal] "{depth}stxMatcher: SUCCESS atom '{sval}' = '{tval}'"
        return .some pctx
      else
        trace[Tactic.matchgoal] "{depth}stxMatcher: FAILURE atom '{sval}' /= '{tval}'"
        return .none
    | Syntax.ident (val := sval) .., .ident (val := tval) .. =>
      if sval = tval then
        trace[Tactic.matchgoal] "{depth}stxMatcher: SUCCESS ident '{sval}' = '{tval}'"
        return .some pctx
      else 
        trace[Tactic.matchgoal] "{depth}stxMatcher: FAILURE ident '{sval}' /= '{tval}'"
        return .none
    | .node (kind := skind) (args := sargs) .., .node (kind := tkind) (args := targs) .. => do
        if skind != tkind then
          trace[Tactic.matchgoal] "{depth}stxMatcher: FAILURE node '{skind}' /= '{tkind}'"
          return .none
        else
          let mut pctx := pctx
          for (sarg, targ) in sargs.zip targs do
            match ← stxMatcher depth.increment pctx sarg targ with
            | .none => return .none
            | .some pctx' => pctx := pctx'
          return .some pctx
    | _, _ => return .none

open Lean Elab Macro Tactic in
/--
Replace holes in the Syntax given by `pattern_var` with the values in ctx
TODO: We need to know if we should replace `MVars` or
`Name`s. In the hypothesis manipulation, we should replace MVarIds.
For the final proof production, we should replace `Names` ? -/
-- TODO: replace with 'replacer'?
partial def replace (pctx : PatternCtx) (s : Syntax) : TacticM (Option Syntax) := do
  -- trace[Tactic.matchgoal] "replace s:'{toString s}'"
  match s with
  | `(pattern_term_var| #$i:ident) | `(term| #$i:ident) => do
     trace[Tactic.matchgoal] "replace in ident '{i}'"
      match pctx.mvars.find? i.getId with
      | .none => do
          -- TODO: this can be verified statically?
         trace[Tactic.matchgoal.search] m!"Matchgoal variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         logErrorAt s <|
           MessageData.tagged `Tactic.Matchgoal <|
           m!"Matchgoal variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         return .none
      | .some stx => return stx
  | `(pattern_hyp_var| ^$i:ident) | `(term| ^$i:ident) => do
      match pctx.hyps.find? i.getId with
      | .none => do
         trace[Tactic.matchgoal.search] m!"Matchgoal hypothesis variable {i} has not been unified when replacing syntax '{s}'. This is an error."
         return .none
      | .some (hypPat, _) => do return hypPat.nameStx
  | _ =>
    match s with
    | Syntax.node info kind args => do
        let mut args' := #[]
        for a in args do
           match ← replace pctx a with
           | .some a' => args' := args'.push a'
           | .none => return .none
        return Syntax.node info kind args'
    | Syntax.missing | Syntax.atom .. | Syntax.ident .. => return s



open Lean Core Elab Meta Macro Tactic PrettyPrinter in
def PatternHyp.matcher (depth : Depth) ( pctx: PatternCtx)
  (hpat : PatternHyp)
  (ldecl: LocalDecl) : TacticM (Option PatternCtx) := do
    let mut pctx := pctx
    let ldeclType : Expr := ldecl.type
    let ldeclStx : Syntax ← delab ldeclType
    match (← stxMatcher depth.increment pctx hpat.rhs.raw ldeclStx) with 
    | .none => 
      trace[Tactic.matchgoal.matcher] "FAILURE: PatternHyp.matcher {pctx} : {hpat} =!= {ldeclStx}"
      return .none
    | .some pctx' => 
      trace[Tactic.matchgoal.matcher] "SUCCESS: PatternHyp.matcher {pctx} : {hpat} === {ldeclStx}"
      pctx := pctx'
        -- Convert the given goal `Ctx |- target` into `Ctx |- type -> target`.
        -- let newgoal ← (← getMainGoal).assert hpat.name ldeclType hpatexpr
        let newgoal ← (← getMainGoal).assert hpat.name ldeclType ldecl.toExpr
        -- `intros` the arrow.
        let (hypFVar, newgoal) ← newgoal.intro1P
        replaceMainGoal [newgoal]
        return (.some { pctx with hyps := pctx.hyps.insert hpat.name (hpat, hypFVar) })



open Lean Core Meta Elab Macro Tactic PrettyPrinter in
/-- The search state of the backtracking depth first search. -/
def depthFirstSearchHyps
  (depth : Depth)
  (tac : TSyntax `tactic)
  (hyppats : List PatternHyp)
  (pctx : PatternCtx)
  (gpat? : Option (TSyntax `pattern_expr)): TacticM Bool :=  do
  trace[Tactic.matchgoal.search] m!"==={depth.depth}==="
  trace[Tactic.matchgoal.search] m!"{depth}STEP: depthFirstSearchHyps {hyppats}"
  match hyppats with
  | [] => do
     let stateBeforeMatcher ← Tactic.saveState
     let mut pctx := pctx
     if let .some gpat := gpat? then
       -- Do not do this in two steps: do the matching and the elaboration in the same step.
       let mainTargetStx ← delab (← getMainTarget)
       trace[Tactic.matchgoal.search] m!"{depth}STEP: '{gpat}' =?= '{mainTargetStx}'"
       match ← stxMatcher depth pctx gpat mainTargetStx with 
       | .none =>  
          trace[Tactic.matchgoal.search] m!"{depth}FAILED '{gpat} =/= '{mainTargetStx}'"
          logErrorAt gpat
            <| MessageData.tagged `Tactic.Matchgoal <|
              m! "unable to match '{gpat}' =?= '{mainTargetStx}'"
          restoreState stateBeforeMatcher
          return False
       | .some pctx' =>
          pctx := pctx'
          trace[Tactic.matchgoal.search] m!"{depth}SUCCESS '{gpat} === '{mainTargetStx}'"
     trace[Tactic.matchgoal.search] m!"{depth}STEP: preparing to run tactic '{tac}'."
     trace[Tactic.matchgoal.search] m!"{depth}replacing '{tac}' with context {pctx}" -- TODO: make {ctx} nested
     let tac ← match ← replace pctx tac with
        | .some t => 
          trace[Tactic.matchgoal.search] m!"{depth}SUCCESS: replaced with {t}"
          pure t
        | .none =>
          trace[Tactic.matchgoal.search] m!"{depth}FAILED: no replacement generated"
          restoreState stateBeforeMatcher
          return False

     trace[Tactic.matchgoal.search] m!"{depth}STEP: running tactic '{tac}'."
     if ← tryTactic (evalTactic tac) then
        trace[Tactic.matchgoal.search] m!"{depth}SUCCESS running '{tac}'."
        return true
     else
        trace[Tactic.matchgoal.search] m!"FAILURE running '{tac}'."
        restoreState stateBeforeMatcher
        return false
  | hyppat :: hyppats' =>
     let stateBeforeMatcher ← Tactic.saveState
     for hyp in (← getMainDecl).lctx do
       if hyp.isImplementationDetail then continue
       stateBeforeMatcher.restore -- Paranoia. This should ideally not be necessary.
       if let .some ctx'  ← hyppat.matcher depth.increment pctx hyp then
         if  (← depthFirstSearchHyps depth.increment tac hyppats' ctx' gpat?) then
          return true
     stateBeforeMatcher.restore -- Paranoia. This should ideally not be necessary.
     return False

/-- match goal tactic -/
-- local syntax (name := matchgoal)
scoped syntax (name := matchgoal)
  "matchgoal" ws
  (hyps ws)?
  "⊢" ws (( pattern_expr ws)?) "=>" ws tactic : tactic

-- foobar [[ ident ]] : tactic
open Lean Core Meta Elab Macro Tactic in
@[tactic MatchGoal.matchgoal]
def evalMatchgoal : Tactic := fun stx => -- (stx -> TacticM Unit)
  -- if stx.kind == node and stx[0] == "matchgoal and stx[1] == ....
  match stx with
  | `(tactic| matchgoal
      $[ $[ $hpatstxs? ];* ]?
      ⊢ $[ $gpat?:pattern_expr ]? => $tac:tactic ) => do
    trace[Tactic.matchgoal] m!"{toString gpat?}"
    let mut pctx : PatternCtx := default
    let hpats : List PatternHyp ← match hpatstxs? with
         | .none => pure []
         | .some stxs => stxs.toList.mapM PatternHyp.parse
    let success ← depthFirstSearchHyps (depth := Depth.mk 0) tac hpats pctx gpat?
    match success with
    | true => return ()
    | false => throwError m!"matchgoal backtracking search exhaustively failed. Giving up up on '{stx}'."
    -- then logErrorAt stx <| MessageData.tagged `Tactic.Matchgoal m!"matchgoal failed to find any match"
  | _ => throwUnsupportedSyntax

end MatchGoal

