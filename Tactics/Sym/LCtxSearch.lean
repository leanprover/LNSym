/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
import Lean

open Lean

/-!
## Local Context Search

In this module we build an abstraction around searching the local context for
multiple local variables or hypotheses at the same time.

The main entry point to search is `searchLocalContext`.
`searchFor` is the main way to register which patterns to search for,
and what actions to perform if the variable is found (or not found).
-/

variable (m) [Monad m]

inductive LCtxSearchResult
  /-- This occurence of the pattern should be ignored -/
  | skip
  /-- This should be counted as a successful occurence,
  and we should *continue* matching for more variables -/
  | continu
  /-- This should be counted as a successful occurence,
  and we can *stop* matching against this particular pattern -/
  | done
  deriving DecidableEq

structure LCtxSearchState.Pattern where
  /-- The type to search for (up to def-eq!).
  Notice that `expectedType` is stored as a monadic value,
  so that we can create fresh metavariables for each search -/
  expectedType : m Expr
  /-- A cached result of `expectedType`;
  this should be regenerated after every match! -/
  cachedExpectedType : Expr
  /-- `whenFound` will be called whenever a match for `pattern` is found,
  with the instantiated pattern as an argument.
  The returned `LCtxSearchResult` determines if we count this as a successful
  occurence of the pattern, which is relevant for if `whenNotFound` is called.

  NOTE: We give the (instantiated) pattern as an arg, *not* the expression that
  we matched against. This way, implementors can recover information through
  syntactic destructuring.

  An alternative design would have `pattern : MetaM (List Expr × Expr)`,
  where the list is intended to be a list of meta-variables, and
  `whenFound : List Expr → Expr → m Unit`, where we would call
  `whenFound` with the list returned by `pattern` (which has the metavariables
  that should now have been instantiated with subexpressions of interest).
  -/
  whenFound : Expr → m LCtxSearchResult
  /-- `whenNotFound` will be called if no successful occurence of the pattern
  (as determined by the return value of `whenFound`)
  could be found in the local context -/
  whenNotFound : Expr → m Unit
  /-- How many times have we (successfully) found the pattern -/
  occurences : Nat := 0
  /-- Whether the pattern is active; is `isActive = false`,
  then no further matches are attempted -/
  isActive : Bool := true

structure LCtxSearchState where
  patterns : Array (LCtxSearchState.Pattern m)

abbrev SearchLCtxForM := StateT (LCtxSearchState m) m

variable {m}

/-- register a new expression pattern to search for:
- `expectedType` should give an expression, with meta-variables, which is the
  type to search for.

  Note that, once a match is found, any meta-variables in `expectedType` will be
  assigned, and thus further matches will now need to match those same concrete
  values. That is why `expectedType` is a monadic value, which is re-evaluated
  after each successful match.
  If multiple matches, with distinct instantiations of a meta-variable, are
  desired, it's important that meta-variable is created *inside* the
  `expectedType` action.
  If, on the other hand, a single instantiation accross all variables is
  desired, the meta-variable should be created *outside*.
- `whenFound` will be called whenever a local variable whose type is def-eq
  to `expectedType` is found, with as argument the instantiated `expectedType`.
  The return value of `whenFound` is used to determine if a match is considered
  succesful.
- `whenNotFound` will be called if no local variable could be found with a type
  def-eq to the pattern, or if `whenFound` returned `skip` for all variables
  that were found. For convenience, we pass in the `expectedType` here as well.
  See `throwNotFound` for a convenient way to throw an error here.

WARNING: Once a pattern is found for which `whenFound` returns `done`, that
particular variable will not be matched for any other patterns.
In case of overlapping patterns, the pattern which was added first will be
tried first
-/
def searchLCtxFor
    (expectedType : m Expr)
    (whenFound : Expr → m LCtxSearchResult)
    (whenNotFound : Expr → m Unit := fun _ => pure ())
    : SearchLCtxForM m Unit := do
  let pattern := {
    -- Placeholder value, since we can't evaluate `m` inside of `LCtxSearchM`
    cachedExpectedType :=← expectedType
    expectedType, whenFound, whenNotFound
  }
  modify fun state => { state with
    patterns := state.patterns.push pattern
  }

/-- A wrapper around `searchLCtxFor`, which is simplified for matching at most
one occurence of `expectedType` -/
def searchLCtxForOnce
    (expectedType : Expr)
    (whenFound : Expr → m Unit)
    (whenNotFound : Expr → m Unit := fun _ => pure ())
    : SearchLCtxForM m Unit := do
  searchLCtxFor (pure expectedType)
    (fun e => do whenFound e; return .done)
    whenNotFound

section Run
open Meta (isDefEq)
variable [MonadLCtx m] [MonadLift MetaM m]

/--
Attempt to match `e` against the given pattern:
- if `e` is def-eq to `pat.cachedExpectedType`, then return
    the updated pattern state (with a fresh `cachedExpectedType`), and
    the result of `whenFound`
- Otherwise, if `e` is not def-eq, return `none`
-/
def LCtxSearchState.Pattern.match? (pat : Pattern m) (e : Expr) :
    m (Option (Pattern m × LCtxSearchResult)) := do
  if !pat.isActive then
    return none
  else if !(← isDefEq e pat.cachedExpectedType) then
    return none
  else
    let cachedExpectedType ← pat.expectedType
    let res ← pat.whenFound pat.cachedExpectedType
    let occurences := match res with
      | .skip => pat.occurences
      | .done | .continu => pat.occurences + 1
    return some ({pat with cachedExpectedType, occurences}, res)

/-- Search the local context for variables of certain types, in a single pass.
`k` is a monadic continuation that determines the patterns to search for,
see `searchLCtxFor` to see how to register those patterns
-/
def searchLCtx (k : SearchLCtxForM m Unit) : m Unit := do
  let ((), { patterns }) ← StateT.run k ⟨#[]⟩
  -- We have to keep `patterns` in a Subtype to be able to prove our indexes
  -- are valid even after mutation
  -- TODO(@alexkeizer): consider using `Batteries.Data.Vector`, if we can
  --                    justify a batteries dependency
  let n := patterns.size
  let mut patterns : { as : Array _ // as.size = n} :=
    ⟨patterns, rfl⟩

  -- The main search
  for decl in ← getLCtx do
    for hi : i in [0:n] do
      have hi : i < patterns.val.size := by
        rw [patterns.property]; get_elem_tactic
      let pat := patterns.val[i]
      if let some (pat, res) ← pat.match? decl.type then
        patterns := ⟨
          patterns.val.set ⟨i, hi⟩ pat,
          by simp[patterns.property]
        ⟩
        if res = .done || res = .continu then
          break -- break out of the inner loop

  -- Finally, check each pattern and call `whenNotFound` if appropriate
  for pat in patterns.val do
    if pat.occurences = 0 then
      pat.whenNotFound pat.cachedExpectedType
  return ()

variable [MonadError m] in
/-- Throw an error complaining that no variable of `expectedType` could
be found -/
def throwNotFound (expectedType : Expr) : m Unit :=
  throwError "Expected a local variable of type:\n  {expectedType}\n\
    but no such variable was found in the local context"

end Run
