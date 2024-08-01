/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec
import Tactics.IntroHyp
import Lean
open Lean Elab Tactic Expr Meta
open BitVec

----------------------------------------------------------------------

/- `fetchAndDecodeInst` simplifies the hypothesis

`h_step: s_next = stepi s`

by unfolding `stepi`, and then simplifying `fetch_inst` and
`decode_raw_inst`, which results in the following:

`h_step: s_next = exec_inst <decoded_instruction> s`

First, the function `stepi` is unfolded, which yields a term
containing `fetch_inst`. This function is then rewritten using the
lemma `fetch_inst_from_program` to a call of `Map.find?`; we expect
that `Map.find?` will have ground arguments (program counter and
program). We reduce this call of `Map.find?` via the simproc
`reduceMapFind?`. The function `decode_raw_inst` is also expected to
be called on a ground 32-bit instruction. We reduce this call by using
`simp/ground`.

Fetching and decoding an instruction relies upon knowing the values of
three components of the current state: error, program counter, and
program (see the definitions of `fetch_inst` and
`decode_raw_inst`). We expect that these values can be gleaned from
the local context. Moreover, we expect that there exist hypotheses in
the local context of the form

`<name>: r <fld> <state> = value

whose user-facing names describe both the field and the state. (Such
hypotheses are added by the tactic "introduce_fetch_lemmas").

As such, `fetchAndDecodeInst` also adds any hypotheses in the context
whose usernames begin with the supplied prefix `hyp_prefix` to the
simp set.  It is the caller's responsibility to provide the
appropriate `hyp_prefix` here.

TODO: More error checks: e.g., checks whether `h_step` and the
resulting hypothesis have the expected forms (i.e., in terms of
`stepi` and `exec_inst`, respectively).
-/
def fetchAndDecodeInst (goal : MVarId) (h_step : Name) (hyp_prefix : String)
  : TacticM Bool := goal.withContext do
  -- Find all the FVars in the local context whose name begins with
  -- hyp_prefix.
  let h_step_expr ← getFVarFromUserName h_step
  let lctx ← getLCtx
  let matching_decls := filterDeclsWithPrefix lctx hyp_prefix.toName
  -- logInfo m!"matching_decls: {matching_decls[0]!.userName}"

  -- Simplify `fetch_inst`: note: using `ground := true` here causes
  -- maxRecDepth to be reached. Use reduceMapFind? instead.
  let (ctx, simprocs) ←
    LNSymSimpContext (config := {decide := true})
                     (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
                     (decls_to_unfold := #[``stepi])
                     (thms := #[``fetch_inst_from_program])
                     (decls := matching_decls)
                     (simprocs := #[``reduceMapFind?])
  let some goal' ← LNSymSimp goal ctx simprocs (fvarid := h_step_expr.fvarId!) |
                   logInfo m!"[fetchAndDecodeInst] The goal appears to be solved, but this tactic \
                              is not a finishing tactic! Something went wrong?"
                   return false
  goal'.withContext do
  let h_step_expr ← getFVarFromUserName h_step
  -- Simplify `decode_raw_inst` using simp/ground.
  let some goal' ← LNSymSimp goal' { ctx with config := {ground := true} }
                             simprocs (fvarid := h_step_expr.fvarId!) |
                   logInfo m!"[fetchAndDecodeInst] The goal appears to be solved, but this tactic \
                              is not a finishing tactic! Something went wrong?"
                   return false
  replaceMainGoal [goal']
  return true

def fetchAndDecodeElab (h_step : Name) (hyp_prefix : String) : TacticM Unit :=
  withMainContext
  (do
    let success ← fetchAndDecodeInst (← getMainGoal) h_step hyp_prefix
    if ! success then
      failure)

elab "fetch_and_decode" h_step:ident hyp_prefix:str : tactic =>
  fetchAndDecodeElab (h_step.getId) (hyp_prefix.getString)

----------------------------------------------------------------------

def introFetchDecodeLemmas (goal : MVarId) (hStep : Expr) (hProgram : Expr)
  (hyp_prefix : String) :
  TacticM Bool := goal.withContext do
  let_expr Eq _ st_var nest ← (← inferType hStep) | return false
  let_expr Eq _ _ program ← (← inferType hProgram) | return false
  -- Find all the FVars in the local context whose name begins with
  -- hyp_prefix.
  let lctx ← getLCtx
  let matching_decls := filterDeclsWithPrefix lctx hyp_prefix.toName
  -- logInfo m!"matching_decls: {matching_decls[0]!.userName}"
  let (ctx, simprocs) ←
    LNSymSimpContext (config := {decide := true})
                     (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
                     -- Is it necessary to have CheckSPAlignment here?
                     (decls_to_unfold := #[])
                     (thms := #[])
                     (decls := matching_decls)
                     (simprocs := #[])
  let st_var := consumeMData st_var
  let nest := consumeMData nest
  if ! (st_var.isFVar && nest.isApp) then
    logInfo m!"[introFetchLemmasExpr] Unexpected hStep expression. We expect \
                the state variable on the LHS to be an FVar and the \
                term on the RHS to be a function application. Here is \
                what they actually are: \
                st_var: {st_var.ctorName}; nest: {nest.ctorName}."
    return false
  let st_var_str := toString (← (getFVarLocalDecl st_var)).userName
  -- Introduce a hypothesis (and attempt to prove) that the error field in the
  -- new state is `StateError.None`.
  let (goal', maybe_err_goal) ←
    introLNSymHyp goal st_var (gen_hyp_name st_var_str "err")
      (mkAppN (Expr.const ``Eq [1])
            #[(mkConst ``StateError),
              (mkAppN (Expr.const ``r []) #[(mkConst ``StateField.ERR), st_var]),
              (mkConst ``StateError.None)])
      ctx simprocs
  -- Obtain the new PC value from the nest of updates, and add its
  -- corresponding read hypothesis to the context.
  let some pc_val := getArmStateComponentNoMem (mkConst ``StateField.PC) nest |
    logInfo m!"[introFetchDecodeLemmas] We only parse function calls `w` and `write_mem_bytes` \
                in the state update equation. Right now, we cannot determine the PC value \
                from the expression: {nest}."
    return false
  let (goal', maybe_pc_goal) ←
    introLNSymHyp goal' st_var (gen_hyp_name st_var_str "pc")
      (mkAppN (Expr.const ``Eq [1])
        #[(← inferType pc_val),
          (mkAppN (Expr.const ``r []) #[(mkConst ``StateField.PC), st_var]),
          pc_val])
      ctx simprocs
  -- Introduce a hypothesis (and attempt to prove) that the stack
  -- pointer (SP) in the new state is aligned.
  let (goal', maybe_sp_aligned_goal) ←
    introLNSymHyp goal' st_var (gen_hyp_name st_var_str "sp_aligned")
      (mkAppN (Expr.const ``CheckSPAlignment []) #[st_var])
      ctx simprocs
  -- Introduce a hypothesis (and attempt to prove) that the program in
  -- the new state is the same as it was earlier in `hProgram`.
  let (goal', maybe_prog_goal) ←
    introLNSymHyp goal' st_var (gen_hyp_name st_var_str "program")
      (mkAppN (Expr.const ``Eq [1])
        #[(mkConst ``Program),
          (mkAppN (Expr.const ``ArmState.program []) #[st_var]),
          program])
      ctx simprocs

  let other_unsolved_goals := optionListtoList [maybe_err_goal, maybe_pc_goal, maybe_sp_aligned_goal, maybe_prog_goal]
  replaceMainGoal (goal' :: other_unsolved_goals)
  return true

def introFetchDecodeLemmasElab (h_step : Name) (h_program : Name) (hyp_prefix : String)
  : TacticM Unit :=
  withMainContext
  (do
    let h_step ← getFVarFromUserName h_step
    let h_program ← getFVarFromUserName h_program
    let success ← introFetchDecodeLemmas (← getMainGoal) h_step h_program hyp_prefix
    if ! success then
      failure)

elab "intro_fetch_decode_lemmas" h_step:ident h_program:ident hyp_prefix:str : tactic =>
  introFetchDecodeLemmasElab (h_step.getId) (h_program.getId) (hyp_prefix.getString)
