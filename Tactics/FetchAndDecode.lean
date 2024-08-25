/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Nathan Wetzler
-/
import Arm.Exec
import Tactics.IntroHyp
import Lean
open Lean Elab Tactic Expr Meta
open BitVec


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
    LNSymSimpContext (config := {decide := true, failIfUnchanged := false})
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
  if !other_unsolved_goals.isEmpty then
    trace[Tactic.sym] "failed to solve goals: {other_unsolved_goals}"

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
