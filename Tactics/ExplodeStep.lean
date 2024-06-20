import Arm.Exec
import Lean

/-
Tactic `explode_step h`:

The tactic `explode_step` operates on a given declaration `h` in the
goal, where `h` is of the form
`state_var_new = write ... (write ... state_var_old)`.
It then introduces corresponding `read` terms in the context, and also
attempts to prove them.

Here is an example:

Goal:
h : s1 = w (StateField.GPR 31#5) 1#64 (w StateField.PC 2#64 s0)
...
|-
conclusion

`explode_step h` modifies the goal as follows; note the new hypotheses
`h_s1_x31` and `h_s1_pc`. `explode_step h` also attempts to prove each
of these new hypotheses using `simp/decide` with theorems in own custom
simp sets, `minimal_theory`, `bitvec_rules`, and `state_simp_rules`.

Goal:
h : s1 = w (StateField.GPR 31#5) 1#64 (w StateField.PC 2#64 s0)
h_s1_x31 : r (StateField.GPR 31#5) s1 = 1#64
h_s1_pc  : r StateField.PC s1 = 2#64
...
|-
conclusion
-/

open Lean Elab Tactic Expr Meta
open BitVec

/- Get the string representation of `e` if it denotes a bitvector
literal. The bitvector's width is not represented in the resulting
string. -/
def getBitVecString? (e : Expr) : MetaM (Option String) := do
  let maybe_e_literal ← getBitVecValue? e
  match maybe_e_literal with
  | some ⟨_, value⟩ => return some (ToString.toString value.toNat)
  | none => return none

/- Get the string representation of `e` if it denotes a `PFlag`. -/
def getPFlagString? (e : Expr) : MetaM (Option String) := OptionT.run do
  match_expr e with
  | PFlag.N => return "n_flag"
  | PFlag.Z => return "z_flag"
  | PFlag.C => return "c_flag"
  | PFlag.V => return "v_flag"
  | _       => panic! s!"[getPFlagString?] Unexpected expression: {e}"

/- Get the string representation of `e` if it denotes a `StateField`. -/
def getStateFieldString? (e : Expr) : MetaM (Option String) := OptionT.run do
  match_expr e with
  | StateField.GPR iExpr  => return ("x" ++ (← getBitVecString? iExpr))
  | StateField.SFP iExpr  => return ("q" ++ (← getBitVecString? iExpr))
  | StateField.PC         => return "pc"
  | StateField.FLAG pExpr => getPFlagString? pExpr
  | StateField.ERR        => return "err"
  | _                     => panic! s!"[getStateFieldName?] Unexpected expression: {e}"

partial def explodeWriteNest (goal : MVarId)
  (st_var : Expr) (e : Expr) (seen_fields : List String)
  (rest_goals : List MVarId) : TacticM (List MVarId) := do
  if e.isFVar then
    return (goal :: rest_goals)
  else
    match_expr e with
    | w field val rest =>
      -- logInfo m!"field: {field} val: {val} rest: {rest}"
      let some field_str ←
        getStateFieldString? field |
        logInfo m!"[explodeWriteNest] Unexpected field argument of function w: {field}";
        return (goal :: rest_goals)
      if field_str ∈ seen_fields then
        -- Skip if we have already generated a hypothesis for this field.
        explodeWriteNest goal st_var rest seen_fields rest_goals
      else
        let val_type ← inferType val
        let new_prop_type :=
              mkAppN (Expr.const ``Eq [1])
                #[val_type,
                  (mkAppN (Expr.const ``r []) #[field, st_var]),
                  val]
        let st_var_decl ← (getFVarLocalDecl st_var)
        let name := Lean.Name.mkSimple
                      ("h_" ++ (toString st_var_decl.userName) ++ "_" ++ field_str)
        let new_prop_val ← mkFreshExprMVar new_prop_type MetavarKind.syntheticOpaque name
        let maybe_new_prop_val ← substVar? new_prop_val.mvarId! st_var.fvarId!
        match maybe_new_prop_val with
          | none =>
            logInfo m!"[explodeWriteNest] Could not substitute {st_var} in \
                       goal {new_prop_val.mvarId!}";
            return (goal :: rest_goals)
          | some p =>
            -- logInfo m!"p: {p}"
            let some minimal_theory_ext ←
              (getSimpExtension? `minimal_theory) |
               logInfo m!"[explodeWriteNest] Error: minimal_theory simp attribute not found!"
               return (goal :: rest_goals)
            let some state_simp_rules_ext ←
              (getSimpExtension? `state_simp_rules) |
                logInfo m!"[explodeWriteNest] Error: state_simp_rules simp attribute not found!"
                return (goal :: rest_goals)
            let some bitvec_rules_ext ←
              (getSimpExtension? `bitvec_rules) |
               logInfo m!"[explodeWriteNest] Error: bitvec_rules simp attribute not found!"
               return (goal :: rest_goals)
            let (ctx : Lean.Meta.Simp.Context) :=
                { config := { decide := true },
                  simpTheorems := #[← minimal_theory_ext.getTheorems,
                                    ← state_simp_rules_ext.getTheorems,
                                    ← bitvec_rules_ext.getTheorems],
                  congrTheorems := (← Meta.getSimpCongrTheorems) }
            let (p_simp?, _) ←
              simpGoal p ctx #[(← Simp.getSimprocs)]
                (simplifyTarget := true)
                (discharge? := none)
            let new_goals :=
              match p_simp? with
              | none => []
              | some (_, p_simp_mvarid) => [p_simp_mvarid]
            -- let new_goals ←
            --   evalTacticAt
            --     (← `(tactic|
            --           (simp (config := {decide := true}) only
            --                        [state_simp_rules, minimal_theory, bitvec_rules])))
            --     p
            -- logInfo m!"new_goals: {new_goals}"
            let (_, goal') ← MVarId.intro1P $ ← Lean.MVarId.assert goal name new_prop_type new_prop_val
            explodeWriteNest goal' st_var rest (field_str :: seen_fields) (rest_goals ++ new_goals)

      | write_mem_bytes n addr val rest =>
        let n ← (if n.hasExprMVar || n.hasFVar then pure n else whnfD n)
        -- TODO: Define normalizers for addresses and values.
        let addr ← (if addr.hasExprMVar || addr.hasFVar then pure addr else whnfD addr)
        let val ← (if val.hasExprMVar || val.hasFVar then pure val else whnfD val)
        -- logInfo m!"val.appFn!: {val.appFn!} val.appArg!: {val.appArg!}"
        -- let val_arg := val.appArg!
        -- let val_arg ← match_expr val_arg with
        --               | BitVec.zeroExtend _ zn _ =>
        --                 let zn ← whnfD zn
        --                 logInfo m!"zn: {zn}"
        --                 pure val_arg
        --               | _ => pure val_arg
        -- logInfo m!"val_arg: {val_arg}"
        logInfo m!"Skipping hypothesis generation for memory writes for now. \
                   \nn: {n} \naddr: {addr}\n val: {val}"
        explodeWriteNest goal st_var rest seen_fields rest_goals

      | _ =>
        logInfo m!"[explodeWriteNest] Cannot explode the following any further: {e}"
        return (goal :: rest_goals)

partial def explodeStepExpr (hS : Expr) : TacticM Bool :=
  -- We expect hS to be of the following shape:
  -- <hyp>: <var:St> = (w ... (w ... <var:St>))
  withMainContext
  (do
    let S ← inferType hS
    let_expr Eq _ st_var nest ← S | return false
    -- Remove metadata, if present, from st_var and nest.
    let st_var := consumeMData st_var
    let nest := consumeMData nest
    -- logInfo m!"var: {st_var} nest: {nest}"
    if ! (st_var.isFVar && nest.isApp) then
      logInfo m!"[explodeStepExpr] Unexpected expression(s). We expect \
                  the state variable on the LHS to be an FVar and the \
                  term on the RHS to be a function application. Here is \
                  what they actually are: \
                  st_var: {st_var.ctorName}; nest: {nest.ctorName}."
      return false
    else
      let goals ← explodeWriteNest (← getMainGoal) st_var nest [] []
      replaceMainGoal goals
      return true)

def explodeStep (name : Name) : TacticM Unit :=
  withMainContext
  (do
    let h ← getFVarFromUserName name
    let success ← explodeStepExpr h
    if ! success then
      failure)

elab "explode_step" h:ident : tactic =>
  explodeStep (h.getId)

example (s0 s1 : ArmState)
  (h : s1 = w (StateField.GPR 31#5) 12#64 (w StateField.PC 0x2000#64 s0)) :
  r StateField.PC s1 = 0x2000#64 := by
  explode_step h
  assumption
  done

example (s0 s1 : ArmState) (x : BitVec 64)
  (h : s1 = w (StateField.GPR 31#5) x (w StateField.PC 0x2000#64 s0)) :
  r StateField.PC s1 = 0x2000#64 := by
  explode_step h
  assumption
  done

-- explode_step is a best-effort tactic. It creates new hypotheses until it
-- encounters an unsupported term (i.e., `if` in the example below).
-- TODO:
--  Force a case-split if an `if` with a symbolic test is encountered?
--  Simp/ground if an `if` with a concrete test is encountered?
example (s0 s1 : ArmState)
  (h : s1 = w (StateField.GPR 31#5) 12#64 (if (1 = 1) then (w StateField.PC 0x2000#64 s0) else (w StateField.PC 0x2001#64 s0))) :
  r StateField.PC s1 = 0x2000#64 := by
  -- explode_step h
  simp at h
  explode_step h
  assumption
  done

-- explode_step adds hypotheses in the outside-in order for the RHS of `h`. It
-- does not add a hypothesis for a field if it was already seen earlier. That is
-- why we do not see two hypotheses for (StateField.GPR 31#5) below; we only see
-- one hypothesis that corresponds to the most recent write.
example (s0 s1 : ArmState)
  (h : s1 = w (StateField.GPR 31#5) 12#64
              (w StateField.PC 1#64
                (w (StateField.GPR 31#5) 13#64 s0))) :
  r StateField.PC s1 = 1#64 := by
  explode_step h
  assumption
  done
