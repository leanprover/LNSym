import Lean
import Arm.Map
import Arm.Decode
import Tactics.Common
import Tactics.Simp
import Tactics.ChangeHyps
open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Command

-- NOTE: This is an experimental and probably quite shoddy method of autogenerating
-- `stepi` theorems from a program under verification, and things may change
-- without warning in the near future.

/-
Command to autogenerate fetch, decode, execute, and stepi theorems for
a given program.
Invocation:
#genStepTheorems <program_map>
                  thmType:="fetch" | "decodeExec" | "step"
                  <simpExtension>

The theorems are generated with the prefix `<prefix>` and are added to the
`simpExtension` simp set (typically, `state_simp_rules`). The `thmType` value
determines the kind of theorem being generated -- note that decode and execute
theorems are generated in one swoop ("decodeExec").

See the end of this file for an example.
-/


/- When true, prints the names of the generated theorems. -/
initialize registerTraceClass `gen_step.print_names
/- When true, prints debugging information. -/
initialize registerTraceClass `gen_step.debug
/- When true, prints the number of heartbeats taken per theorem. -/
initialize registerTraceClass `gen_step.debug.heartBeats

/- Generate and prove a fetch theorem of the following form:
```
theorem (<thm_prefix> ++ "fetch_0x" ++ <address_str>) (s : ArmState)
 (h : s.program = <orig_map>) : fetch_inst <address_expr> s = some <raw_inst_expr>
```
-/
def genFetchTheorem (program_name : Name) (address_str : String)
  (orig_map address_expr raw_inst_expr : Expr)
  : MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genFetchTheorem] Start heartbeats: {startHB}"
  let declName := Name.str program_name ("fetch_0x" ++ address_str)
  let s_program_hyp_fn :=
      fun s => -- (s.program = <orig_map>)
         (mkAppN (mkConst ``Eq [1])
                    #[(mkConst ``Program),
                      (mkAppN (mkConst ``ArmState.program) #[s]),
                      orig_map])
  let fetch_inst_fn := fun s => -- (fetch_inst <address_expr> <s>)
                        (mkAppN (mkConst ``fetch_inst) #[address_expr, s])
  let bitvec32 := (mkAppN (mkConst ``BitVec) #[mkRawNatLit 32])
  let opt_bitvec32 := (mkAppN (mkConst ``Option [0]) #[bitvec32])
  let raw_inst_rhs := (mkAppN (mkConst ``Option.some [0]) #[bitvec32, raw_inst_expr])
  let orig_thm := -- ∀ (s : ArmState), (h : s.program = <orig_map>) :
                  --      fetch_inst <address_expr> s = some <raw_inst_expr>
                forallE `s (mkConst ``ArmState)
                  (forallE (Name.mkSimple "h")
                    (s_program_hyp_fn (bvar 0))
                      (mkAppN (mkConst ``Eq [1])
                        #[opt_bitvec32, (fetch_inst_fn (bvar 1)), raw_inst_rhs])
                Lean.BinderInfo.default)
               Lean.BinderInfo.default
  trace[gen_step.debug] "[genFetchTheorem] Statement of the theorem: {orig_thm}"
  withLocalDeclD `s (mkConst ``ArmState) fun s => do
    withLocalDeclD `h (s_program_hyp_fn s) fun _h => do
    let lhs := fetch_inst_fn s
    trace[gen_step.debug] "[genFetchTheorem] lhs: {lhs}"
    let (ctx, simprocs) ← LNSymSimpContext (config := {ground := false})
                            (simp_attrs := #[`minimal_theory])
                            (thms := #[``fetch_inst_from_program])
                            (simprocs := #[``reduceMapFind?])
    -- Adding local declarations to the context.
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      trace[gen_step.debug] "[genFetchTheorem] Prop. in Local Context: {← h.getType}"
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := { ctx with simpTheorems }
    let (result, _) ← simp lhs ctx simprocs
    trace[gen_step.debug] "[genFetchTheorem] Simp result: result: {result.expr}"
    trace[gen_step.debug] "[genFetchTheorem] result.proof?: {result.proof?}"
    -- FIXME: Is this DefEq check necessary?
    -- if ! (← isDefEq result.expr raw_inst_rhs) then
    --   throwError "[genFetchTheorem] {lhs} simplified to {result.expr}, which is not \
    --                the expected term, {raw_inst_rhs}"
    -- Why do we need to add s explicitly here?
    let args := #[s] ++ (hs.map (fun f => (.fvar f)))
    let value ← mkLambdaFVars args result.proof?.get! (usedOnly := true) (usedLetOnly := true)
    trace[gen_step.debug] "[genFetchTheorem] Proof: {value}"
    let decl := Declaration.thmDecl {
      name := declName,
      -- TODO: Compute levelParams instead of hard-coding it?
      levelParams := [],
      type := orig_thm,
      value := value
    }
    addDecl decl
    -- addAndCompile decl
    trace[gen_step.print_names] "[Proved theorem {declName}.]"
    let stopHB ← IO.getNumHeartbeats
    trace[gen_step.debug.heartBeats] "[genFetchTheorem]: Stop heartbeats: {stopHB}"
    trace[gen_step.debug.heartBeats] "[genFetchTheorem]: HeartBeats used: {stopHB - startHB}"

/- Generate and prove an exec theorem of the following form:
```
theorem (<thm_prefix> ++ "exec_0x" ++ <address_str>) (s : ArmState) :
  exec_inst <decoded_inst> s = <simplified_semantics>
```
-/
def genExecTheorem (program_name : Name) (address_str : String)
    (decoded_inst : Expr) : MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genExecTheorem] Start heartbeats: {startHB}"
  let declName := Name.str program_name ("exec_0x" ++ address_str)
  withLocalDeclD `s (mkConst ``ArmState) fun s => do
    let exec_inst_expr := (mkAppN (mkConst ``exec_inst) #[decoded_inst, s])
    trace[gen_step.debug] "[Exec_inst Expression: {exec_inst_expr}]"
    -- let sp_aligned ← (mkAppM ``Eq #[(← mkAppM ``CheckSPAlignment #[s]), (mkConst ``true)])
    -- logInfo m!"sp_aligned: {sp_aligned}"
    -- withLocalDeclD `h_sp_aligned sp_aligned fun _h_sp_aligned => do
    let (ctx, _simprocs) ←
            LNSymSimpContext
              -- Unfortunately, using `ground := true` exposes a lot of internal BitVec
              -- structure in terms of Fin.
              (config := {decide := true, ground := false})
              (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
              (decls_to_unfold := #[``exec_inst])
    -- Adding local declarations to the context.
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      trace[gen_step.debug] "[genExecTheorem] Prop. in Local Context: {← h.getType}"
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := { ctx with simpTheorems }
    let (exec_inst_result, _) ← simp exec_inst_expr ctx
    trace[gen_step.debug] "[Exec_inst Simplified Expression: {exec_inst_result.expr}]"
    let hs ← getPropHyps
    let args := #[s] ++ (hs.map (fun f => (.fvar f)))
    let thm ← mkAppM ``Eq #[exec_inst_expr, exec_inst_result.expr]
    let type ← mkForallFVars args thm -- (usedOnly := true) (usedLetOnly := false)
    trace[gen_step.debug] "[Exec_inst Theorem: {type}.]"
    let value ← mkLambdaFVars args exec_inst_result.proof?.get!
                    -- (usedOnly := true) (usedLetOnly := false)
    let decl := Declaration.thmDecl
                -- TODO: Compute levelParams instead of hard-coding it?
                { name := declName, levelParams := [],
                  type := type, value := value }
    addDecl decl
    trace[gen_step.print_names] "[Proved theorem {declName}.]"
    let stopHB ← IO.getNumHeartbeats
    trace[gen_step.debug.heartBeats] "[genExecTheorem]: Stop heartbeats: {stopHB}"
    trace[gen_step.debug.heartBeats] "[genExecTheorem]: HeartBeats used: {stopHB - startHB}"

/- Generate and prove a decode theorem of the following form:
```
theorem (<thm_prefix> ++ "decode_0x" ++ <address_str>) (s : ArmState) :
  decode_raw_inst <raw_inst> = <computed_decoded_inst>
```

The <computed_decoded_inst> is then used as an input to `genExecTheorem` to generate
an exec theorem.
-/
def genDecodeAndExecTheorems (program_name : Name) (address_str : String)
  (raw_inst : Expr) :
  MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genDecodeTheorem] Start heartbeats: {startHB}"
  let declName := Name.str program_name ("decode_0x" ++ address_str)
  let lhs := (mkAppN (Expr.const ``decode_raw_inst []) #[raw_inst])
  -- reduce and whnfD do too much and expose the internal Fin structure of the
  -- BitVecs below. whnfR does not do enough and leaves the decode_raw_inst term
  -- unsimplified. So we use simp for this simplification.
  -- let rhs ← reduce lhs -- whnfD or whnfR?
  let (ctx, _simprocs) ← LNSymSimpContext (config := {ground := true})
  let (rhs, _) ← simp lhs ctx
  let opt_arminst := (mkAppN (mkConst ``Option [0]) #[(mkConst ``ArmInst [])])
  let type := mkAppN (Expr.const ``Eq [1]) #[opt_arminst, lhs, rhs.expr]
  let value := mkAppN (Expr.const ``Eq.refl [1]) #[opt_arminst, lhs]
  let decl := Declaration.thmDecl {
    name := declName,
    -- TODO: Compute levelParams instead of hard-coding it?
    levelParams := [],
    type := type,
    value := value
  }
  addDecl decl
  trace[gen_step.print_names] "[Proved theorem {declName}.]"
  let_expr Option.some _ decoded_inst ← rhs.expr |
    throwError "[genDecodeTheorem] Instruction {raw_inst} could not be decoded!"
  let stopHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genDecodeTheorem]: Stop heartbeats: {stopHB}"
  trace[gen_step.debug.heartBeats] "[genDecodeTheorem]: HeartBeats used: {stopHB - startHB}"
  genExecTheorem program_name address_str decoded_inst

/- Generate and prove a step theorem, using pre-existing fetch, decode, and exec
theorems. The step theorem looks like the following:
```
theorem (<thm_prefix> ++ "stepi_0x" ++ <address_str>) (s sn : ArmState)
  (h_program : s.program = <orig_map>)
  (h_pc : r StateField.PC s = <address_expr>)
  (h_err : r StateField.ERR s = StateError.None) :
  (sn = stepi s) =
  (sn = <simplified_semantics>)
```
-/
def genStepTheorem (program_name : Name) (address_str : String)
  (orig_map address_expr : Expr) (simpExt : Option Name) : MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genStepTheorem] Start heartbeats: {startHB}"
  let declName := Name.str program_name ("stepi_0x" ++ address_str)
  let s_program_hyp_fn :=
      fun s => -- (s.program = <orig_map>)
        (mkAppN (mkConst ``Eq [1])
                #[(mkConst ``Program),
                  (mkAppN (mkConst ``ArmState.program) #[s]),
                  orig_map])
  let bitvec64 := (mkAppN (mkConst ``BitVec) #[mkRawNatLit 64])
  let s_pc_hyp_fn :=
      fun s => -- (r StateField.PC s = <address_expr>)
        (mkAppN (Expr.const ``Eq [1])
                #[bitvec64,
                  (mkAppN (Expr.const ``r []) #[mkConst ``StateField.PC, s]),
                  address_expr])
  let s_err_hyp_fn :=
      fun s => -- (r StateField.ERR s = StateError.None)
        (mkAppN (Expr.const ``Eq [1])
                #[mkConst ``StateError,
                 (mkAppN (Expr.const ``r []) #[mkConst ``StateField.ERR, s]),
                 (mkConst ``StateError.None)])
  let stepi_fn := fun sn s => -- (sn = stepi s)
      (mkAppN (mkConst ``Eq [1])
              #[mkConst ``ArmState, sn, (mkAppN (mkConst ``stepi) #[s])])
  let helper_thms :=
      -- We assume that the necessary fetch, decode, and exec theorems already exist.
      Array.map
        (fun str => Name.str program_name (str ++ address_str))
        #["fetch_0x", "decode_0x", "exec_0x"]
  withLocalDeclD `sn (mkConst ``ArmState) fun sn => do
  withLocalDeclD `s (mkConst ``ArmState) fun s => do
  withLocalDeclD `h_program (s_program_hyp_fn s) fun _h_program => do
  withLocalDeclD `h_pc (s_pc_hyp_fn s) fun _h_program => do
  withLocalDeclD `h_err (s_err_hyp_fn s) fun _h_err => do
    let lhs := stepi_fn sn s
    trace[gen_step.debug] "[genStepTheorem] lhs: {lhs}"
    let (ctx, simprocs) ← LNSymSimpContext (config := {ground := false, decide := false})
                            (simp_attrs := #[`minimal_theory, `bitvec_rules])
                            (decls_to_unfold := #[``stepi, ``read_pc, ``read_err])
                            (thms := helper_thms)
                            (simprocs := #[])
    -- Adding local declarations to the context.
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      trace[gen_step.debug] "[genStepTheorem] Prop. in Local Context: {← h.getType}"
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := { ctx with simpTheorems }
    let (result, _) ← simp lhs ctx simprocs
    trace[gen_step.debug] "[genStepTheorem] Simp result: result: {result.expr}"
    trace[gen_step.debug] "[genStepTheorem] result.proof?: {result.proof?}"
    -- Why do we need to add s explicitly here?
    let args := #[s, sn] ++ (hs.map (fun f => (.fvar f)))
    let thm ← mkAppM ``Eq #[lhs, result.expr]
    -- let (_, changed_expr, unchanged_expr) ← getChangedUnchangedExprs result.expr
    -- let thm ← mkAppM ``Iff #[lhs, (mkAnd changed_expr unchanged_expr)]
    let type ← mkForallFVars args thm -- (usedOnly := true) (usedLetOnly := false)
    trace[gen_step.debug] "[genStepTheorem] type: {type}"
    let value ← mkLambdaFVars args result.proof?.get! (usedOnly := true) (usedLetOnly := true)
    trace[gen_step.debug] "[genStepTheorem] Proof: {value}"
    let decl := Declaration.thmDecl {
      name := declName,
      -- TODO: Compute levelParams instead of hard-coding it?
      levelParams := [],
      type := type,
      value := value -- (← mkSorry type (synthetic := true))
    }
    addDecl decl
    -- Unlike the fetch, decode, and exec theorems, which we view as ephemeral,
    -- the step theorems are added to the simpset `simpExt`.
    -- TODO: We should erase the fetch, decode, and exec theorems once we
    -- prove the corresponding step theorem.
    if simpExt.isSome then
      addToSimpExt declName simpExt.get!
    trace[gen_step.print_names] "[Proved theorem {declName}.]"
    let stopHB ← IO.getNumHeartbeats
    trace[gen_step.debug.heartBeats] "[genStepTheorem]: Stop heartbeats: {stopHB}"
    trace[gen_step.debug.heartBeats] "[genStepTheorem]: HeartBeats used: {stopHB - startHB}"

partial def genStepTheorems (program map : Expr) (program_name : Name)
  (thm_type : String) (simpExt : Option Name) : MetaM Unit := do
  trace[gen_step.debug] "[genStepTheorems: Poised to run whnfD on the map: {map}]"
  let map ← whnfD map
  trace[gen_step.debug] "[genStepTheorems: after whnfD: {map}]"
  match_expr map with
  | List.cons _ hd tl =>
    let hd ← whnfD hd
    let_expr Prod.mk _ _ address_expr raw_inst_expr ← hd |
      throwError "Unexpected program map entry! {hd}"
    let address_expr ← whnfR address_expr -- whnfR vs whnfD?
    let raw_inst_expr ← whnfR raw_inst_expr
    let some address_string ← getBitVecString? address_expr (hex := true)
      | throwError "We expect program addresses to be concrete. \
                  Found this instead: {address_expr}."
    trace[gen_step.debug] "[genStepTheorems: address_expr {address_expr} \
                              raw_inst_expr {raw_inst_expr}]"
    if thm_type == "fetch" then
      genFetchTheorem program_name address_string program address_expr raw_inst_expr
    if thm_type == "decodeExec" then
      genDecodeAndExecTheorems program_name address_string raw_inst_expr
    if thm_type == "step" then
      genStepTheorem program_name address_string program address_expr simpExt
    genStepTheorems program tl program_name thm_type simpExt
  | List.nil _ => return
  | _ =>
    throwError "Unexpected program map term! {map}"

-- TODO:
-- The arguments of this command are pretty clunky. For instance, they are sort
-- of named, but we still expect them to appear in the same order.
-- Also, it'd be nice to not have `thmType` as a string, but an inductive type
-- of legal values.
-- Maybe elaborate a StepTheorems object here? See, e.g., declare_config_elab.
elab "#genStepTheorems " arg:term
                        "thmType:="thmType:str
                        ext:(name)? : command => liftTermElabM do
  let ty := mkConst `Program []
  let arg ← Term.elabTermAndSynthesize arg ty
  let arg ← Term.ensureHasType ty arg

  -- Abort if there are any metavariables or free variables in arg.
  if arg.hasExprMVar || arg.hasFVar then
    throwError "No meta-variable(s) or free variable(s) allowed in arg: {arg}"
  else
    let .const program_name _ := arg
      | throwError "Expected a constant, found:\n\t{arg}

Tip: you can always introduce an abbreviation, as in:
\tabbrev myProgram : Program := {arg}"

    genStepTheorems arg arg program_name thmType.getString
      (if ext.isSome then ext.get!.getName else Option.none)

-----------------------------------------------------------------------------

section StepThmsExample

def test_program : Program :=
  def_program
  [(0x12650c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
    (0x126510#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
    (0x126514#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
    (0x126518#64 , 0x4ea31c7d#32)]      --  mov     v29.16b, v3.16b

#genStepTheorems test_program thmType:="fetch"
/--
info: test_program.fetch_0x126510 (s : ArmState) (h : s.program = test_program) :
  fetch_inst (1205520#64) s = some 1319181371#32
-/
#guard_msgs in
#check test_program.fetch_0x126510

#genStepTheorems test_program thmType:="decodeExec"
/--
info: test_program.decode_0x126510 :
  decode_raw_inst 1319181371#32 =
    some
      (ArmInst.DPSFP
        (DataProcSFPInst.Advanced_simd_three_same
          { _fixed1 := 0#1, Q := 1#1, U := 0#1, _fixed2 := 14#5, size := 2#2, _fixed3 := 1#1, Rm := 1#5, opcode := 3#5,
            _fixed4 := 1#1, Rn := 1#5, Rd := 27#5 }))
-/
#guard_msgs in
#check test_program.decode_0x126510

/--
info: test_program.exec_0x126510 (s : ArmState) :
  exec_inst
      (ArmInst.DPSFP
        (DataProcSFPInst.Advanced_simd_three_same
          { _fixed1 := 0#1, Q := 1#1, U := 0#1, _fixed2 := 14#5, size := 2#2, _fixed3 := 1#1, Rm := 1#5, opcode := 3#5,
            _fixed4 := 1#1, Rn := 1#5, Rd := 27#5 }))
      s =
    w StateField.PC (r StateField.PC s + 4#64) (w (StateField.SFP 27#5) (r (StateField.SFP 1#5) s) s)
-/
#guard_msgs in
#check test_program.exec_0x126510

#genStepTheorems test_program thmType:="step" `state_simp_rules
/--
info: test_program.stepi_0x126510 (s sn : ArmState) (h_program : s.program = test_program)
  (h_pc : r StateField.PC s = 1205520#64) (h_err : r StateField.ERR s = StateError.None) :
  (sn = stepi s) = (sn = w StateField.PC (1205524#64) (w (StateField.SFP 27#5) (r (StateField.SFP 1#5) s) s))
-/
#guard_msgs in
#check test_program.stepi_0x126510

-- Here's the theorem that we'd actually like to obtain instead of the
-- erstwhile test_stepi_0x126510.
theorem test_stepi_0x126510_desired (s sn : ArmState)
  (h_program : s.program = test_program)
  (h_pc : r StateField.PC s = 1205520#64)
  (h_err : r StateField.ERR s = StateError.None)
  (h_step : sn = stepi s) :
  -- Effects
  (r (StateField.SFP 27#5) sn = r (StateField.SFP 1#5) s) ∧
  (r StateField.PC sn = 1205524#64) ∧
  -- Non-Effects
  (∀ (f : StateField), f ≠ StateField.PC ∧ f ≠ StateField.SFP 27#5 → r f sn = r f s) ∧
  (∀ (n : Nat) (addr : BitVec 64), read_mem_bytes n addr sn = read_mem_bytes n addr s) := by
  simp_all only [minimal_theory, state_simp_rules, bitvec_rules, test_program.stepi_0x126510]
  done

end StepThmsExample

-----------------------------------------------------------------------------
