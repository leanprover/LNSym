import Lean
import Arm.Map
import Arm.Decode
import Tactics.Common
import Tactics.Simp
import Tactics.ChangeHyps
open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Command

/-
Command to autogenerate fetch and decode theorems for a given program.
Invocation:
`#genStepTheorems <program_map> namePrefix:=<prefix> simpExt:=<simpExtension>`

The theorems are generated with the prefix `<prefix>` and are added to the
`simpExtension` simp set (typically, `state_simp_rules`).

For example, `#genStepTheorems` generates and proves the following two
theorems for the instruction at address `0x1264e8` of the program
`sha512_program_map` (see `Tests.SHA2.SHA512ProgramTest`):

```
sha512_fetch_0x1264e8 (s : ArmState) (h : s.program = sha512_program_map) :
   fetch_inst (1205480#64) s = some 1310722675#32

sha512_decode_0x1264e8 :
  decode_raw_inst 1310722675#32 =
    some
      (ArmInst.DPSFP
        (DataProcSFPInst.Advanced_simd_two_reg_misc
          { _fixed1 := 0#1, Q := 1#1, U := 0#1, _fixed2 := 14#5, size := 0#2, _fixed3 := 16#5, opcode := 0#5,
            _fixed4 := 2#2, Rn := 19#5, Rd := 19#5 }))
```
-/

/- When true, prints the names of the generated theorems. -/
initialize registerTraceClass `gen_step.print_names
/- When true, prints debugging information. -/
initialize registerTraceClass `gen_step.debug
/- When true, prints the number of heartbeats taken per theorem. -/
initialize registerTraceClass `gen_step.debug.heartBeats

def genFetchTheorem (thm_prefix address_str : String) (orig_map address_expr raw_inst_expr : Expr)
  : MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genFetchTheorem] Start heartbeats: {startHB}"
  let name := thm_prefix ++ "fetch_0x" ++ address_str
  let declName := Lean.Name.mkSimple name
  let s_program_hyp_fn :=
      fun s =>  (mkAppN (mkConst ``Eq [1])
                        #[(mkConst ``Program),
                          (mkAppN (mkConst ``ArmState.program) #[s]),
                          orig_map])
  let fetch_inst_fn := fun s => (mkAppN (mkConst ``fetch_inst) #[address_expr, s])
  let bitvec32 := (mkAppN (mkConst ``BitVec) #[mkRawNatLit 32])
  let opt_bitvec32 := (mkAppN (mkConst ``Option [0]) #[bitvec32])
  let raw_inst_rhs := (mkAppN (mkConst ``Option.some [0]) #[bitvec32, raw_inst_expr])
  let orig_thm := forallE `s (mkConst ``ArmState)
              (forallE (Name.mkSimple "h")
                -- s.program = <orig_map>
                (s_program_hyp_fn (bvar 0))
                -- (fetch_inst <address_expr> s = <raw_inst_rhs>)
                  (mkAppN (mkConst ``Eq [1])
                   #[opt_bitvec32, (fetch_inst_fn (bvar 1)), raw_inst_rhs])
                Lean.BinderInfo.default)
               Lean.BinderInfo.default
  trace[gen_step.debug] "[genFetchTheorem] Statement of the theorem: {orig_thm}"
  withLocalDeclD `s (mkConst ``ArmState) fun s => do
    withLocalDeclD `h (mkAppN (mkConst ``Eq [1])
                        #[(mkConst ``Program),
                          (mkAppN (mkConst ``ArmState.program) #[s]),
                          orig_map]) fun _h => do
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
      levelParams := [],
      type := orig_thm,
      value := value
    }
    addDecl decl
    -- addAndCompile decl
    -- addToSimpExt declName simp_ext
    trace[gen_step.print_names] "[Proved theorem {declName}.]"
    let stopHB ← IO.getNumHeartbeats
    trace[gen_step.debug.heartBeats] "[genFetchTheorem]: Stop heartbeats: {stopHB}"
    trace[gen_step.debug.heartBeats] "[genFetchTheorem]: HeartBeats used: {stopHB - startHB}"

def genExecTheorem (thm_prefix address_str : String) (decoded_inst : Expr) : MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genExecTheorem] Start heartbeats: {startHB}"
  let name := thm_prefix ++ "exec_0x" ++ address_str
  let declName := Lean.Name.mkSimple name
  withLocalDeclD `s (mkConst ``ArmState) fun s => do
    let exec_inst_expr := (mkAppN (mkConst ``exec_inst) #[decoded_inst, s])
    trace[gen_step.debug] "[Exec_inst Expression: {exec_inst_expr}]"
    -- let sp_aligned ← (mkAppM ``Eq #[(← mkAppM ``CheckSPAlignment #[s]), (mkConst ``true)])
    -- logInfo m!"sp_aligned: {sp_aligned}"
    -- withLocalDeclD `h_sp_aligned sp_aligned fun _h_sp_aligned => do
    let (ctx, _simprocs) ←
            LNSymSimpContext
              (config := {decide := true})
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
                { name := declName, levelParams := [],
                  type := type, value := value }
    addDecl decl
    -- addAndCompile decl
    -- addToSimpExt declName simp_ext
    trace[gen_step.print_names] "[Proved theorem {declName}.]"
    let stopHB ← IO.getNumHeartbeats
    trace[gen_step.debug.heartBeats] "[genExecTheorem]: Stop heartbeats: {stopHB}"
    trace[gen_step.debug.heartBeats] "[genExecTheorem]: HeartBeats used: {stopHB - startHB}"

def genDecodeAndExecTheorems (thm_prefix address_str : String) (raw_inst : Expr) :
  MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genDecodeTheorem] Start heartbeats: {startHB}"
  let name := thm_prefix ++ "decode_0x" ++ address_str
  let declName := Lean.Name.mkSimple name
  let lhs := (mkAppN (Expr.const ``decode_raw_inst []) #[raw_inst])
  -- let rhs ← reduce lhs -- whnfD?
  let (ctx, _simprocs) ← LNSymSimpContext (config := {ground := true})
  let (rhs, _) ← simp lhs ctx
  let opt_arminst := (mkAppN (mkConst ``Option [0]) #[(mkConst ``ArmInst [])])
  let type := mkAppN (Expr.const ``Eq [1]) #[opt_arminst, lhs, rhs.expr]
  let value := mkAppN (Expr.const ``Eq.refl [1]) #[opt_arminst, lhs]
  let decl := Declaration.thmDecl {
    name := declName,
    levelParams := [],
    type := type,
    value := value
  }
  addDecl decl
  -- addAndCompile decl
  -- addToSimpExt declName simp_ext
  trace[gen_step.print_names] "[Proved theorem {declName}.]"
  let_expr Option.some _ decoded_inst ← rhs.expr |
    throwError "[genDecodeTheorem] Instruction {raw_inst} could not be decoded!"
  let stopHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genDecodeTheorem]: Stop heartbeats: {stopHB}"
  trace[gen_step.debug.heartBeats] "[genDecodeTheorem]: HeartBeats used: {stopHB - startHB}"
  genExecTheorem thm_prefix address_str decoded_inst

def genStepTheorem (thm_prefix address_str : String)
  (orig_map address_expr : Expr) (simpExt : Name) : MetaM Unit := do
  let startHB ← IO.getNumHeartbeats
  trace[gen_step.debug.heartBeats] "[genStepTheorem] Start heartbeats: {startHB}"
  let name := thm_prefix ++ "stepi_0x" ++ address_str
  let declName := Lean.Name.mkSimple name
  let s_program_hyp_fn :=
      fun s =>  (mkAppN (mkConst ``Eq [1])
                        #[(mkConst ``Program),
                          (mkAppN (mkConst ``ArmState.program) #[s]),
                          orig_map])
  let bitvec64 := (mkAppN (mkConst ``BitVec) #[mkRawNatLit 64])
  let s_pc_hyp_fn :=
      fun s => (mkAppN (Expr.const ``Eq [1])
                          #[bitvec64,
                             (mkAppN (Expr.const ``r []) #[mkConst ``StateField.PC, s]),
                          address_expr])
  let s_err_hyp_fn :=
      fun s => (mkAppN (Expr.const ``Eq [1])
                          #[mkConst ``StateError,
                             (mkAppN (Expr.const ``r []) #[mkConst ``StateField.ERR, s]),
                          (mkConst ``StateError.None)])
  let stepi_fn := fun sn s =>
      (mkAppN (mkConst ``Eq [1])
          #[mkConst ``ArmState, sn, (mkAppN (mkConst ``stepi) #[s])])
  let helper_thms :=
      Array.map
        (fun str => Lean.Name.mkSimple (thm_prefix ++ str ++ address_str))
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
      levelParams := [],
      type := type,
      value := value -- (← mkSorry type (synthetic := true))
    }
    addDecl decl
    -- addAndCompile decl
    addToSimpExt declName simpExt
    trace[gen_step.print_names] "[Proved theorem {declName}.]"
    let stopHB ← IO.getNumHeartbeats
    trace[gen_step.debug.heartBeats] "[genStepTheorem]: Stop heartbeats: {stopHB}"
    trace[gen_step.debug.heartBeats] "[genStepTheorem]: HeartBeats used: {stopHB - startHB}"

partial def genStepTheorems (program map : Expr) (thm_prefix : String)
  (thmType : String) (simp_ext : Name) : MetaM Unit := do
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
    let address_str ← getBitVecString? address_expr (hex := true)
    if address_str.isNone then
      throwError "We expect program addresses to be concrete. \
                  Found this instead: {address_expr}."
    let address_string := address_str.get!
    trace[gen_step.debug] "[genStepTheorems: address_expr {address_expr} \
                              raw_inst_expr {raw_inst_expr}]"
    if thmType == "fetch" then
      genFetchTheorem thm_prefix address_string program address_expr raw_inst_expr
    if thmType == "decodeExec" then
      genDecodeAndExecTheorems thm_prefix address_string raw_inst_expr
    if thmType == "step" then
      genStepTheorem thm_prefix address_string program address_expr simp_ext
    genStepTheorems program tl thm_prefix thmType simp_ext
  | List.nil _ => return
  | _ =>
    throwError s!"Unexpected program map term! {map}"

elab "#genStepTheorems " arg:term "namePrefix:="thmPrefix:str "thmType:="thmType:str "simpExt:="ext:name : command => liftTermElabM do
  let arg ← Term.elabTermAndSynthesize arg none
  -- Abort if there are any metavariables or free variables in arg.
  if arg.hasExprMVar || arg.hasFVar then
    throwError "No meta-variable(s) or free variable(s) allowed in arg: {arg}"
  else
    let arg_typ ← inferType arg
    if (arg_typ != (mkConst `Program [])) then
        throwError "Arg {arg} expected to be of type Program, but instead it is: {arg_typ}"
    genStepTheorems arg arg thmPrefix.getString thmType.getString ext.getName

/-
def test_program : Program :=
  def_program
  [(0x12650c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
    (0x126510#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
    (0x126514#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
    (0x126518#64 , 0x4ea31c7d#32)]      --  mov     v29.16b, v3.16b

#genStepTheorems test_program namePrefix:="test_" thmType:="fetch" simpExt:=`state_simp_rules
#check test_fetch_0x126510

#genStepTheorems test_program namePrefix:="test_" thmType:="decodeExec" simpExt:=`state_simp_rules
#check test_decode_0x126510
#check test_exec_0x126510

#genStepTheorems test_program namePrefix:="test_" thmType:="step" simpExt:=`state_simp_rules
#check test_stepi_0x126510

#print test_stepi_0x126510

theorem bar_test_stepi_0x126510 (s sn : ArmState)
  (h_program : s.program = test_program)
  (h_pc : r StateField.PC s = 1205520#64)
  (h_err : r StateField.ERR s = StateError.None) :
  (sn = stepi s) ↔
    ((r (StateField.SFP 27#5) sn = r (StateField.SFP 1#5) s ∧ r StateField.PC sn = 1205524#64) ∧
      ∀ (f : StateField), f ≠ StateField.PC ∧ f ≠ StateField.SFP 27#5 → r f sn = r f s) := by
  simp only [*, stepi, read_err, read_pc, minimal_theory,
             test_fetch_0x126510, test_decode_0x126510, test_exec_0x126510]
  sorry



theorem foo (s : ArmState)
  (h_program : s.program = test_program)
  (h_pc : r StateField.PC s = 1205520#64)
  (h_err : r StateField.ERR s = StateError.None) :
  stepi s =
    w StateField.PC (1205524#64) (w (StateField.SFP 27#5) (r (StateField.SFP 1#5) s) s) := by
  simp only [*, stepi, read_err, read_pc, minimal_theory, bitvec_rules,
             test_fetch_0x126510, test_decode_0x126510, test_exec_0x126510]
-/
