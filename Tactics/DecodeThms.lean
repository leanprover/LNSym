import Lean
import Arm.Map
import Arm.Decode
import Tactics.Common
import Tactics.Simp
open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Command

/-
Command to autogenerate fetch and decode theorems for a given program.
Invocation:
`#genDecodeTheorems <program_map> namePrefix:=<prefix> simpExt:=<simpExtension>`

The theorems are generated with the prefix `<prefix>` and are added to the
`simpExtension` simp set (typically, `state_simp_rules`).

For example, `#genDecodeTheorems` generates and proves the following two
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
initialize registerTraceClass `gen_decode.print_names
/- When true, prints debugging information. -/
initialize registerTraceClass `gen_decode.debug
/- When true, prints the number of heartbeats taken per theorem. -/
initialize registerTraceClass `gen_decode.debug.heartBeats

def addToSimpExt (declName : Name) (simp_ext : Name) : MetaM Unit := do
  let some ext ← getSimpExtension? simp_ext |
    throwError "Simp Extension [simp_ext] not found!"
  addSimpTheorem ext declName false false Lean.AttributeKind.global default

def genFetchTheorem (name : String) (orig_map address_expr raw_inst_expr : Expr) (simp_ext : Name) :
  MetaM Unit := do
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
  trace[gen_decode.debug] "[genFetchTheorem] Statement of the theorem: {orig_thm}"
  withLocalDeclD `s (mkConst ``ArmState) fun s => do
    withLocalDeclD `h (mkAppN (mkConst ``Eq [1])
                        #[(mkConst ``Program),
                          (mkAppN (mkConst ``ArmState.program) #[s]),
                          orig_map]) fun _h => do
    let lhs := fetch_inst_fn s
    trace[gen_decode.debug] "[genFetchTheorem] lhs: {lhs}"
    let (ctx, simprocs) ← LNSymSimpContext (config := {ground := false})
                            (simp_attrs := #[`minimal_theory])
                            (thms := #[``fetch_inst_from_program])
                            (simprocs := #[``reduceMapFind?])
    -- Adding local declarations to the context.
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      trace[gen_decode.debug] "[genFetchTheorem] Prop. in Local Context: {← h.getType}"
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := { ctx with simpTheorems }
    let (result, _) ← simp lhs ctx simprocs
    trace[gen_decode.debug] "[genFetchTheorem] Simp result: result: {result.expr}"
    trace[gen_decode.debug] "[genFetchTheorem] result.proof?: {result.proof?}"
    -- FIXME: Is this DefEq check necessary?
    -- if ! (← isDefEq result.expr raw_inst_rhs) then
    --   throwError "[genFetchTheorem] {lhs} simplified to {result.expr}, which is not \
    --                the expected term, {raw_inst_rhs}"
    -- Why do we need to add s explicitly here?
    let args := #[s] ++ (hs.map (fun f => (.fvar f)))
    let value ← mkLambdaFVars args result.proof?.get! (usedOnly := true) (usedLetOnly := true)
    trace[gen_decode.debug] "[genFetchTheorem] Proof: {value}"
    let decl := Declaration.thmDecl {
      name := declName,
      levelParams := [],
      type := orig_thm,
      value := value
    }
    addAndCompile decl
    addToSimpExt declName simp_ext
    trace[gen_decode.print_names] "[Proved theorem {declName}.]"


def genDecodeTheorem (name : String) (raw_inst : Expr) (simp_ext : Name) :
  MetaM Unit := do
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
  addAndCompile decl
  addToSimpExt declName simp_ext
  trace[gen_decode.print_names] "[Proved theorem {declName}.]"

partial def genDecodeTheoremsForMap (program : Expr) (map : Expr) (thm_prefix : String) (simp_ext : Name) : MetaM Unit := do
  trace[gen_decode.debug] "[genDecodeTheoremsForMap: Poised to run whnfD on the map: {map}]"
  let map ← whnfD map
  trace[gen_decode.debug] "[genDecodeTheoremsForMap: after whnfD: {map}]"
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
    let fetch_name := thm_prefix ++ "fetch_0x" ++ address_str.get!
    let decode_name := thm_prefix ++ "decode_0x" ++ address_str.get!
    trace[gen_decode.debug] "[genDecodeTheoremsForMap: address_expr {address_expr} \
                              raw_inst_expr {raw_inst_expr}]"
    let startHB ← IO.getNumHeartbeats
    trace[gen_decode.debug.heartBeats] "Start heartBeats: {startHB}"
    genFetchTheorem fetch_name program address_expr raw_inst_expr simp_ext
    let stopHB ← IO.getNumHeartbeats
    trace[gen_decode.debug.heartBeats] "Heartbeats used for {fetch_name}: {stopHB - startHB}"
    let startHB ← IO.getNumHeartbeats
    genDecodeTheorem decode_name raw_inst_expr simp_ext
    let stopHB ← IO.getNumHeartbeats
    trace[gen_decode.debug.heartBeats] "Heartbeats used for {decode_name}: {stopHB - startHB}"
    trace[gen_decode.debug.heartBeats] "Stop heartBeats: {stopHB}"
    genDecodeTheoremsForMap program tl thm_prefix simp_ext
  | List.nil _ => return
  | _ =>
    throwError s!"Unexpected program map term! {map}"

elab "#genDecodeTheorems " arg:term "namePrefix:="thmPrefix:str "simpExt:="ext:name : command => liftTermElabM do
  let arg ← Term.elabTermAndSynthesize arg none
  -- Abort if there are any metavariables or free variables in arg.
  if arg.hasExprMVar || arg.hasFVar then
    throwError "No meta-variable(s) or free variable(s) allowed in arg: {arg}"
  else
    let arg_typ ← inferType arg
    if (arg_typ != (mkConst `Program [])) then
        throwError "Arg {arg} expected to be of type Program, but instead it is: {arg_typ}"
    genDecodeTheoremsForMap arg arg thmPrefix.getString ext.getName
