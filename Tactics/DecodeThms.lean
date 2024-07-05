import Lean
import Arm.Map
import Arm.Decode
import Tactics.Common
open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-
Command to autogenerate decode theorems for a given program. Invocation:
genDecodeTheorems <program_map>

Each generated theorem looks like the following, where the name of the theorem
is "decode_<address>".

theorem decode_0x4ea31c7d :
  decode_raw_inst 0x4ea31c7d#32 = some (ArmInst.DPSFP
  (DataProcSFPInst.Advanced_simd_three_same
    { _fixed1 := 0x0#1,
      Q := 0x1#1,
      U := 0x0#1,
      _fixed2 := 0x0e#5,
      size := 0x2#2,
      _fixed3 := 0x1#1,
      Rm := 0x03#5,
      opcode := 0x03#5,
      _fixed4 := 0x1#1,
      Rn := 0x03#5,
      Rd := 0x1d#5 })) := by
      rfl

-/

/- When true, prints the names of the generated theorems. -/
initialize registerTraceClass `gen_decode.print_names
/- When true, prints debugging information. -/
initialize registerTraceClass `gen_decode.debug

def addToSimpExt (declName : Name) (simp_ext : Name) : MetaM Unit := do
  let some ext ← getSimpExtension? simp_ext |
    throwError "Simp Extension [simp_ext] not found!"
  addSimpTheorem ext declName false false Lean.AttributeKind.global default

syntax "define_fetch_thm " ident "program :=" term "address :=" term "raw_inst :=" term: command
macro_rules
  | `(define_fetch_thm $name:ident program :=$program:term address :=$address:term raw_inst :=$raw_inst) =>
    `(theorem $name (s : ArmState) (h : s.program = $program) :
        (fetch_inst $address s = $raw_inst) := by
          simp only [h, fetch_inst_from_program, reduceMapFind?])

def genFetchTheorem (name : String) (program : Term) (address : Expr) (raw_inst : Expr) (simp_ext : Name) :
  MetaM Unit := do
  let declName := Lean.Name.mkSimple name
  let address_term ← Lean.PrettyPrinter.delab address
  let raw_inst_term ← Lean.PrettyPrinter.delab raw_inst
  liftCommandElabM <| Elab.Command.elabCommand <|
    ← `(define_fetch_thm $(mkIdent declName) program := $program address := $address_term raw_inst := $raw_inst_term)
  addToSimpExt declName simp_ext
  trace[gen_decode.print_names] "[Proved theorem {declName}.]"

def genDecodeTheorem (name : String) (raw_inst : Expr) (simp_ext : Name) :
  MetaM Unit := do
  let declName := Lean.Name.mkSimple name
  let lhs := (mkAppN (Expr.const ``decode_raw_inst []) #[raw_inst])
  let rhs ← reduce lhs -- whnfD?
  let opt_arminst := (mkAppN (mkConst ``Option [0]) #[(mkConst ``ArmInst [])])
  let type := mkAppN (Expr.const ``Eq [1]) #[opt_arminst, lhs, rhs]
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

partial def genDecodeTheoremsForMap (program : Term) (map : Expr) (thm_prefix : String) (simp_ext : Name) : MetaM Unit := do
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
    -- let fetch_name := thm_prefix ++ "fetch_0x" ++ address_str.get!
    let decode_name := thm_prefix ++ "decode_0x" ++ address_str.get!
    trace[gen_decode.debug] "[genDecodeTheoremsForMap: \n
                                address_expr {address_expr} \n
                                raw_inst_expr {raw_inst_expr}]"
    -- genFetchTheorem fetch_name program address_expr raw_inst_expr simp_ext
    genDecodeTheorem decode_name raw_inst_expr simp_ext
    genDecodeTheoremsForMap program tl thm_prefix simp_ext
  | List.nil _ => return
  | _ =>
    throwError s!"Unexpected program map term! {map}"

elab "#genDecodeTheorems " arg:term "namePrefix:="thmPrefix:str "simpExt:="ext:name : command => liftTermElabM do
  let arg_term := arg
  let arg ← Term.elabTermAndSynthesize arg none
  -- Abort if there are any metavariables or free variables in arg.
  if arg.hasExprMVar || arg.hasFVar then
    throwError "No meta-variable(s) or free variable(s) allowed in arg: {arg}"
  else
    let arg_typ ← inferType arg
    if (arg_typ != (mkConst `Program [])) then
        throwError "Arg {arg} expected to be of type Program, but instead it is: {arg_typ}"
    genDecodeTheoremsForMap arg_term arg thmPrefix.getString ext.getName
