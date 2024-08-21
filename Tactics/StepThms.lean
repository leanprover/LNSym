/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Alex Keizer
-/
import Lean
import Arm.Map
import Arm.Decode
import Tactics.Common
import Tactics.Simp
import Tactics.ChangeHyps
import Tactics.Reflect.ProgramInfo

open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Command
open SymContext (h_pc_type h_program_type h_err_type)

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
/- When true, prints the time taken at various steps of generation. -/
initialize registerTraceClass `gen_step.debug.timing

/-- Assuming that `rawInst` is indeed the right result, construct a proof that
  `fetch_inst addr state = some rawInst`
given that `state.program = program` -/
private def fetchLemma (state program h_program : Expr)
    (addr : BitVec 64) (rawInst : BitVec 32) : Expr :=
  let someRawInst := toExpr (some rawInst)
  mkAppN (mkConst ``fetch_inst_eq_of_prgram_eq_of_map_find) #[
    state,
    program,
    toExpr addr,
    someRawInst,
    h_program,
    mkApp2 (.const ``Eq.refl [1])
      (mkApp (.const ``Option [0]) <|
        mkApp (.const ``BitVec []) (toExpr 32))
      someRawInst
  ]

-- /-! ## `reduceDecodeInst` -/

/-- `canonicalizeBitVec e` recursively walks over expression `e` to convert any
occurrences of:
  `BitVec.ofFin w (Fin.mk x _)`
to the canonical form:
  `BitVec.ofNat w x` (i.e., `x#w`)

Such expressions tend to result from using `reduce` or
`simp` with `{ground := true}`.
You can call `canonicalizeBitVec` after these functions to ensure you don't
needlessly expose `BitVec` internal details -/
-- TODO: should this canonicalize to `BitVec.ofNatLt` instead,
--       as the current transformation loses information?
partial def canonicalizeBitVec (e : Expr) : MetaM Expr := do
  match_expr e with
    | BitVec.ofFin w i =>
        let_expr Fin.mk _ x _h := i | fallback
        let w ←
          if w.hasFVar || w.hasMVar then
            pure w
          else
            withTransparency .all <| reduce w
            -- ^^ NOTE: potentially expensive reduction
        return mkApp2 (mkConst ``BitVec.ofNat) w x
    | _ => fallback
  where
    fallback : MetaM Expr := do
      let fn   := e.getAppFn
      let args  ← e.getAppArgs.mapM canonicalizeBitVec
      return mkAppN fn args

/-- Given an expr `rawInst` of type `BitVec 32`,
return an expr of type `Option ArmInst` representing what `rawInst` decodes to.
The resulting expr is guaranteed to be def-eq to `decode_raw_inst $rawInst` -/
def reduceDecodeInstExpr (rawInst : Expr) : MetaM Expr := do
  let expr := mkApp (mkConst ``decode_raw_inst) rawInst
  let expr ← withTransparency .all <| reduce expr
  -- ^^ NOTE: possibly expensive reduction
  canonicalizeBitVec expr

/-! ## SymM Monad -/

abbrev SymM.CacheKey := BitVec 32
abbrev SymM.CacheM := MonadCacheT CacheKey Expr MetaM
abbrev SymM := ProgramInfoT <| MonadCacheT SymM.CacheKey Expr MetaM

@[inherit_doc ProgramInfoT.run]
abbrev SymM.run (name : Name) (k : SymM α) (persist : Bool := true) : MetaM α :=
  MonadCacheT.run <| ProgramInfoT.run name k persist

open SymM in
/-- Given a (reflected) raw instruction,
return an expr of type `Option ArmInst` representing what `rawInst` decodes to.
The resulting expr is guaranteed to be def-eq to `decode_raw_inst $rawInst`.

Results are cached so that the same instruction is not reduced multiple times -/
def reduceDecodeInst (rawInst : BitVec 32) : CacheM Expr :=
  checkCache (rawInst) fun _ =>
    reduceDecodeInstExpr (toExpr rawInst)

open ProgramInfoT InstInfoT

/-! ## reduceStepiToExecInst -/

/-- Given a program and an address, and optionally the corresponding
raw and decoded instructions, construct and return first the expression:
```
∀ {s} (h_program : s.program = <progam>) (h_pc : r .PC s = <addr>)
  (h_err : r .ERR s = .None),
  stepi s = <reduced form of `exec_inst <inst> s`>
```
and then a proof of this fact.
That is, in
  `let ⟨type, value⟩ ← reduceStepi ...`
`value` is an expr whose type is `type` -/
def reduceStepi (addr : BitVec 64) : SymM (Expr × Expr) := do
  let pi : ProgramInfo ← get
  let ⟨_, type, proof⟩ ← modifyInstInfoAt addr <| getInstSemantics fun _ => do
    let rawInst ← getRawInst

    let inst ← getDecodedInst <| fun _ => do
      let optInst ← reduceDecodeInst rawInst
      let_expr some _ inst := optInst
        | let some := mkConst ``Option.some [1]
          throwError "Expected an application of {some}, found:\n\t{optInst}"
      pure inst

    withLocalDecl `s .implicit (mkConst ``ArmState) <| fun s =>
    withLocalDeclD `h_program (h_program_type s pi.expr)  <| fun h_program =>
    withLocalDeclD `h_pc      (h_pc_type s (toExpr addr)) <| fun h_pc =>
    withLocalDeclD `h_err     (h_err_type s)              <| fun h_err => do
      let h_fetch  := fetchLemma s pi.expr h_program addr rawInst
      let h_decode :=
        let armInstTy := mkConst ``ArmInst
        mkApp2 (mkConst ``Eq.refl [1])
          (mkApp (mkConst ``Option [0]) armInstTy)
          (mkApp2 (mkConst ``Option.some [0]) armInstTy inst)

      let proof := -- stepi s = exec_inst <inst> s
        mkAppN (mkConst ``stepi_eq_of_fetch_inst_of_decode_raw_inst) #[
          s, toExpr addr, toExpr rawInst, inst,
          h_err, h_pc, h_fetch, h_decode
        ]
      let type ← inferType proof

      let (ctx, simprocs) ← do
        let localDecls ← do
          let hs := #[h_pc, h_err]
          pure <| hs.filterMap (← getLCtx).findFVar?
        LNSymSimpContext
          (config := {decide := true, ground := false})
          (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
          (decls := localDecls)
          (decls_to_unfold := #[``exec_inst])

      let ⟨simpRes, _⟩ ← simp type ctx simprocs

      let_expr Eq _ _ sem := simpRes.expr
        | let eq ← mkEq (← mkFreshExprMVar none) (← mkFreshExprMVar none)
          throwError "Failed to normalize instruction semantics. Expected {eq}, but found:\n\t{simpRes.expr}"
      let sem ← mkLambdaFVars #[s] sem

      let proof ← simpRes.mkCast proof -- stepi s = <reduced to `w ...`>
      let hs := #[s, h_program, h_pc, h_err]
      let proof ← mkLambdaFVars hs proof
      let type  ← mkForallFVars hs simpRes.expr
      return ⟨sem, type, proof⟩
  return ⟨type, proof⟩

def genStepEqTheorems : SymM Unit := do
  let pi ← get
  for ⟨addr, instInfo⟩ in pi.instructions do
    let startTime ← IO.monoMsNow
    let inst := instInfo.rawInst

    trace[gen_step.debug] "[genStepEqTheorems] Generating theorem for address {addr.toHex}\
      with instruction {inst.toHex}"
    let name := let addr_str := addr.toHexWithoutLeadingZeroes
                Name.str pi.name ("stepi_eq_0x" ++ addr_str)
    let ⟨type, value⟩ ← reduceStepi addr

    trace[gen_step.debug.timing] "[genStepEqTheorems] reduced in: {(← IO.monoMsNow) - startTime}ms"
    addDecl <| Declaration.thmDecl {
      name, type, value,
      levelParams := []
    }
    trace[gen_step.debug.timing] "[genStepEqTheorems] added to environment in: {(← IO.monoMsNow) - startTime}ms"

/-- `#genProgramInfo program` ensures the `ProgramInfo` for `program`
has been generated and persistently cached in the enviroment -/
elab "#genProgramInfo" program:ident : command => liftTermElabM do
  let _ ← ProgramInfo.lookupOrGenerate program.getId


elab "#genStepEqTheorems" program:term : command => liftTermElabM do
  let .const name _ ← Elab.Term.elabTerm program (mkConst ``Program)
    | throwError "Expected a constant, found: {program}"

  SymM.run name (persist := true) <|
    genStepEqTheorems

-----------------------------------------------------------------------------

section StepThmsExample

def test_program : Program :=
  def_program
  [(0x12650c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
    (0x126510#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
    (0x126514#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
    (0x126518#64 , 0x4ea31c7d#32)]      --  mov     v29.16b, v3.16b

#genStepEqTheorems test_program

/--
info: test_program.stepi_eq_0x126510 {s : ArmState} (h_program : s.program = test_program)
  (h_pc : r StateField.PC s = 1205520#64) (h_err : r StateField.ERR s = StateError.None) :
  stepi s = w StateField.PC (1205524#64) (w (StateField.SFP 27#5) (r (StateField.SFP 1#5) s) s)
-/
#guard_msgs in
#check test_program.stepi_eq_0x126510

-- Here's the theorem that we'd actually like to obtain instead of the
-- erstwhile test_program.stepi_eq_0x126510, provided that this
-- enables better aggregation of the effects of a basic block.
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
  simp_all only [minimal_theory, state_simp_rules, bitvec_rules, test_program.stepi_eq_0x126510]
  done

end StepThmsExample

-----------------------------------------------------------------------------
