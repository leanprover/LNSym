/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Arm.Exec

namespace Cfg

open BitVec

/--
Conditions under which a branch is taken; this is a function that
takes a state as input, and returns whether the branch was taken.
-/
abbrev CondHoldsFn := ArmState → Bool

/--
The general type of an instruction: for control-flow analysis, we
only care about how an instruction affects the program's control
flow.
-/
inductive InstType where
  -- Seq: Instruction at address pc after which control falls through
  -- to the next one, in program order (i.e., at pc + 4).
  | Seq   (pc : BitVec 64)                      : InstType
  -- BrTgt: Instruction at address pc is the target of a conditional
  -- branch; cond is the condition under which the branch was taken
  | BrTgt (pc : BitVec 64) (cond : CondHoldsFn) : InstType
  -- BrOrg: Instruction at address pc is the origin of a conditional
  -- branch; cond is the condition under which the branch was taken.
  | BrOrg (pc : BitVec 64) (cond : CondHoldsFn) : InstType
  -- Ret: Instruction at address oc is the return instruction.
  | Ret   (pc : BitVec 64)                      : InstType

instance : Repr InstType where
  reprPrec pc_e _ :=
    match pc_e with
      | InstType.Seq pc  => "<Seq>" ++ repr pc
      | InstType.BrTgt pc _ => "<BrTgt>" ++ repr pc
      | InstType.BrOrg pc _ => "<BrOrg>" ++ repr pc
      | InstType.Ret pc  => "<Ret>" ++ repr pc

instance : ToString InstType where toString i := toString (repr i)

def InstType.pc (x : InstType) : BitVec 64 :=
  match x with
  | Seq x | BrTgt x _ | BrOrg x _ | Ret x => x

instance : Ord InstType where
  -- Only compares the pc values.
  compare x y :=
     let x_pc := InstType.pc x
     let y_pc := InstType.pc y
     compare x_pc y_pc

def InstType.pc_equal (x y : InstType) : Bool :=
  -- Essentially: InstType.pc x == InstType.pc y
  (compare x y) == .eq

def InstType.pc_and_type_equal (x y : InstType) : Bool :=
  open InstType in
  match x, y with
  | Seq _, Seq _
  | BrOrg _ _, BrOrg _ _
  | BrTgt _ _, BrTgt _ _
  | Ret _, Ret _ => InstType.pc_equal x y
  | _, _ => false

/-- An entry in the forward control-flow graph. -/
abbrev F_CFGentry := InstType × List InstType

/--
A forward control-flow graph maps an instruction (in its InstType
form) to all possible next instructions (in their InstTypes forms).

An edge from `from_pc` to `to_pc` means that control may transfer from
the former to the latter in one instruction step.
-/
def ForwardGraph := Array F_CFGentry deriving Repr

instance : ToString ForwardGraph where toString fg := toString (repr fg)

structure LoopInfo where
  guard   : InstType -- Instruction where the loop guard is tested
  target  : InstType -- First instruction of the loop, where control
                     -- flows if the loop guard is satisfied
  next    : InstType -- First instruction executed after the loop.
  -- unrollp : Bool := false
deriving Repr

def LoopsInfo := Array (Nat × LoopInfo)
deriving Repr

instance : ToString LoopsInfo where toString li := toString (repr li)

/--
CFG collects all the control-flow information gleaned from the
program during static analysis.
-/
structure Cfg where
  start_address       : BitVec 64
  graph               : ForwardGraph  := #[]
  loops_info          : LoopsInfo := #[]
  maybe_modified_regs : Array RegType := #[]
deriving Repr

instance : ToString Cfg where toString cfg := toString (repr cfg)

/--
We can detect a loop if we find an entry where some `to_pc` is
less than its corresponding `from_pc`, i.e., there is a back-jump from
`from_pc` to `to_pc`.

In that case, `to_pc` has the loop target instruction and `from_pc`
has the loop guard instruction. The first instruction that will be
executed after the loop terminates will also be a member of `to_insts`
of type `Seq`.
-/
private def loop_detected (from_inst : InstType) (to_insts : List InstType) :
  Except Format (Option LoopInfo) :=
  let check := List.find?
               (fun x => compare x from_inst == .lt)
               to_insts
  match check with
  | none => pure none
  | some to_inst =>
    let next := List.filter
                 (fun x => match x with | InstType.Seq _ => true | _ => false)
                to_insts
    if h : next.length == 1 then
      have h' : next.length > 0 := by simp_all
      pure (some { guard := from_inst, target := to_inst, next := next[0]'h' })
    else
      .error
        s!"We expected exactly one Seq instruction in the control-flow graph \
        for this entry. Instead, we found {next.length}."

private def addToLoopsInfo (entry : Option LoopInfo) (loops_info : LoopsInfo) : LoopsInfo :=
  match entry with
  | none => loops_info
  | some loop_info =>
    let index := loops_info.size
    Array.push loops_info (index, loop_info)

private def addEntry (from_inst : InstType) (to_insts : List InstType)
                     (mod_regs : List RegType) (cfg : Cfg) : Except String Cfg := do
  -- We crawl through the program in a linear manner, so by
  -- construction, we should not add a previously-added InstType to
  -- the graph.
  let maybe_entry := Array.find? cfg.graph (fun (e, _) => InstType.pc_equal e from_inst)
  if Option.isNone maybe_entry then
    let maybe_loop_info ← loop_detected from_inst to_insts
    let new_loops_info := addToLoopsInfo maybe_loop_info cfg.loops_info
    let new_graph := Array.push cfg.graph (from_inst, to_insts)
    let maybe_modified_regs :=
      -- Would've been nice to be able to deduplicate and sort at the same time...
      Array.insertionSort (mod_regs_go mod_regs cfg.maybe_modified_regs)
                          (fun r1 r2 =>
                            match r1, r2 with
                            | .GPR i, .GPR j => i ≤ j
                            | .GPR _, .SFP _ => true
                            | .SFP i, .SFP j => i ≤ j
                            | .SFP _, .GPR _ => false)
    pure { cfg with graph := new_graph,
                    loops_info := new_loops_info,
                    maybe_modified_regs := maybe_modified_regs }
  else
  .error
    f!"[ForwardGraph] Implementation Error: graph already contains \
    an entry with PC {InstType.pc from_inst}! \
    Here is the graph: ${Format.indentD cfg.graph}."
  where mod_regs_go (mod_regs : List RegType) (all : Array RegType) : Array RegType :=
    match mod_regs with
    | [] => all
    | m :: ms => if m ∈ all then mod_regs_go ms all
                 else mod_regs_go ms (all.push m)
/--
This function adds information for an Arm instruction into Cfg
Inputs: `pc` -- current program counter
        `arm_inst` -- current Arm instruction
        `cfg` -- the control-flow graph
outputs: `haltp` : `Bool` -- whether the program halts
         `cfg` : `Cfg` -- the updated control-flow graph
-/
protected def addArmInstToCfg (pc : BitVec 64) (raw_inst : BitVec 32)
   (arm_inst : ArmInst) (cfg : Cfg) : Except String (Bool × Cfg) := do
   let default_to_pc ← pure (pc + 4#64)
   -- variable pc_inst: the type of instruction InstType: Seq, BrOrg, BrTgt, Ret
   -- variable to_insts: an over-approximation of possible next pcs,
   --                    for a conditional branch, the to_insts include all
   --                    possible branch targets
   let ((haltp : Bool), (pc_inst : InstType), (to_insts : List InstType)) :=
   open InstType ArmInst in
   match arm_inst with
   | DPI _ | DPR _ | LDST _ | DPSFP _ =>
    (false, Seq pc, [Seq default_to_pc])
   | BR i =>
     open BranchInst in
     match i with
      | Compare_branch inst => -- CBZ, CBNZ
        let branch_taken_pc := BR.Compare_branch_inst.branch_taken_pc inst pc
        let (condition_holds : CondHoldsFn) :=
            (fun state => BR.Compare_branch_inst.condition_holds inst state)
        (false, BrOrg pc condition_holds,
                [Seq default_to_pc, BrTgt branch_taken_pc condition_holds])
      | Uncond_branch_imm inst => -- B, BL
        let branch_taken_pc := BR.Uncond_branch_imm_inst.branch_taken_pc inst pc
        -- These are unconditional branch instructions; we do not add
        -- BrTgt/BrOrg or the default_to_pc here.
        (false, Seq pc, [Seq branch_taken_pc])
      | Uncond_branch_reg _ => -- RET
        -- (FIXME) Extend CFG analysis when instructions other than
        -- RET are implemented.
        --
        -- (FIXME) The to_inst for RET can be the value in the GPR
        -- indexed by `inst.Rn`, but we can figure that value out only
        -- after symbolic simulation.
        (true, Ret pc, [Ret pc])
      | Cond_branch_imm inst =>
        let branch_taken_pc := BR.Cond_branch_imm_inst.branch_taken_pc inst pc
        let (condition_holds : CondHoldsFn) :=
            (fun state => BR.Cond_branch_imm_inst.condition_holds inst state)
        (false, BrOrg pc condition_holds,
          [Seq default_to_pc, BrTgt branch_taken_pc condition_holds])
      -- Currently only consider NOP
      | Hints _ =>
        (false, Seq pc, [Seq default_to_pc])
   do let maybe_modified_regs ← mayModifiedRegs raw_inst
   let new_cfg ← addEntry pc_inst to_insts maybe_modified_regs cfg
   pure (haltp, new_cfg)

protected def addToCfg (address : BitVec 64) (program : Program) (cfg : Cfg)
  : Except String (Bool × Cfg) :=
  let maybe_raw_inst := program.find? address
  match maybe_raw_inst with
  | none => .error s!"No instruction found at address {address}!"
  | some raw_inst =>
    let maybe_arm_inst := decode_raw_inst raw_inst
    match maybe_arm_inst with
    | none =>
      .error s!"Instruction {raw_inst} at {address} could not be decoded!"
    | some arm_inst =>
      Cfg.addArmInstToCfg address raw_inst arm_inst cfg

/-
Termination argument for the `create'` function below. This theorem
is in terms of `Fin` so that we can take advantage of `Fin` lemmas. We
will map this theorem to `BitVecs` (using lemmas like
`BitVec.fin_bitvec_lt`) in `create'`.
-/
private theorem termination_lemma (i j max : Fin n) (h : n > 0)
  (h0 : i < max) (h1 : j <= max - i) (h2 : ((Fin.ofNat' 0 h) : Fin n) < j) :
  (max - (i + j)) < (max - i) := by
  -- Our strategy is to convert this proof obligation in terms of Nat,
  -- which is made possible by h0 and h1 hypotheses above.
  have h0' : (i : Nat) < (max : Nat) := by simp_all only [Fin.lt_def, h0]
  have h3 : (max - i : Fin n) = ((max - i) : Nat) := by
    simp_all [Fin.coe_sub_iff_le]
    exact Nat.le_of_lt h0
  have h1' : (j : Nat) <= ((max - i) : Fin n) := by
    apply Fin.le_def.mpr; exact h1
  rw [h3] at h1'
  have h1'' : (i : Nat) + (j : Nat) <= (max : Nat) - (i : Nat) + (i : Nat) := by
    rw [Nat.add_comm]
    exact Nat.add_le_add_right h1' (i : Nat)
  have h1_rhs'' : (max : Nat) - (i : Nat) + (i : Nat) = (max : Nat) := by
    apply Nat.sub_add_cancel
    apply Nat.le_of_lt; trivial
  rw [h1_rhs''] at h1''
  -- At this point, we have Nat versions of h0 and h1:
  -- h0' : ↑i < ↑max
  -- h1'' : ↑i + ↑j ≤ ↑max
  -- Now we will go about mapping the conclusion in terms of Nat too.
  have max_limit := max.isLt
  have sub_lhs' : ((i + j) : Fin n) = (i : Nat) + (j : Nat) := by
    rw [Fin.val_add]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt h1'' max_limit
  apply Fin.lt_def.mp
  have lhs'' : (max - (i + j) : Fin n) = (max - (i + j) : Nat) := by
    rw [←sub_lhs']
    apply Fin.coe_sub_iff_le.mpr
    apply Fin.le_def.mpr
    simp_all! only [h0, sub_lhs', h1'']
  simp_all! only [Fin.lt_def, Fin.le_def, Fin.is_lt, h0]
  -- Now our conclusion is in terms of Nat, and we can use standard
  -- Nat lemmas to close the goal.
  rw [Nat.sub_add_eq]
  exact Nat.sub_lt_self h2 h1'
  done

/--
Create a `Cfg` structure for `program`, beginning at `start_address` until
`end_address`.
-/
protected def create' (start_address end_address : BitVec 64)
                      (program : Program) : Except String Cfg :=
  go start_address end_address program { start_address }
  where go (address max_address : BitVec 64)
           (program : Program) (cfg : Cfg) : Except String Cfg := do
  if h₀ : max_address < address then
    pure cfg
  else
    let (haltp, cfg) ← Cfg.addToCfg address program cfg
    if haltp then
      pure cfg
    else if h₁ : address = max_address then
      pure cfg
    else if h₂ : 4#64 <= max_address - address then
         have ?term_lemma : (max_address - (address + 4#64)).toNat < (max_address - address).toNat := by
           have := termination_lemma address.toFin (4#64).toFin max_address.toFin
                   (by decide)
                   (by simp_all! only [BitVec.not_lt,
                                       BitVec.fin_bitvec_lt,
                                       not_false_eq_true,
                                       BitVec.lt_of_le_ne, h₁])
                   (by rw [← BitVec.toFin_sub]; exact h₂)
                   (by simp_arith)
           simp [BitVec.fin_bitvec_le, BitVec.fin_bitvec_lt] at *
           exact this
         go (address + 4#64) max_address program cfg
    else
        .error
               s!"We expect Arm instructions to be 32-bits wide; i.e., each \
                program address should be 4-apart from its successor. \
                This does not seem to be the case with this program for the \
                successor of address {address}. Note that the highest \
                address is {max_address}."
  termination_by (max_address - address).toNat

/--
Create a `Cfg` structure for the program `program`.
-/
protected def create (program : Program) : Except String Cfg :=
  let maybe_start_address := program.min?
  let maybe_max_address := program.max?
  match maybe_start_address, maybe_max_address with
  | some start_address, some max_address =>
    Cfg.create' start_address max_address program
  | _, _ =>
    .error s!"Could not determine the start/stop address for the program!"

end Cfg
