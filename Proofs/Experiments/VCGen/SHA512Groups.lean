/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.Experiments.VCGen.SHA512Rounds
import Proofs.SHA512.SHA512StepLemmas
import Tactics.VCGen

/-!
# SHA512's loop body, one two-round group at a time, with `vcgen`

The 80 rounds of `sha512_block_armv8`'s loop body are 40 groups of 11–12
instructions. `GI P k s` says what state `s` holds at the start of group `k`, in
terms of the specification: the working state after `2k` rounds
(`rounds P.H P.w (2 * k)`) in the four rotating hash registers, the next
round-constant pair, the 16-word message window (or, from group 32, the next
block's words), and the registers the body does not change.

`#sha512_group g k` builds group `k`'s segment `g` from the program and proves
`⦃ GI P k ⦄ g ⦃ GI P (k + 1) ⦄` by `vcgen`. Each proof sees only its own group's
instructions. `SHA512Groups0`–`3` apply it to groups 0–39, ten per file so that
they build in parallel; `SHA512VCGen.lean` composes them. The functional content is
`group_ok` (from `two_rounds`) and `sched_Wp` (from `sched_step`).
-/

open Std.WP ArmVCGen BitVec SHA2 sha512_helpers DPSFP
set_option experimental.vcgen true

namespace SHA512VCGen

#genVCGenSpecs SHA512.program

/-! ## The program's layout

Every address in the proof is computed from the program: the entry is its lowest
address, the other code addresses are fixed offsets from it (the code's shape),
and the round-constant table's address is what the prologue's `adrp`/`add`
compute. `arm_lit%` turns each into a literal. A rebuild that moves the code or the
table therefore needs only a new `SHA512.program`. -/

/-- The entry (`stp x29, x30, [sp, #-16]!`). -/
abbrev entryPC : BitVec 64 := arm_lit% SHA512.program.min!
/-- The loop head (`ld1 {v24.2d}, [x3], #16`). -/
abbrev headPC : BitVec 64 := arm_lit% (entryPC + 0x40#64)
/-- Group 0 (the first `add v24.2d, v24.2d, v16.2d`). -/
abbrev g0PC : BitVec 64 := arm_lit% (entryPC + 0x60#64)
/-- Group 32, the first that loads the next block. -/
abbrev g32PC : BitVec 64 := arm_lit% (entryPC + 0x660#64)
/-- The tail (adding the saved hash, `add v0.2d, v0.2d, v26.2d`). -/
abbrev tailPC : BitVec 64 := arm_lit% (entryPC + 0x7c0#64)
/-- The loop's `cbnz x2`. -/
abbrev brPC : BitVec 64 := arm_lit% (entryPC + 0x7d0#64)
/-- The `ret`. -/
abbrev retPC : BitVec 64 := arm_lit% (entryPC + 0x7dc#64)

/-- `x3` after the two instructions at `pc` (`adrp x3, …; add x3, x3, …`). -/
def x3After (prog : Program) (pc : BitVec 64) : BitVec 64 :=
  let s : ArmState :=
    { gpr := fun _ => 0#64, sfp := fun _ => 0#128, pc := pc, pstate := PState.zero,
      mem := fun _ => 0#8, program := prog, error := .None }
  r (.GPR 3#5) (run 2 s)

/-- The round-constant table, as addressed by the prologue. -/
abbrev kt : BitVec 64 := arm_lit% (x3After SHA512.program (entryPC + 0x14#64))

/-- The working state after `n` rounds of the compression function from `H`, with
message schedule `w` (as in `compression_alt`). -/
def rounds (H : Hash) (w : Nat → BitVec 64) : Nat → Hash
  | 0 => H
  | n + 1 => compression_update (rounds H w n) (k_512[n]!) (w n)

/-! ## The working state in registers

`sha512h`/`sha512h2` keep the working state in four registers of two words each:
`A = b:a`, `B = d:c`, `C = f:e`, `D = h:g` (high lane first). -/
def lA (S : Hash) : BitVec 128 := S.b ++ S.a
def lB (S : Hash) : BitVec 128 := S.d ++ S.c
def lC (S : Hash) : BitVec 128 := S.f ++ S.e
def lD (S : Hash) : BitVec 128 := S.h ++ S.g

/-- Round-constant pair `k`, as loaded from the table: `K[2k+1] : K[2k]`. -/
def Kp (k : Nat) : BitVec 128 := k_512[2 * k + 1]! ++ k_512[2 * k]!
/-- Message-word pair `j`: `w[2j+1] : w[2j]`. -/
def Wp (w : Nat → BitVec 64) (j : Nat) : BitVec 128 := w (2 * j + 1) ++ w (2 * j)

theorem rounds_two (H : Hash) (w : Nat → BitVec 64) (k : Nat) :
    rounds H w (2 * k + 2) =
      compression_update (compression_update (rounds H w (2 * k)) ((Kp k).extractLsb' 0 64) ((Wp w k).extractLsb' 0 64))
        ((Kp k).extractLsb' 64 64) ((Wp w k).extractLsb' 64 64) := by
  simp only [rounds, Kp, Wp, hi_of_append, lo_of_append]

theorem lB_two (S : Hash) (a b c d : BitVec 64) :
    lB (compression_update (compression_update S a b) c d) = lA S := by
  simp [lB, lA, compression_update]
theorem lD_two (S : Hash) (a b c d : BitVec 64) :
    lD (compression_update (compression_update S a b) c d) = lC S := by
  simp [lD, lC, compression_update]

theorem split128 (K : BitVec 128) : K = K.extractLsb' 64 64 ++ K.extractLsb' 0 64 := by bv_decide

/-- One group's hash computation (`two_rounds`), with the round constants and
message words as 128-bit pairs, in the form the instructions produce. -/
theorem group_ok (S : Hash) (K W : BitVec 128) :
    sha512h2 (lB S) (lA S) (sha512h (extractLsb' 64 128 (lD S ++ lC S)) (extractLsb' 64 128 (lC S ++ lB S))
      (binary_vector_op_aux 0 2 64 BitVec.add (lD S)
        (extractLsb' 64 128 (binary_vector_op_aux 0 2 64 BitVec.add K W 0#128 ++
          binary_vector_op_aux 0 2 64 BitVec.add K W 0#128)) 0#128)) =
      lA (compression_update (compression_update S (K.extractLsb' 0 64) (W.extractLsb' 0 64))
        (K.extractLsb' 64 64) (W.extractLsb' 64 64)) ∧
    binary_vector_op_aux 0 2 64 BitVec.add (lB S) (sha512h (extractLsb' 64 128 (lD S ++ lC S)) (extractLsb' 64 128 (lC S ++ lB S))
      (binary_vector_op_aux 0 2 64 BitVec.add (lD S)
        (extractLsb' 64 128 (binary_vector_op_aux 0 2 64 BitVec.add K W 0#128 ++
          binary_vector_op_aux 0 2 64 BitVec.add K W 0#128)) 0#128)) 0#128 =
      lC (compression_update (compression_update S (K.extractLsb' 0 64) (W.extractLsb' 0 64))
        (K.extractLsb' 64 64) (W.extractLsb' 64 64)) := by
  have h := two_rounds S (K.extractLsb' 0 64) (K.extractLsb' 64 64) (W.extractLsb' 0 64) (W.extractLsb' 64 64)
  simp only [← split128] at h
  exact h

theorem group_okA (S : Hash) (K W : BitVec 128) :
    sha512h2 (lB S) (lA S) (sha512h (extractLsb' 64 128 (lD S ++ lC S)) (extractLsb' 64 128 (lC S ++ lB S))
      (binary_vector_op_aux 0 2 64 BitVec.add (lD S)
        (extractLsb' 64 128 (binary_vector_op_aux 0 2 64 BitVec.add K W 0#128 ++
          binary_vector_op_aux 0 2 64 BitVec.add K W 0#128)) 0#128)) =
      lA (compression_update (compression_update S (K.extractLsb' 0 64) (W.extractLsb' 0 64))
        (K.extractLsb' 64 64) (W.extractLsb' 64 64)) := (group_ok S K W).1

theorem group_okC (S : Hash) (K W : BitVec 128) :
    binary_vector_op_aux 0 2 64 BitVec.add (lB S) (sha512h (extractLsb' 64 128 (lD S ++ lC S)) (extractLsb' 64 128 (lC S ++ lB S))
      (binary_vector_op_aux 0 2 64 BitVec.add (lD S)
        (extractLsb' 64 128 (binary_vector_op_aux 0 2 64 BitVec.add K W 0#128 ++
          binary_vector_op_aux 0 2 64 BitVec.add K W 0#128)) 0#128)) 0#128 =
      lC (compression_update (compression_update S (K.extractLsb' 0 64) (W.extractLsb' 0 64))
        (K.extractLsb' 64 64) (W.extractLsb' 64 64)) := (group_ok S K W).2

/-- `w` satisfies the message-schedule recurrence. -/
def WRec (w : Nat → BitVec 64) : Prop :=
  ∀ u, 16 ≤ u → w u = message_schedule_word_aux (w (u - 2)) (w (u - 7)) (w (u - 15)) (w (u - 16))

/-- One group's message-schedule update, on pairs. -/
theorem sched_Wp (w : Nat → BitVec 64) (hw : WRec w) (j : Nat) :
    sha512su1 (Wp w (j + 7)) (extractLsb' 64 128 (Wp w (j + 5) ++ Wp w (j + 4)))
      (sha512su0 (Wp w (j + 1)) (Wp w j)) = Wp w (j + 8) := by
  have h := sched_step w (2 * j + 16) (by omega) hw
  simp only [Wp]
  rw [show 2 * (j + 8) + 1 = 2 * j + 16 + 1 by omega, show 2 * (j + 8) = 2 * j + 16 by omega, ← h]
  congr 2 <;> congr 1 <;> omega

/-- What is fixed during one iteration of the loop (one block): the values of
the registers the body does not change, the memory, the hash `H` before this
block, and the block's message schedule `w`. `x1` is the input pointer after the
loop header (the next block, or this one again on the last iteration). -/
structure It where
  ctx : BitVec 64
  x1 : BitVec 64
  x2 : BitVec 64
  sp : BitVec 64
  fp : BitVec 64
  lr : BitVec 64
  mem : Memory
  H : Hash
  w : Nat → BitVec 64
  /-- The state whose `regFrame` registers the loop keeps. -/
  base : ArmState

/-- Registers the program does not write, other than `x0` and `x30` (which the
invariants state separately): `x5`–`x28`, `v8`–`v15`, `v30`, `v31`. The program
writes `x1`–`x4`, `v0`–`v7`, `v16`–`v29` and the flags, and restores `x29` and
`sp`. -/
def regFrame (s : ArmState) : List (BitVec 64) × List (BitVec 128) :=
  ([r (.GPR 5#5) s, r (.GPR 6#5) s, r (.GPR 7#5) s, r (.GPR 8#5) s, r (.GPR 9#5) s, r (.GPR 10#5) s, r (.GPR 11#5) s, r (.GPR 12#5) s, r (.GPR 13#5) s, r (.GPR 14#5) s, r (.GPR 15#5) s, r (.GPR 16#5) s, r (.GPR 17#5) s, r (.GPR 18#5) s, r (.GPR 19#5) s, r (.GPR 20#5) s, r (.GPR 21#5) s, r (.GPR 22#5) s, r (.GPR 23#5) s, r (.GPR 24#5) s, r (.GPR 25#5) s, r (.GPR 26#5) s, r (.GPR 27#5) s, r (.GPR 28#5) s],
   [r (.SFP 8#5) s, r (.SFP 9#5) s, r (.SFP 10#5) s, r (.SFP 11#5) s, r (.SFP 12#5) s, r (.SFP 13#5) s, r (.SFP 14#5) s, r (.SFP 15#5) s, r (.SFP 30#5) s, r (.SFP 31#5) s])

/-- Address of group `k` (`k = 40`: the tail after the last group). Groups 0–31
have 12 instructions; groups 32–39 have 11 (no schedule update, but a load of the
next block). -/
def gpc (k : Nat) : BitVec 64 :=
  if k < 32 then arm_lit% g0PC + BitVec.ofNat 64 (48 * k) else arm_lit% g32PC + BitVec.ofNat 64 (44 * (k - 32))

/-- Registers holding `A`, `B`, `C`, `D` at group `k`: each group's result
rotates them, `(A, B, C, D, T) ↦ (D, A, T, C, B)` over `v0`–`v4` (period 5). -/
def ra (k : Nat) : BitVec 5 :=
  if k % 5 = 0 then 0 else if k % 5 = 1 then 3 else if k % 5 = 2 then 2 else if k % 5 = 3 then 4 else 1
def rb (k : Nat) : BitVec 5 :=
  if k % 5 = 0 then 1 else if k % 5 = 1 then 0 else if k % 5 = 2 then 3 else if k % 5 = 3 then 2 else 4
def rc (k : Nat) : BitVec 5 :=
  if k % 5 = 0 then 2 else if k % 5 = 1 then 4 else if k % 5 = 2 then 1 else if k % 5 = 3 then 0 else 3
def rd (k : Nat) : BitVec 5 :=
  if k % 5 = 0 then 3 else if k % 5 = 1 then 2 else if k % 5 = 2 then 4 else if k % 5 = 3 then 1 else 0

/-- Message register `q` of the next block, as loaded (and byte-reversed) in
groups 32–39. -/
def nbv (P : It) (q : Nat) : BitVec 128 :=
  vrev128_64_8 (P.mem.read_bytes 16 (P.x1 + BitVec.ofNat 64 (16 * q)))

/-- Message register `v(16+q)` at group `k`: before group 32, the pair from the
16-word window `w[2k ..]`; from group 32 on, the next block's words replace
the pairs already used. -/
def msgv (P : It) (k q : Nat) : BitVec 128 :=
  if k < 32 then Wp P.w (k + (q + 8 - k % 8) % 8)
  else if q + 32 < k then nbv P q else Wp P.w (32 + q)

/-- `x3` (the round-constant pointer) at group `k`. -/
def ktX (k : Nat) : BitVec 64 :=
  if k < 40 then arm_lit% kt + BitVec.ofNat 64 (16 * (k + 1)) else arm_lit% kt

/-- `x1` (the input pointer) at group `k`. -/
def x1v (P : It) (k : Nat) : BitVec 64 :=
  if k ≤ 32 then P.x1 else P.x1 + BitVec.ofNat 64 (16 * (k - 32))

/-- The state at the start of two-round group `k` of the iteration `P`. -/
def GI (P : It) (k : Nat) (s : ArmState) : Prop :=
  Side SHA512.program (gpc k) s ∧ s.mem = P.mem ∧
  r (.GPR 0#5) s = P.ctx ∧ r (.GPR 1#5) s = x1v P k ∧ r (.GPR 2#5) s = P.x2 ∧
  r (.GPR 3#5) s = ktX k ∧ r (.GPR 29#5) s = P.fp ∧ r (.GPR 30#5) s = P.lr ∧
  r (.GPR 31#5) s = P.sp ∧
  r (.SFP (ra k)) s = lA (rounds P.H P.w (2 * k)) ∧
  r (.SFP (rb k)) s = lB (rounds P.H P.w (2 * k)) ∧
  r (.SFP (rc k)) s = lC (rounds P.H P.w (2 * k)) ∧
  r (.SFP (rd k)) s = lD (rounds P.H P.w (2 * k)) ∧
  r (.SFP 26#5) s = lA P.H ∧ r (.SFP 27#5) s = lB P.H ∧
  r (.SFP 28#5) s = lC P.H ∧ r (.SFP 29#5) s = lD P.H ∧
  (k < 40 → r (.SFP (BitVec.ofNat 5 (24 + k % 2))) s = Kp k) ∧
  r (.SFP 16#5) s = msgv P k 0 ∧ r (.SFP 17#5) s = msgv P k 1 ∧
  r (.SFP 18#5) s = msgv P k 2 ∧ r (.SFP 19#5) s = msgv P k 3 ∧
  r (.SFP 20#5) s = msgv P k 4 ∧ r (.SFP 21#5) s = msgv P k 5 ∧
  r (.SFP 22#5) s = msgv P k 6 ∧ r (.SFP 23#5) s = msgv P k 7 ∧
  regFrame s = regFrame P.base

/-- Segment boundaries inside the loop: the loop head, the groups, the tail and
the `cbnz`. -/
def isB (pc : BitVec 64) : Bool :=
  pc = arm_lit% headPC || pc = arm_lit% tailPC || pc = arm_lit% brPC ||
  (arm_lit% g0PC ≤ pc && pc < arm_lit% g32PC && (pc - arm_lit% g0PC).toNat % 48 = 0) ||
  (arm_lit% g32PC ≤ pc && pc < arm_lit% tailPC && (pc - arm_lit% g32PC).toNat % 44 = 0)

/-- Simp set that evaluates `GI P k` for a literal `k`. -/
macro "sha512_gi_simp" : tactic => `(tactic|
  simp only [GI, gpc, ra, rb, rc, rd, msgv, nbv, ktX, x1v, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte, ↓dreduceIte,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero, BitVec.add_assoc,
    Memory.State.read_mem_bytes_eq_mem_read_bytes, regFrame, Prod.mk.injEq, List.cons.injEq,
    and_true] at *)

open Lean in
/-- `#sha512_group g k`: the segment `g` of two-round group `k` and its triple `g_spec`. -/
macro "#sha512_group " g:ident k:num : command => do
  let spec := mkIdent (g.getId.appendAfter "_spec")
  `(#genVCGenSegment $g := buildSeg SHA512.program isB 20 (gpc $k)
    theorem $spec (P : It) (hK : $k < 39 → P.mem.read_bytes 16 (ktX $k) = Kp ($k + 1)) (hw : WRec P.w) :
        ⦃ GI P $k ⦄ $g ⦃ fun _ => GI P ($k + 1) ⦄ := by
      have hr := rounds_two P.H P.w $k
      have hs := sched_Wp P.w hw $k
      simp only [Nat.reduceMul, Nat.reduceAdd] at hr hs
      try (have hK := hK (by decide); simp only [ktX, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT,
        ↓reduceIte, BitVec.reduceAdd] at hK)
      unfold $g:ident
      vcgen
      all_goals first
        | arm_vc_step
        | exact (‹GI P $k _›).1
        | (sha512_gi_simp
           arm_vc_final
           repeat' apply And.intro
           all_goals first
             | with_reducible assumption
             | with_reducible exact group_okA _ _ _ | with_reducible exact group_okC _ _ _
             | with_reducible exact (lB_two _ _ _ _ _).symm
             | with_reducible exact (lD_two _ _ _ _ _).symm
             | (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)))

end SHA512VCGen
