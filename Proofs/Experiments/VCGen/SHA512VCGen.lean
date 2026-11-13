/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.Experiments.VCGen.SHA512Groups0
import Proofs.Experiments.VCGen.SHA512Groups1
import Proofs.Experiments.VCGen.SHA512Groups2
import Proofs.Experiments.VCGen.SHA512Groups3
import Correctness.VCGen
import Arm.Memory.Separate
import Arm.Memory.MemoryProofs

/-!
# Experimental: total correctness of `sha512_block_armv8` with Lean's `vcgen`

The main theorem is `sha512_correct`, stated in the specification's terms (see
its docstring and `preS`/`postS`). It follows from `correctness`, which states
the same with the context and input as the program loads them:

`correctness : Correctness ArmState`: from any state satisfying `pre`, the
program (`SHA512.program`, 504 instructions, any number `N ≥ 1` of blocks) runs
to its `ret`, and there `post` holds: the context holds the hash of the input
blocks, `processBlocks_alt` from the specification (`Specs/SHA512.lean`),
starting from the hash the context held on entry; `x29`, `x30` and `sp` are
restored; memory outside the stack frame and the context is unchanged.

It is proved by the cut-point method (`Correctness.by_the_method`), with cut
points at the entry, the loop head and the `ret`, and a `rank` that decreases
from each cut point to the next (`x2`, the number of blocks left, decreases
around the loop). Each obligation is a `vcgen` triple about the segment to the
next cut point, bridged by `ArmVCGen.by_the_method_v4_of_triple`:

- `pro_spec`: the prologue (16 instructions) establishes `LoopInv` with no
  block done.
- `body_spec`: one trip around the loop (488 instructions), composed with
  `triple_seq` from separately verified pieces, so that each `vcgen` run sees
  only its own instructions: `hdr_spec` (the loop header), the 40 two-round
  groups (`SHA512Groups*.lean`), `tail_spec` (adding the block's result to the
  hash) and `br_spec` (the `cbnz`: back to the loop head with `LoopInv` for one
  more block, or the epilogue's store and `ret` with `post`).

Representation (see `pre`): the context is four little-endian 128-bit lanes
`b:a`, `d:c`, `f:e`, `h:g` (`ofLanes`); message word `j` of block `i` is the
big-endian 64-bit word at `x1 + 128 i + 8 j` (`msgPair` byte-reverses each half
of a 16-byte load, as `rev64` does); the round-constant table holds `K[2j+1] :
K[2j]` at `kt + 16 j` (`kt`: the address the prologue computes). The stack frame (`stp x29, x30`) must be separate
from the context, the input and the table.
-/

open Std.WP ArmVCGen BitVec SHA2 sha512_helpers DPSFP
set_option experimental.vcgen true

namespace SHA512VCGen

/-! ## The data: context, blocks, and the hash after `i` blocks -/

/-- A `Hash` from the four 128-bit lanes `b:a`, `d:c`, `f:e`, `h:g`. -/
def ofLanes (v0 v1 v2 v3 : BitVec 128) : Hash :=
  ⟨v0.extractLsb' 0 64, v0.extractLsb' 64 64, v1.extractLsb' 0 64, v1.extractLsb' 64 64,
   v2.extractLsb' 0 64, v2.extractLsb' 64 64, v3.extractLsb' 0 64, v3.extractLsb' 64 64⟩

abbrev ctx (s0 : ArmState) : BitVec 64 := r (.GPR 0#5) s0
abbrev inp (s0 : ArmState) : BitVec 64 := r (.GPR 1#5) s0
abbrev sp (s0 : ArmState) : BitVec 64 := r (.GPR 31#5) s0
/-- The number of blocks. -/
abbrev nblk (s0 : ArmState) : Nat := (r (.GPR 2#5) s0).toNat

/-- The initial hash, in the context at `x0`. -/
def H0 (s0 : ArmState) : Hash :=
  ofLanes (read_mem_bytes 16 (ctx s0) s0) (read_mem_bytes 16 (ctx s0 + 16#64) s0)
    (read_mem_bytes 16 (ctx s0 + 32#64) s0) (read_mem_bytes 16 (ctx s0 + 48#64) s0)

def blkA (s0 : ArmState) (i q : Nat) : BitVec 64 :=
  inp s0 + BitVec.ofNat 64 (128 * i) + BitVec.ofNat 64 (16 * q)

/-- Message words `2q+1 : 2q` of block `i` (big-endian 64-bit words). -/
def msgPair (s0 : ArmState) (i q : Nat) : BitVec 128 :=
  vrev128_64_8 (read_mem_bytes 16 (blkA s0 i q) s0)

def msgWords (s0 : ArmState) (i : Nat) : List (BitVec 64) :=
  (List.range 16).map fun j =>
    if j % 2 = 0 then (msgPair s0 i (j / 2)).extractLsb' 0 64 else (msgPair s0 i (j / 2)).extractLsb' 64 64

def blocks (s0 : ArmState) : List (List (BitVec 64)) := (List.range (nblk s0)).map (msgWords s0)

/-- The hash after the first `i` blocks. -/
def hashAt (s0 : ArmState) (i : Nat) : Hash :=
  processBlocks_alt j_512 (H0 s0) k_512 ((blocks s0).take i)

def msched (s0 : ArmState) (i : Nat) : Nat → BitVec 64 := fun t => message_schedule_word t (msgWords s0 i)

/-- Memory after the prologue pushes `x29`, `x30`. -/
def stackMem (s0 : ArmState) : Memory :=
  (write_mem_bytes 16 (sp s0 - 16#64) (r (.GPR 30#5) s0 ++ r (.GPR 29#5) s0) s0).mem

/-- The loop invariant at the loop head (`headPC`): `i` blocks done. -/
def LoopInv (s0 s : ArmState) : Prop :=
  Side SHA512.program arm_lit% headPC s ∧
  0 < (r (.GPR 2#5) s).toNat ∧ (r (.GPR 2#5) s).toNat ≤ nblk s0 ∧
  r (.GPR 0#5) s = ctx s0 ∧
  r (.GPR 1#5) s = inp s0 + BitVec.ofNat 64 (128 * (nblk s0 - (r (.GPR 2#5) s).toNat + 1)) ∧
  r (.GPR 3#5) s = kt ∧
  r (.GPR 29#5) s = sp s0 - 16#64 ∧ r (.GPR 30#5) s = r (.GPR 30#5) s0 ∧
  r (.GPR 31#5) s = sp s0 - 16#64 ∧
  s.mem = stackMem s0 ∧
  r (.SFP 0#5) s = lA (hashAt s0 (nblk s0 - (r (.GPR 2#5) s).toNat)) ∧
  r (.SFP 1#5) s = lB (hashAt s0 (nblk s0 - (r (.GPR 2#5) s).toNat)) ∧
  r (.SFP 2#5) s = lC (hashAt s0 (nblk s0 - (r (.GPR 2#5) s).toNat)) ∧
  r (.SFP 3#5) s = lD (hashAt s0 (nblk s0 - (r (.GPR 2#5) s).toNat)) ∧
  r (.SFP 16#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 0 ∧
  r (.SFP 17#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 1 ∧
  r (.SFP 18#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 2 ∧
  r (.SFP 19#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 3 ∧
  r (.SFP 20#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 4 ∧
  r (.SFP 21#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 5 ∧
  r (.SFP 22#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 6 ∧
  r (.SFP 23#5) s = msgPair s0 (nblk s0 - (r (.GPR 2#5) s).toNat) 7 ∧
  regFrame s = regFrame s0

theorem LoopInv.mem {s0 s : ArmState} (h : LoopInv s0 s) : s.mem = stackMem s0 :=
  h.2.2.2.2.2.2.2.2.2.1

/-- The iteration's fixed data, from the state `si` at the loop head. -/
def itOf (s0 si : ArmState) : It where
  ctx := ctx s0
  x1 := if r (.GPR 2#5) si - 1#64 = 0#64 then r (.GPR 1#5) si - 128#64 else r (.GPR 1#5) si
  x2 := r (.GPR 2#5) si - 1#64
  sp := sp s0 - 16#64
  fp := sp s0 - 16#64
  lr := r (.GPR 30#5) s0
  mem := si.mem
  H := hashAt s0 (nblk s0 - (r (.GPR 2#5) si).toNat)
  w := msched s0 (nblk s0 - (r (.GPR 2#5) si).toNat)
  base := s0

/-! ## Segments -/

#genVCGenSegment hdr := buildSeg SHA512.program isB 20 arm_lit% headPC
#genVCGenSegment tail := buildSeg SHA512.program isB 20 arm_lit% tailPC

theorem rounds_zero (H : Hash) (w : Nat → BitVec 64) : rounds H w 0 = H := rfl

theorem subs1_z (x : BitVec 64) :
    ((AddWithCarry x 0xfffffffffffffffe#64 1#1).snd.z = 1#1) ↔ (x - 1#64 = 0#64) := by
  simp only [AddWithCarry, bitvec_rules, state_simp_rules]
  repeat split
  · bv_decide
  · bv_decide

theorem hdr_spec (s0 si : ArmState) (hI : LoopInv s0 si)
    (hK0 : si.mem.read_bytes 16 kt = Kp 0)
    (hW : ∀ q < 8, Wp (msched s0 (nblk s0 - (r (.GPR 2#5) si).toNat)) q =
      msgPair s0 (nblk s0 - (r (.GPR 2#5) si).toNat) q) :
    ⦃ fun s => s = si ⦄ hdr ⦃ fun _ => GI (itOf s0 si) 0 ⦄ := by
  unfold hdr
  vcgen
  all_goals first
    | arm_vc_step
    | (subst_vars; exact hI.1)
    | (subst_vars
       simp only [LoopInv, regFrame, Prod.mk.injEq, List.cons.injEq, and_true] at hI
       sha512_gi_simp
       simp only [itOf, rounds_zero] at *
       arm_vc_final_with [subs1_z])

/-- The state at the `cbnz` (`brPC`) after the iteration `P`. -/
def TI (P : It) (s : ArmState) : Prop :=
  Side SHA512.program arm_lit% brPC s ∧ s.mem = P.mem ∧
  r (.GPR 0#5) s = P.ctx ∧ r (.GPR 1#5) s = P.x1 + 128#64 ∧ r (.GPR 2#5) s = P.x2 ∧
  r (.GPR 3#5) s = kt ∧ r (.GPR 29#5) s = P.fp ∧ r (.GPR 30#5) s = P.lr ∧
  r (.GPR 31#5) s = P.sp ∧
  r (.SFP 0#5) s = lA (add_hash P.H (rounds P.H P.w 80)) ∧
  r (.SFP 1#5) s = lB (add_hash P.H (rounds P.H P.w 80)) ∧
  r (.SFP 2#5) s = lC (add_hash P.H (rounds P.H P.w 80)) ∧
  r (.SFP 3#5) s = lD (add_hash P.H (rounds P.H P.w 80)) ∧
  r (.SFP 16#5) s = nbv P 0 ∧ r (.SFP 17#5) s = nbv P 1 ∧
  r (.SFP 18#5) s = nbv P 2 ∧ r (.SFP 19#5) s = nbv P 3 ∧
  r (.SFP 20#5) s = nbv P 4 ∧ r (.SFP 21#5) s = nbv P 5 ∧
  r (.SFP 22#5) s = nbv P 6 ∧ r (.SFP 23#5) s = nbv P 7 ∧
  regFrame s = regFrame P.base

theorem lane_addA (S H : Hash) : binary_vector_op_aux 0 2 64 BitVec.add (lA S) (lA H) 0#128 = lA (add_hash H S) := by
  simp only [binary_vector_op_aux_add_128_simp, lA, add_hash, hi_of_append, lo_of_append, BitVec.add_comm]
theorem lane_addB (S H : Hash) : binary_vector_op_aux 0 2 64 BitVec.add (lB S) (lB H) 0#128 = lB (add_hash H S) := by
  simp only [binary_vector_op_aux_add_128_simp, lB, add_hash, hi_of_append, lo_of_append, BitVec.add_comm]
theorem lane_addC (S H : Hash) : binary_vector_op_aux 0 2 64 BitVec.add (lC S) (lC H) 0#128 = lC (add_hash H S) := by
  simp only [binary_vector_op_aux_add_128_simp, lC, add_hash, hi_of_append, lo_of_append, BitVec.add_comm]
theorem lane_addD (S H : Hash) : binary_vector_op_aux 0 2 64 BitVec.add (lD S) (lD H) 0#128 = lD (add_hash H S) := by
  simp only [binary_vector_op_aux_add_128_simp, lD, add_hash, hi_of_append, lo_of_append, BitVec.add_comm]

theorem tail_spec (P : It) : ⦃ GI P 40 ⦄ tail ⦃ fun _ => TI P ⦄ := by
  unfold tail
  vcgen
  all_goals first
    | arm_vc_step
    | exact (‹GI P 40 _›).1
    | (simp only [TI, regFrame, Prod.mk.injEq, List.cons.injEq, and_true] at *
       sha512_gi_simp
       arm_vc_final_with [lane_addA, lane_addB, lane_addC, lane_addD, BitVec.add_assoc])

/-! ## The specification (`pre`, `post`, `exit`), cut points, assertions and the rank -/

/-- The hash of all blocks. -/
def Hfin (s0 : ArmState) : Hash := processBlocks_alt j_512 (H0 s0) k_512 (blocks s0)

def pre (s0 : ArmState) : Prop :=
  s0.program = SHA512.program ∧ r .PC s0 = arm_lit% entryPC ∧ r .ERR s0 = .None ∧ CheckSPAlignment s0 ∧
  0 < nblk s0 ∧
  -- The round constants, two per 16 bytes (little-endian, `K[0]` first).
  (∀ j < 40, read_mem_bytes 16 (kt + BitVec.ofNat 64 (16 * j)) s0 = Kp j) ∧
  -- The stack frame is separate from the context, the input and the table.
  mem_separate' (sp s0 - 16#64) 16 (ctx s0) 64 ∧
  mem_separate' (sp s0 - 16#64) 16 (inp s0) (nblk s0 * 128) ∧
  mem_separate' (sp s0 - 16#64) 16 kt 640

theorem pre.nblk_pos {s0 : ArmState} (h : pre s0) : 0 < nblk s0 := h.2.2.2.2.1
theorem pre.ktbl {s0 : ArmState} (h : pre s0) :
    ∀ j < 40, read_mem_bytes 16 (kt + BitVec.ofNat 64 (16 * j)) s0 = Kp j := h.2.2.2.2.2.1
theorem pre.sep_ctx {s0 : ArmState} (h : pre s0) : mem_separate' (sp s0 - 16#64) 16 (ctx s0) 64 :=
  h.2.2.2.2.2.2.1
theorem pre.sep_inp {s0 : ArmState} (h : pre s0) :
    mem_separate' (sp s0 - 16#64) 16 (inp s0) (nblk s0 * 128) := h.2.2.2.2.2.2.2.1
theorem pre.sep_kt {s0 : ArmState} (h : pre s0) : mem_separate' (sp s0 - 16#64) 16 kt 640 :=
  h.2.2.2.2.2.2.2.2

/-- At the `ret`: the context holds the hash of all blocks, the frame is popped,
the registers the program does not write (`x0`, `x30`, `regFrame`) are
unchanged, and so is memory outside the stack frame and the context. -/
def post (s0 sf : ArmState) : Prop :=
  read_mem_bytes 16 (ctx s0) sf = lA (Hfin s0) ∧
  read_mem_bytes 16 (ctx s0 + 16#64) sf = lB (Hfin s0) ∧
  read_mem_bytes 16 (ctx s0 + 32#64) sf = lC (Hfin s0) ∧
  read_mem_bytes 16 (ctx s0 + 48#64) sf = lD (Hfin s0) ∧
  r (.GPR 29#5) sf = r (.GPR 29#5) s0 ∧ r (.GPR 30#5) sf = r (.GPR 30#5) s0 ∧
  r (.GPR 0#5) sf = r (.GPR 0#5) s0 ∧ regFrame sf = regFrame s0 ∧
  sp sf = sp s0 ∧
  sf.program = SHA512.program ∧ r .PC sf = arm_lit% retPC ∧ r .ERR sf = .None ∧
  -- Memory outside the stack frame and the context is unchanged.
  (∀ n a, mem_separate' a n (sp s0 - 16#64) 16 → mem_separate' a n (ctx s0) 64 →
    read_mem_bytes n a sf = read_mem_bytes n a s0)

def exit (s : ArmState) : Prop := r .PC s = arm_lit% retPC

def cutPC (pc : BitVec 64) : Bool := pc = arm_lit% entryPC || pc = arm_lit% headPC || pc = arm_lit% retPC

def cut (s : ArmState) : Bool := cutPC (r .PC s)

def assert (s0 s : ArmState) : Prop :=
  pre s0 ∧
  if r .PC s = arm_lit% entryPC then s = s0
  else if r .PC s = arm_lit% headPC then LoopInv s0 s
  else if r .PC s = arm_lit% retPC then post s0 s
  else False

def rank (s : ArmState) : Nat :=
  if r .PC s = arm_lit% entryPC then (r (.GPR 2#5) s).toNat + 2
  else if r .PC s = arm_lit% headPC then (r (.GPR 2#5) s).toNat + 1
  else 0

#genVCGenSegment br := buildSeg SHA512.program cutPC 10 arm_lit% brPC

/-- The four stores of `st1 {v0.2d-v3.2d}, [x0]`. -/
abbrev st1W (a : BitVec 64) (v0 v1 v2 v3 : BitVec 128) (s : ArmState) : ArmState :=
  write_mem_bytes 16 (a + 48#64) v3 (write_mem_bytes 16 (a + 32#64) v2
    (write_mem_bytes 16 (a + 16#64) v1 (write_mem_bytes 16 a v0 s)))

theorem st1_mem (a : BitVec 64) (v0 v1 v2 v3 : BitVec 128) (s : ArmState) :
    (st1W a v0 v1 v2 v3 s).mem =
      (((s.mem.write_bytes 16 a v0).write_bytes 16 (a + 16#64) v1).write_bytes 16 (a + 32#64) v2).write_bytes
        16 (a + 48#64) v3 := by
  simp only [st1W, Memory.write_mem_bytes_eq_mem_write_bytes]

theorem st1_rd0 (a : BitVec 64) (h : mem_legal' a 64) (v0 v1 v2 v3 : BitVec 128) (s : ArmState) :
    (st1W a v0 v1 v2 v3 s).mem.read_bytes 16 a = v0 := by
  have hl := h.omega_def
  rw [st1_mem, Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_same (by omega)]
theorem st1_rd1 (a : BitVec 64) (h : mem_legal' a 64) (v0 v1 v2 v3 : BitVec 128) (s : ArmState) :
    (st1W a v0 v1 v2 v3 s).mem.read_bytes 16 (a + 16#64) = v1 := by
  have hl := h.omega_def
  rw [st1_mem, Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_same (by omega)]
theorem st1_rd2 (a : BitVec 64) (h : mem_legal' a 64) (v0 v1 v2 v3 : BitVec 128) (s : ArmState) :
    (st1W a v0 v1 v2 v3 s).mem.read_bytes 16 (a + 32#64) = v2 := by
  have hl := h.omega_def
  rw [st1_mem, Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_same (by omega)]
theorem st1_rd3 (a : BitVec 64) (v0 v1 v2 v3 : BitVec 128) (s : ArmState) :
    (st1W a v0 v1 v2 v3 s).mem.read_bytes 16 (a + 48#64) = v3 := by
  rw [st1_mem, Memory.read_bytes_write_bytes_same (by omega)]

theorem st1_rd_sep (a b : BitVec 64) (h : mem_separate' b 8 a 64) (v0 v1 v2 v3 : BitVec 128) (s : ArmState) :
    (st1W a v0 v1 v2 v3 s).mem.read_bytes 8 b = s.mem.read_bytes 8 b := by
  have hl := h.omega_def
  rw [st1_mem, Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega))]

theorem stack_rd (s0 : ArmState) {a : BitVec 64} {n : Nat} (h : mem_separate' a n (sp s0 - 16#64) 16) :
    (stackMem s0).read_bytes n a = s0.mem.read_bytes n a := by
  simp only [stackMem, Memory.write_mem_bytes_eq_mem_write_bytes]
  exact Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' h _

/-- The epilogue's stores leave memory outside the context unchanged. -/
theorem st1_frame (a b : BitVec 64) {n : Nat} (h : mem_separate' b n a 64) (v0 v1 v2 v3 : BitVec 128)
    (s : ArmState) : (st1W a v0 v1 v2 v3 s).mem.read_bytes n b = s.mem.read_bytes n b := by
  have hl := h.omega_def
  rw [st1_mem, Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega)),
    Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' (mem_separate'.of_omega (by bv_omega))]

/-- From the `cbnz`: back to the loop head with one more block done, or out
through the epilogue to the `ret` with the final hash stored. -/
theorem br_spec (s0 si : ArmState) (P : It) (hpre : pre s0)
    (hloop : P.x2 ≠ 0#64 →
      0 < P.x2.toNat ∧ P.x2.toNat ≤ nblk s0 ∧ P.ctx = ctx s0 ∧
      P.x1 + 128#64 = inp s0 + BitVec.ofNat 64 (128 * (nblk s0 - P.x2.toNat + 1)) ∧
      P.fp = sp s0 - 16#64 ∧ P.lr = r (.GPR 30#5) s0 ∧ P.sp = sp s0 - 16#64 ∧
      P.mem = stackMem s0 ∧ P.base = s0 ∧
      add_hash P.H (rounds P.H P.w 80) = hashAt s0 (nblk s0 - P.x2.toNat) ∧
      (∀ q < 8, nbv P q = msgPair s0 (nblk s0 - P.x2.toNat) q) ∧
      P.x2.toNat + 1 < rank si)
    (hexit : P.x2 = 0#64 →
      P.ctx = ctx s0 ∧ mem_legal' P.ctx 64 ∧ mem_separate' P.sp 8 P.ctx 64 ∧
      P.sp = sp s0 - 16#64 ∧ P.lr = r (.GPR 30#5) s0 ∧ P.mem = stackMem s0 ∧ P.base = s0 ∧
      P.mem.read_bytes 8 P.sp = r (.GPR 29#5) s0 ∧
      add_hash P.H (rounds P.H P.w 80) = Hfin s0 ∧ 0 < rank si) :
    ⦃ TI P ⦄ br ⦃ fun _ s => cut s = true ∧ assert s0 s ∧ rank s < rank si ⦄ := by
  by_cases hx : P.x2 = 0#64
  · have h := hexit hx; clear hloop hexit
    simp only [rank] at h
    have e0 := st1_rd0 _ h.2.1
    have e1 := st1_rd1 _ h.2.1
    have e2 := st1_rd2 _ h.2.1
    have es := st1_rd_sep _ _ h.2.2.1
    simp only [h.1, h.2.2.2.1] at e0 e1 e2 es
    obtain ⟨hctx, -, -, hsp, hlr, hpm, hbase, hx29, hfin, hrank⟩ := h
    rw [hsp] at hx29
    unfold br
    vcgen
    all_goals first
      | arm_vc_step
      | exact (‹TI P _›).1
      | (simp only [TI, cut, cutPC, assert, LoopInv, post, rank, regFrame, Prod.mk.injEq, List.cons.injEq, and_true] at *
         arm_vc_final_with [Memory.State.read_mem_bytes_eq_mem_read_bytes, e0, e1, e2, st1_rd3, es]
         -- The memory frame.
         all_goals
           intro n a h1 h2
           rw [st1_frame _ _ h2, ArmState.mem_w_eq_mem]
           simp_all only [stack_rd s0 h1])
  · have h := hloop hx; clear hloop hexit
    simp only [rank] at h
    unfold br
    vcgen
    all_goals first
      | arm_vc_step
      | exact (‹TI P _›).1
      | (simp only [TI, cut, cutPC, assert, LoopInv, post, rank, regFrame, Prod.mk.injEq, List.cons.injEq, and_true] at *
         arm_vc_final_with [Memory.State.read_mem_bytes_eq_mem_read_bytes])

/-! ## Memory: the stack frame is separate from what the loop reads -/

theorem toNat_add_ofNat {base : BitVec 64} {off : Nat} (h : base.toNat + off < 2 ^ 64) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A 16-byte piece of a region separate from `b`. -/
theorem sep_sub {b base : BitVec 64} {bn len off : Nat} (h : mem_separate' b bn base len)
    (hoff : off + 16 ≤ len) : mem_separate' (base + BitVec.ofNat 64 off) 16 b bn := by
  have h' := h.omega_def
  have := toNat_add_ofNat (base := base) (off := off) (by omega)
  exact mem_separate'.of_omega (by omega)

theorem blkA_eq (s0 : ArmState) (i q : Nat) :
    blkA s0 i q = inp s0 + BitVec.ofNat 64 (128 * i + 16 * q) := by
  simp only [blkA, BitVec.add_assoc, BitVec.ofNat_add]

theorem stack_rd_blk (s0 : ArmState) (hpre : pre s0) {i q : Nat} (hi : i < nblk s0) (hq : q < 8) :
    (stackMem s0).read_bytes 16 (blkA s0 i q) = s0.mem.read_bytes 16 (blkA s0 i q) := by
  apply stack_rd
  rw [blkA_eq]
  exact sep_sub hpre.sep_inp (by
    have : i + 1 ≤ nblk s0 := hi
    have : 128 * (i + 1) ≤ 128 * nblk s0 := Nat.mul_le_mul_left _ this
    omega)

theorem stack_rd_kt (s0 : ArmState) (hpre : pre s0) {j : Nat} (hj : j < 40) :
    (stackMem s0).read_bytes 16 (kt + BitVec.ofNat 64 (16 * j)) = Kp j := by
  rw [stack_rd s0 (sep_sub hpre.sep_kt (by omega)), ← Memory.State.read_mem_bytes_eq_mem_read_bytes]
  exact hpre.ktbl j hj

theorem stack_rd_ctx (s0 : ArmState) (hpre : pre s0) {j : Nat} (hj : j < 4) :
    (stackMem s0).read_bytes 16 (ctx s0 + BitVec.ofNat 64 (16 * j)) =
      s0.mem.read_bytes 16 (ctx s0 + BitVec.ofNat 64 (16 * j)) :=
  stack_rd s0 (sep_sub hpre.sep_ctx (by omega))

theorem stack_rd_fp (s0 : ArmState) (hpre : pre s0) :
    (stackMem s0).read_bytes 8 (sp s0 - 16#64) = r (.GPR 29#5) s0 := by
  have h := hpre.sep_ctx.omega_def
  simp only [stackMem, Memory.write_mem_bytes_eq_mem_write_bytes]
  rw [Memory.read_bytes_write_bytes_eq_of_mem_subset' (mem_subset'.of_omega (by omega)), Nat.sub_self]
  exact lo_of_append _ _

/-! ## Facts about the specification functions -/

theorem Wp_msched (s0 : ArmState) (i q : Nat) (hq : q < 8) :
    Wp (msched s0 i) q = msgPair s0 i q := by
  simp only [Wp, msched]
  rw [message_schedule_word]
  simp only [show 2 * q + 1 ≤ 15 by omega, dite_true]
  rw [message_schedule_word]
  simp only [show 2 * q ≤ 15 by omega, dite_true]
  simp only [msgWords, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show 2 * q + 1 < 16 by omega), List.getElem?_range (show 2 * q < 16 by omega),
    Option.map_some, Option.getD_some, show (2 * q + 1) % 2 = 1 by omega, show (2 * q) % 2 = 0 by omega,
    show (2 * q + 1) / 2 = q by omega, show 2 * q / 2 = q by omega, ↓reduceIte, Nat.one_ne_zero]
  exact (split128 _).symm

theorem WRec_msched (s0 : ArmState) (i : Nat) : WRec (msched s0 i) :=
  fun _ hu => message_schedule_word_rec _ hu

theorem hashAt_zero (s0 : ArmState) : hashAt s0 0 = H0 s0 := by
  simp [hashAt, processBlocks_alt]

theorem pb_append (j : Nat) (h : Hash) (k : List (BitVec 64)) (l₁ l₂ : List (List (BitVec 64))) :
    processBlocks_alt j h k (l₁ ++ l₂) = processBlocks_alt j (processBlocks_alt j h k l₁) k l₂ := by
  induction l₁ generalizing h with
  | nil => rfl
  | cons m rest ih => simp only [List.cons_append, processBlocks_alt, ih]

theorem comp_rounds (H : Hash) (m : List (BitVec 64)) :
    ∀ d i, i + d = 80 → compression_alt i 80 (rounds H (fun t => message_schedule_word t m) i) k_512 m =
      rounds H (fun t => message_schedule_word t m) 80 := by
  intro d
  induction d with
  | zero => intro i hi; subst hi; rw [compression_alt]; simp
  | succ d ih =>
    intro i hi
    rw [compression_alt]
    simp only [show i < 80 by omega, ↓reduceIte]
    exact ih (i + 1) (by omega)

theorem hashAt_succ (s0 : ArmState) {i : Nat} (hi : i < nblk s0) :
    hashAt s0 (i + 1) = add_hash (hashAt s0 i) (rounds (hashAt s0 i) (msched s0 i) 80) := by
  have hl : (blocks s0).length = nblk s0 := by simp [blocks]
  have ht : (blocks s0).take (i + 1) = (blocks s0).take i ++ [msgWords s0 i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp [blocks]
  simp only [hashAt, ht, pb_append, processBlocks_alt]
  rw [show (0 : Nat) = 0 from rfl]
  have := comp_rounds (processBlocks_alt j_512 (H0 s0) k_512 (List.take i (blocks s0))) (msgWords s0 i) 80 0 rfl
  simp only [rounds_zero, j_512] at this ⊢
  rw [this]; rfl

theorem Hfin_eq (s0 : ArmState) : Hfin s0 = hashAt s0 (nblk s0) := by
  simp only [Hfin, hashAt]
  rw [List.take_of_length_le (by simp [blocks])]

theorem lA_ofLanes (v0 v1 v2 v3 : BitVec 128) : lA (ofLanes v0 v1 v2 v3) = v0 := (split128 v0).symm
theorem lB_ofLanes (v0 v1 v2 v3 : BitVec 128) : lB (ofLanes v0 v1 v2 v3) = v1 := (split128 v1).symm
theorem lC_ofLanes (v0 v1 v2 v3 : BitVec 128) : lC (ofLanes v0 v1 v2 v3) = v2 := (split128 v2).symm
theorem lD_ofLanes (v0 v1 v2 v3 : BitVec 128) : lD (ofLanes v0 v1 v2 v3) = v3 := (split128 v3).symm

#genVCGenSegment pro := buildSeg SHA512.program cutPC 30 arm_lit% entryPC

theorem add_eq_sub_16 (x : BitVec 64) : x + 0xfffffffffffffff0#64 = x - 16#64 := by bv_decide

theorem mem_stack (s0 : ArmState) :
    (write_mem_bytes 16 (sp s0 - 16#64) (r (.GPR 30#5) s0 ++ r (.GPR 29#5) s0) s0).mem = stackMem s0 := rfl

/-- The prologue, from the entry to the loop head with no block done. -/
theorem pro_spec (s0 : ArmState) (hpre : pre s0) :
    ⦃ fun s => s = s0 ⦄ pro ⦃ fun _ s => cut s = true ∧ assert s0 s ∧ rank s < rank s0 ⦄ := by
  have hc0 := stack_rd_ctx s0 hpre (j := 0) (by decide)
  have hc1 := stack_rd_ctx s0 hpre (j := 1) (by decide)
  have hc2 := stack_rd_ctx s0 hpre (j := 2) (by decide)
  have hc3 := stack_rd_ctx s0 hpre (j := 3) (by decide)
  have hm0 := stack_rd_blk s0 hpre (i := 0) (q := 0) hpre.nblk_pos (by decide)
  have hm1 := stack_rd_blk s0 hpre (i := 0) (q := 1) hpre.nblk_pos (by decide)
  have hm2 := stack_rd_blk s0 hpre (i := 0) (q := 2) hpre.nblk_pos (by decide)
  have hm3 := stack_rd_blk s0 hpre (i := 0) (q := 3) hpre.nblk_pos (by decide)
  have hm4 := stack_rd_blk s0 hpre (i := 0) (q := 4) hpre.nblk_pos (by decide)
  have hm5 := stack_rd_blk s0 hpre (i := 0) (q := 5) hpre.nblk_pos (by decide)
  have hm6 := stack_rd_blk s0 hpre (i := 0) (q := 6) hpre.nblk_pos (by decide)
  have hm7 := stack_rd_blk s0 hpre (i := 0) (q := 7) hpre.nblk_pos (by decide)
  simp only [blkA, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hc0 hc1 hc2 hc3 hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7
  have hp := hpre
  simp only [pre] at hp
  unfold pro
  vcgen
  all_goals first
    | arm_vc_step
    | (subst_vars; exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩)
    | (subst_vars
       simp only [cut, cutPC, assert, LoopInv, rank, msgPair, blkA, stackMem, regFrame, Prod.mk.injEq, List.cons.injEq, and_true] at *
       arm_vc_final_with [add_eq_sub_16, BitVec.add_assoc, BitVec.reduceAdd, Nat.sub_self,
         Memory.State.read_mem_bytes_eq_mem_read_bytes, hashAt_zero, H0, lA_ofLanes, lB_ofLanes,
         lC_ofLanes, lD_ofLanes, Nat.add_lt_add_iff_left])

/-! ## One iteration -/

theorem x2_facts {x : BitVec 64} (h0 : 0 < x.toNat) : (x - 1#64).toNat = x.toNat - 1 := by bv_omega

theorem ofNat_step (n : Nat) : BitVec.ofNat 64 (128 * n) + 128#64 = BitVec.ofNat 64 (128 * (n + 1)) := by
  rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]

/-- At the `cbnz` of an iteration that continues the loop: `x2` is still
positive, `x1` points at the next block, and the hash and message registers
hold the next iteration's values. -/
theorem loop_facts (s0 si : ArmState) (hpre : pre s0) (hI : LoopInv s0 si) :
    let P := itOf s0 si
    P.x2 ≠ 0#64 →
      0 < P.x2.toNat ∧ P.x2.toNat ≤ nblk s0 ∧ P.ctx = ctx s0 ∧
      P.x1 + 128#64 = inp s0 + BitVec.ofNat 64 (128 * (nblk s0 - P.x2.toNat + 1)) ∧
      P.fp = sp s0 - 16#64 ∧ P.lr = r (.GPR 30#5) s0 ∧ P.sp = sp s0 - 16#64 ∧
      P.mem = stackMem s0 ∧ P.base = s0 ∧
      add_hash P.H (rounds P.H P.w 80) = hashAt s0 (nblk s0 - P.x2.toNat) ∧
      (∀ q < 8, nbv P q = msgPair s0 (nblk s0 - P.x2.toNat) q) ∧
      P.x2.toNat + 1 < rank si := by
  intro P hx
  obtain ⟨hside, hpos, hle, -, hx1, -, -, -, -, hmem, -⟩ := hI
  have hpc : r .PC si = arm_lit% headPC := hside.2.1
  have hx' : r (.GPR 2#5) si - 1#64 ≠ 0#64 := hx
  have ht := x2_facts hpos
  have hge : 2 ≤ (r (.GPR 2#5) si).toNat := by bv_omega
  have hidx : nblk s0 - (r (.GPR 2#5) si - 1#64).toNat = nblk s0 - (r (.GPR 2#5) si).toNat + 1 := by
    rw [ht]; omega
  simp (config := { decide := true }) only [P, itOf, hx', ↓reduceIte, hidx, rank, hpc, true_and]
  refine ⟨by omega, by omega, ?_, hmem, ?_, ?_, by omega⟩
  · rw [hx1, BitVec.add_assoc, ofNat_step]
  · exact (hashAt_succ s0 (by omega)).symm
  · intro q hq
    simp only [nbv, hmem, hx1]
    rw [show inp s0 + BitVec.ofNat 64 (128 * (nblk s0 - (r (.GPR 2#5) si).toNat + 1)) +
        BitVec.ofNat 64 (16 * q) = blkA s0 (nblk s0 - (r (.GPR 2#5) si).toNat + 1) q from rfl,
      stack_rd_blk s0 hpre (by omega) hq, msgPair, Memory.State.read_mem_bytes_eq_mem_read_bytes]

/-- At the `cbnz` of the last iteration: the stores and the frame-pointer load
of the epilogue are separate, and the hash registers hold `Hfin`. -/
theorem exit_facts (s0 si : ArmState) (hpre : pre s0) (hI : LoopInv s0 si) :
    let P := itOf s0 si
    P.x2 = 0#64 →
      P.ctx = ctx s0 ∧ mem_legal' P.ctx 64 ∧ mem_separate' P.sp 8 P.ctx 64 ∧
      P.sp = sp s0 - 16#64 ∧ P.lr = r (.GPR 30#5) s0 ∧ P.mem = stackMem s0 ∧ P.base = s0 ∧
      P.mem.read_bytes 8 P.sp = r (.GPR 29#5) s0 ∧
      add_hash P.H (rounds P.H P.w 80) = Hfin s0 ∧ 0 < rank si := by
  intro P hx
  obtain ⟨hside, hpos, hle, -, -, -, -, -, -, hmem, -⟩ := hI
  have hpc : r .PC si = arm_lit% headPC := hside.2.1
  have hx' : r (.GPR 2#5) si - 1#64 = 0#64 := hx
  have h1 : (r (.GPR 2#5) si).toNat = 1 := by bv_omega
  have hsep := hpre.sep_ctx
  have hs := hsep.omega_def
  simp (config := { decide := true }) only [P, itOf, rank, hpc, ↓reduceIte, true_and]
  refine ⟨hsep.hb, mem_separate'.of_omega ?_, hmem, by rw [hmem, stack_rd_fp s0 hpre], ?_, by omega⟩
  · omega
  have h := hashAt_succ s0 (i := nblk s0 - (r (.GPR 2#5) si).toNat) (by omega)
  rw [show nblk s0 - (r (.GPR 2#5) si).toNat + 1 = nblk s0 by omega] at h
  rw [Hfin_eq, h]

/-- The loop, from the loop head back to it or out to the `ret`. -/
noncomputable abbrev body : ArmCmd :=
  .seq hdr (.seq g0 (.seq g1 (.seq g2 (.seq g3 (.seq g4 (.seq g5 (.seq g6 (.seq g7 (.seq g8 (.seq g9 (.seq g10 (.seq g11 (.seq g12 (.seq g13 (.seq g14 (.seq g15 (.seq g16 (.seq g17 (.seq g18 (.seq g19 (.seq g20 (.seq g21 (.seq g22 (.seq g23 (.seq g24 (.seq g25 (.seq g26 (.seq g27 (.seq g28 (.seq g29 (.seq g30 (.seq g31 (.seq g32 (.seq g33 (.seq g34 (.seq g35 (.seq g36 (.seq g37 (.seq g38 (.seq g39 (.seq tail br)))))))))))))))))))))))))))))))))))))))))

/-- One iteration of the loop: the composition of the header, the 40 groups,
the tail and the branch. -/
theorem body_spec (s0 si : ArmState) (hpre : pre s0) (hI : LoopInv s0 si) :
    ⦃ fun s => s = si ⦄ body ⦃ fun _ s => cut s = true ∧ assert s0 s ∧ rank s < rank si ⦄ := by
  have hmem : si.mem = stackMem s0 := hI.mem
  have hK : ∀ k, k < 39 → (itOf s0 si).mem.read_bytes 16 (ktX k) = Kp (k + 1) := by
    intro k hk
    simp only [itOf, ktX, show k < 40 by omega, ↓reduceIte, hmem]
    exact stack_rd_kt s0 hpre (by omega)
  have hK0 : si.mem.read_bytes 16 kt = Kp 0 := by
    have := stack_rd_kt s0 hpre (j := 0) (by decide)
    simpa [hmem] using this
  have hw := WRec_msched s0 (nblk s0 - (r (.GPR 2#5) si).toNat)
  apply triple_seq (hdr_spec s0 si hI hK0 (fun q hq => Wp_msched s0 _ q hq))
  apply triple_seq (g0_spec _ (hK 0) hw)
  apply triple_seq (g1_spec _ (hK 1) hw)
  apply triple_seq (g2_spec _ (hK 2) hw)
  apply triple_seq (g3_spec _ (hK 3) hw)
  apply triple_seq (g4_spec _ (hK 4) hw)
  apply triple_seq (g5_spec _ (hK 5) hw)
  apply triple_seq (g6_spec _ (hK 6) hw)
  apply triple_seq (g7_spec _ (hK 7) hw)
  apply triple_seq (g8_spec _ (hK 8) hw)
  apply triple_seq (g9_spec _ (hK 9) hw)
  apply triple_seq (g10_spec _ (hK 10) hw)
  apply triple_seq (g11_spec _ (hK 11) hw)
  apply triple_seq (g12_spec _ (hK 12) hw)
  apply triple_seq (g13_spec _ (hK 13) hw)
  apply triple_seq (g14_spec _ (hK 14) hw)
  apply triple_seq (g15_spec _ (hK 15) hw)
  apply triple_seq (g16_spec _ (hK 16) hw)
  apply triple_seq (g17_spec _ (hK 17) hw)
  apply triple_seq (g18_spec _ (hK 18) hw)
  apply triple_seq (g19_spec _ (hK 19) hw)
  apply triple_seq (g20_spec _ (hK 20) hw)
  apply triple_seq (g21_spec _ (hK 21) hw)
  apply triple_seq (g22_spec _ (hK 22) hw)
  apply triple_seq (g23_spec _ (hK 23) hw)
  apply triple_seq (g24_spec _ (hK 24) hw)
  apply triple_seq (g25_spec _ (hK 25) hw)
  apply triple_seq (g26_spec _ (hK 26) hw)
  apply triple_seq (g27_spec _ (hK 27) hw)
  apply triple_seq (g28_spec _ (hK 28) hw)
  apply triple_seq (g29_spec _ (hK 29) hw)
  apply triple_seq (g30_spec _ (hK 30) hw)
  apply triple_seq (g31_spec _ (hK 31) hw)
  apply triple_seq (g32_spec _ (hK 32) hw)
  apply triple_seq (g33_spec _ (hK 33) hw)
  apply triple_seq (g34_spec _ (hK 34) hw)
  apply triple_seq (g35_spec _ (hK 35) hw)
  apply triple_seq (g36_spec _ (hK 36) hw)
  apply triple_seq (g37_spec _ (hK 37) hw)
  apply triple_seq (g38_spec _ (hK 38) hw)
  apply triple_seq (g39_spec _ (hK 39) hw)
  apply triple_seq (tail_spec _)
  exact br_spec s0 si _ hpre (loop_facts s0 si hpre hI) (exit_facts s0 si hpre hI)

/-! ## Total correctness -/

/-- The specification `correctness` is about: `pre`, `post` and `exit` (the
`ret`), with the cut points and assertions used to prove it. Local, so that
importers do not get it implicitly and `Correctness ArmState` below is about
this instance. -/
local instance spec : Spec' ArmState where
  pre := pre
  post := post
  exit := exit
  cut := cut
  assert := assert

theorem cut_eq_cutPC (s : ArmState) : Spec'.cut s = cutPC (r .PC s) := rfl

/-- **Total correctness of `sha512_block_armv8`**: from any state satisfying
`pre`, the program reaches the `ret`, and there `post` holds: the context holds
`processBlocks_alt` of the input blocks, starting from the hash in the context. -/
theorem correctness : Correctness ArmState := by
  apply Correctness.by_the_method rank
  case v1 =>
    intro s0 h
    simp only [Spec.pre, Spec'.assert, assert] at h ⊢
    exact ⟨h, by simp [h.2.1]⟩
  case v2 =>
    intro sf h
    simp only [Spec.exit, exit] at h
    simp [Spec'.cut, cut, cutPC, h]
  case v3 =>
    intro s0 sf hA hex
    simp only [Spec.exit, exit] at hex
    simp only [Spec'.assert, assert, hex] at hA
    simpa [Spec.post] using hA.2
  case v4 =>
    intro s0 si hA hex
    simp only [Spec.exit, exit] at hex
    simp only [Spec'.assert, assert] at hA
    obtain ⟨hpre, hA⟩ := hA
    split at hA
    · subst hA
      exact ArmVCGen.by_the_method_v4_of_triple cut_eq_cutPC (by arm_pcs [cutPC]) rank
        (pre := fun _ => True) (triple_pre (pro_spec si hpre) (fun s h => h.1)) trivial
    · split at hA
      · exact ArmVCGen.by_the_method_v4_of_triple cut_eq_cutPC (by arm_pcs [cutPC]) rank
          (pre := fun _ => True) (triple_reassoc (triple_pre (body_spec s0 si hpre hA) (fun s h => h.1))) trivial
      · exfalso
        first
          | exact hA
          | (split at hA
             · exact hex ‹_›
             · exact hA)

/-! ## The theorem in the specification's terms

`correctness` states the context and the input as the program loads them
(128-bit lanes, `rev64` of 16-byte loads). `sha512_correct` states them in the
specification's terms: the context is `Hash.toBitVec`, the input is big-endian
64-bit words, and the table is `flatten k_512.reverse`. -/

/-- The round-constant table as one 640-byte value, `K[0]` at the lowest address. -/
def ktBytes : BitVec (640 * 8) := (BitVec.flatten k_512.reverse).cast (by decide)

/-- The big-endian reading of 8 bytes loaded little-endian: the byte at the
lowest address is the most significant. -/
def be64 (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
  x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8

/-- The hash `H` with `H.toBitVec = x` (`a` in the low 64 bits). -/
def hashOfBitVec (x : BitVec 512) : Hash :=
  ⟨x.extractLsb' 0 64, x.extractLsb' 64 64, x.extractLsb' 128 64, x.extractLsb' 192 64,
   x.extractLsb' 256 64, x.extractLsb' 320 64, x.extractLsb' 384 64, x.extractLsb' 448 64⟩

/-- The input: `N = x2` blocks of 16 big-endian 64-bit words at `x1`. -/
def inputBlocks (s0 : ArmState) : List (List (BitVec 64)) :=
  (List.range (nblk s0)).map fun i => (List.range 16).map fun j =>
    be64 (read_mem_bytes 8 (inp s0 + BitVec.ofNat 64 (128 * i + 8 * j)) s0)

theorem vrev_eq (x : BitVec 128) :
    vrev128_64_8 x = rev_elems 64 8 (x.extractLsb' 64 64) (by decide) (by decide) ++
      rev_elems 64 8 (x.extractLsb' 0 64) (by decide) (by decide) := by
  simp only [vrev128_64_8]
  unfold rev_vector
  simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
  unfold rev_vector
  simp (config := {decide := true}) only [bitvec_rules, minimal_theory]
  exact rfl

theorem rev_elems_be (y : BitVec 64) : rev_elems 64 8 y (by decide) (by decide) = be64 y := by
  repeat (unfold rev_elems; simp (config := {decide := true}) only [bitvec_rules, minimal_theory])
  simp only [be64]
  bv_decide

theorem lo_vrev (x : BitVec 128) : (vrev128_64_8 x).extractLsb' 0 64 = be64 (x.extractLsb' 0 64) := by
  rw [vrev_eq, lo_of_append, rev_elems_be]
theorem hi_vrev (x : BitVec 128) : (vrev128_64_8 x).extractLsb' 64 64 = be64 (x.extractLsb' 64 64) := by
  rw [vrev_eq, hi_of_append, rev_elems_be]

/-- Reading a sub-range of a region read as one value. -/
theorem rd_sub {mem : Memory} {b a : BitVec 64} {bn an : Nat} {v : BitVec (bn * 8)}
    (hv : mem.read_bytes bn b = v) (hl : b.toNat + bn ≤ 2 ^ 64) {off : Nat} (han : 0 < an) (hoff : off + an ≤ bn)
    (ha : a = b + BitVec.ofNat 64 off) : mem.read_bytes an a = v.extractLsBytes off an := by
  have hb : (b + BitVec.ofNat 64 off).toNat = b.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  subst ha
  rw [Memory.read_bytes_eq_extractLsBytes_sub_of_mem_subset' hv (mem_subset'.of_omega (by omega)), hb,
    show b.toNat + off - b.toNat = off by omega]

/-- `pre`, with the round-constant table as one 640-byte read. -/
def preS (s0 : ArmState) : Prop :=
  s0.program = SHA512.program ∧ r .PC s0 = arm_lit% entryPC ∧ r .ERR s0 = .None ∧ CheckSPAlignment s0 ∧
  0 < nblk s0 ∧
  read_mem_bytes 640 kt s0 = ktBytes ∧
  mem_separate' (sp s0 - 16#64) 16 (ctx s0) 64 ∧
  mem_separate' (sp s0 - 16#64) 16 (inp s0) (nblk s0 * 128) ∧
  mem_separate' (sp s0 - 16#64) 16 kt 640

/-- `post`, with the context as one 64-byte read of `Hash.toBitVec`. -/
def postS (s0 sf : ArmState) : Prop :=
  read_mem_bytes 64 (ctx s0) sf =
    (processBlocks_alt j_512 (hashOfBitVec (read_mem_bytes 64 (ctx s0) s0)) k_512
      (inputBlocks s0)).toBitVec ∧
  r (.GPR 29#5) sf = r (.GPR 29#5) s0 ∧ r (.GPR 30#5) sf = r (.GPR 30#5) s0 ∧
  r (.GPR 0#5) sf = r (.GPR 0#5) s0 ∧ regFrame sf = regFrame s0 ∧
  sp sf = sp s0 ∧
  sf.program = SHA512.program ∧ r .PC sf = arm_lit% retPC ∧ r .ERR sf = .None ∧
  (∀ n a, mem_separate' a n (sp s0 - 16#64) 16 → mem_separate' a n (ctx s0) 64 →
    read_mem_bytes n a sf = read_mem_bytes n a s0)

theorem pre_of_preS {s0 : ArmState} (h : preS s0) : pre s0 := by
  obtain ⟨hp, hpc, he, ha, hn, hk, h1, h2, h3⟩ := h
  refine ⟨hp, hpc, he, ha, hn, ?_, h1, h2, h3⟩
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes] at hk
  have hl := h3.hb.omega_def
  intro j hj
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes,
    rd_sub hk hl (an := 16) (off := 16 * j) (by omega) (by omega) rfl]
  revert j hj; decide +kernel

theorem ofLanes_eq (Y : BitVec 512) :
    ofLanes (Y.extractLsb' 0 128) (Y.extractLsb' 128 128) (Y.extractLsb' 256 128)
      (Y.extractLsb' 384 128) = hashOfBitVec Y := by
  simp only [ofLanes, hashOfBitVec, Hash.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem H0_eq {s0 : ArmState} (hl : (ctx s0).toNat + 64 ≤ 2 ^ 64) :
    H0 s0 = hashOfBitVec (read_mem_bytes 64 (ctx s0) s0) := by
  have hY : s0.mem.read_bytes 64 (ctx s0) = s0.mem.read_bytes 64 (ctx s0) := rfl
  simp only [H0, Memory.State.read_mem_bytes_eq_mem_read_bytes]
  rw [rd_sub hY hl (an := 16) (off := 0) (by omega) (by omega) (by simp),
    rd_sub hY hl (an := 16) (off := 16) (by omega) (by omega) rfl,
    rd_sub hY hl (an := 16) (off := 32) (by omega) (by omega) rfl,
    rd_sub hY hl (an := 16) (off := 48) (by omega) (by omega) rfl]
  exact ofLanes_eq _

theorem blocks_eq {s0 : ArmState} (hl : (inp s0).toNat + nblk s0 * 128 ≤ 2 ^ 64) :
    blocks s0 = inputBlocks s0 := by
  simp only [blocks, inputBlocks]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  have hq : j / 2 < 8 := by omega
  -- The 16-byte load the program does, and its two halves.
  have hA : (blkA s0 i (j / 2)).toNat + 16 ≤ 2 ^ 64 := by
    rw [blkA_eq, toNat_add_ofNat (by omega)]
    have : 128 * i + 16 * (j / 2) + 16 ≤ nblk s0 * 128 := by omega
    omega
  have hY : s0.mem.read_bytes 16 (blkA s0 i (j / 2)) = s0.mem.read_bytes 16 (blkA s0 i (j / 2)) := rfl
  simp only [msgPair, Memory.State.read_mem_bytes_eq_mem_read_bytes]
  split
  · rw [lo_vrev, rd_sub hY hA (an := 8) (off := 0) (by omega) (by omega)
      (by rw [blkA_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega)]
    rfl
  · rw [hi_vrev, rd_sub hY hA (an := 8) (off := 8) (by omega) (by omega)
      (by rw [blkA_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega)]
    rfl

theorem toBitVec_of_lanes (Y : BitVec 512) (H : Hash)
    (h0 : Y.extractLsb' 0 128 = lA H) (h1 : Y.extractLsb' 128 128 = lB H)
    (h2 : Y.extractLsb' 256 128 = lC H) (h3 : Y.extractLsb' 384 128 = lD H) :
    Y = H.toBitVec := by
  simp only [lA, lB, lC, lD, Hash.toBitVec] at *
  bv_decide

theorem postS_of_post {s0 sf : ArmState} (hs : preS s0) (h : post s0 sf) : postS s0 sf := by
  have hl := (pre_of_preS hs).sep_ctx.hb.omega_def
  obtain ⟨l0, l1, l2, l3, rest⟩ := h
  refine ⟨?_, rest⟩
  rw [← H0_eq hl, ← blocks_eq (pre_of_preS hs).sep_inp.hb.omega_def]
  have hY : sf.mem.read_bytes 64 (ctx s0) = sf.mem.read_bytes 64 (ctx s0) := rfl
  simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes] at l0 l1 l2 l3 ⊢
  rw [rd_sub hY hl (an := 16) (off := 0) (by omega) (by omega) (by simp)] at l0
  rw [rd_sub hY hl (an := 16) (off := 16) (by omega) (by omega) rfl] at l1
  rw [rd_sub hY hl (an := 16) (off := 32) (by omega) (by omega) rfl] at l2
  rw [rd_sub hY hl (an := 16) (off := 48) (by omega) (by omega) rfl] at l3
  exact toBitVec_of_lanes _ _ l0 l1 l2 l3

/-- The specification `sha512_correct` is about. -/
abbrev specification : Spec ArmState where
  pre := preS
  post := postS
  exit := exit

/-- **Total correctness of `sha512_block_armv8`.** From any state satisfying
`preS` (the program loaded and at its entry, `x2 ≥ 1` blocks of input at `x1`,
the round-constant table `k_512` at `kt`, the 16-byte stack frame below `sp`
separate from the context, the input and the table), the program reaches its
`ret`, and there `postS` holds: the 64-byte context at `x0` holds
`(processBlocks_alt 80 H k_512 blocks).toBitVec`, where `H` is the hash the
context held on entry and `blocks` are the input's big-endian 64-bit words;
`x0`, `x29`, `x30`, `sp` and the registers the program does not write are
unchanged, and so is memory outside the stack frame and the context. -/
theorem sha512_correct : @Correctness ArmState _ specification := by
  obtain ⟨hp, ht⟩ := correctness
  refine ⟨fun s n hs hex => ?_, fun s hs => ht s (pre_of_preS hs)⟩
  obtain ⟨m, hm, hexm, hpost⟩ := hp s n (pre_of_preS hs) hex
  exact ⟨m, hm, hexm, postS_of_post hs hpost⟩

/-! ## `preS` is satisfiable

A concrete state satisfies `preS` (and so `pre`), so `sha512_correct` and
`correctness` are not vacuous. -/

/-- Zero memory with the table at `kt`. -/
def demoMem : Memory := Memory.write_bytes 640 kt ktBytes (fun _ => 0#8)

/-- A state satisfying `pre`: one block at `0x30000`, the context at `0x20000`,
the stack pointer at `0x10000`, and the table at `kt`. -/
def demo : ArmState :=
  { gpr := fun i => if i = 0#5 then 0x20000#64 else if i = 1#5 then 0x30000#64
      else if i = 2#5 then 1#64 else if i = 31#5 then 0x10000#64 else 0#64,
    sfp := fun _ => 0#128, pc := entryPC, pstate := PState.zero,
    mem := demoMem,
    program := SHA512.program, error := .None }

theorem preS_demo : preS demo := by
  refine ⟨by rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, demo, demoMem]
  exact Memory.read_bytes_write_bytes_same (by decide)

theorem preS_satisfiable : ∃ s, preS s := ⟨demo, preS_demo⟩

theorem pre_satisfiable : ∃ s, pre s := ⟨demo, pre_of_preS preS_demo⟩

end SHA512VCGen
