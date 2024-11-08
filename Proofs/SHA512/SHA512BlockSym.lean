/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Proofs.SHA512.SHA512LoopBlocks
-- import Proofs.SHA512.SHA512LoopBlocks2
import Tactics.SymBlock
import Tactics.ClearNamed

open BitVec

namespace SHA512
#eval SHA2.k_512.length

#time
set_option trace.Tactic.sym.info true in
set_option trace.Tactic.sym true in
set_option pp.maxSteps 100 in
theorem sha512_loop_sym {s0 sf : ArmState}
 { a b c d e f g h
   i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
   k0 k1
   : BitVec 64 }
  (h_program : s0.program = program)
  (h_pc : r StateField.PC s0 = 0x126500#64)
  (h_err : r StateField.ERR s0 = StateError.None)
  (h_N : N = 1#64)
  (h_precondition : SHA512.prelude 0x126500#64 N SP CtxBase InputBase s0)
  (h_q0  : r (.SFP  0#5) s0 = b ++ a)
  (h_q1  : r (.SFP  1#5) s0 = d ++ c)
  (h_q2  : r (.SFP  2#5) s0 = f ++ e)
  (h_q3  : r (.SFP  3#5) s0 = h ++ g)
  (h_q16 : r (.SFP 16#5) s0 = i1 ++ i0)
  (h_q17 : r (.SFP 17#5) s0 = i3 ++ i2)
  (h_q18 : r (.SFP 18#5) s0 = i5 ++ i4)
  (h_q19 : r (.SFP 19#5) s0 = i7 ++ i6)
  (h_q20 : r (.SFP 20#5) s0 = i9 ++ i8)
  (h_q21 : r (.SFP 21#5) s0 = i11 ++ i10)
  (h_q22 : r (.SFP 22#5) s0 = i13 ++ i12)
  (h_q23 : r (.SFP 23#5) s0 = i15 ++ i14)

--   (h_ktbl0  : s0[r (.GPR 3#5) s0,         16] = k1 ++ k0)
--   (h_ktbl1  : s0[r (.GPR 3#5) s0 + 16,    16] = k3 ++ k2)
--   (h_ktbl2  : s0[r (.GPR 3#5) s0 + 16*2,  16] = k5 ++ k4)
--   (h_ktbl3  : s0[r (.GPR 3#5) s0 + 16*3,  16] = k7 ++ k6)
--
--   (h_ktbl4  : s0[r (.GPR 3#5) s0 + 16*4,  16] = k9 ++ k8)
--   (h_ktbl5  : s0[r (.GPR 3#5) s0 + 16*5,  16] = k11 ++ k10)
--   (h_ktbl6  : s0[r (.GPR 3#5) s0 + 16*6,  16] = k13 ++ k12)
--   (h_ktbl7  : s0[r (.GPR 3#5) s0 + 16*7,  16] = k15 ++ k14)
--
--   (h_ktbl8  : s0[r (.GPR 3#5) s0 + 16*8,  16] = k17 ++ k16)
--   (h_ktbl9  : s0[r (.GPR 3#5) s0 + 16*9,  16] = k19 ++ k18)
--   (h_ktbl10 : s0[r (.GPR 3#5) s0 + 16*10, 16] = k21 ++ k20)
--   (h_ktbl11 : s0[r (.GPR 3#5) s0 + 16*11, 16] = k23 ++ k22)
--
--   (h_ktbl12 : s0[r (.GPR 3#5) s0 + 16*12, 16] = k25 ++ k24)
--   (h_ktbl13 : s0[r (.GPR 3#5) s0 + 16*13, 16] = k27 ++ k26)
--   (h_ktbl14 : s0[r (.GPR 3#5) s0 + 16*14, 16] = k29 ++ k28)
--   (h_ktbl15 : s0[r (.GPR 3#5) s0 + 16*15, 16] = k31 ++ k30)
--
--   (h_ktbl16 : s0[r (.GPR 3#5) s0 + 16*16, 16] = k33 ++ k32)
--   (h_ktbl17 : s0[r (.GPR 3#5) s0 + 16*17, 16] = k35 ++ k34)
--   (h_ktbl18 : s0[r (.GPR 3#5) s0 + 16*18, 16] = k37 ++ k36)
--   (h_ktbl19 : s0[r (.GPR 3#5) s0 + 16*19, 16] = k39 ++ k38)
--
--   (h_ktbl20 : s0[r (.GPR 3#5) s0 + 16*20, 16] = k41 ++ k40)
--   (h_ktbl21 : s0[r (.GPR 3#5) s0 + 16*21, 16] = k43 ++ k42)
--   (h_ktbl22 : s0[r (.GPR 3#5) s0 + 16*22, 16] = k45 ++ k44)
--   (h_ktbl23 : s0[r (.GPR 3#5) s0 + 16*23, 16] = k47 ++ k46)
--
--   (h_ktbl24 : s0[r (.GPR 3#5) s0 + 16*24, 16] = k49 ++ k48)
--   (h_ktbl25 : s0[r (.GPR 3#5) s0 + 16*25, 16] = k51 ++ k50)
--   (h_ktbl26 : s0[r (.GPR 3#5) s0 + 16*26, 16] = k53 ++ k52)
--   (h_ktbl27 : s0[r (.GPR 3#5) s0 + 16*27, 16] = k55 ++ k54)
--
--   (h_ktbl28 : s0[r (.GPR 3#5) s0 + 16*28, 16] = k57 ++ k56)
--   (h_ktbl29 : s0[r (.GPR 3#5) s0 + 16*29, 16] = k59 ++ k58)
--   (h_ktbl30 : s0[r (.GPR 3#5) s0 + 16*30, 16] = k61 ++ k60)
--   (h_ktbl31 : s0[r (.GPR 3#5) s0 + 16*31, 16] = k63 ++ k62)
--
--   (h_ktbl32 : s0[r (.GPR 3#5) s0 + 16*32, 16] = k65 ++ k64)
--   (h_ktbl33 : s0[r (.GPR 3#5) s0 + 16*33, 16] = k67 ++ k66)
--   (h_ktbl34 : s0[r (.GPR 3#5) s0 + 16*34, 16] = k69 ++ k68)
--   (h_ktbl35 : s0[r (.GPR 3#5) s0 + 16*35, 16] = k71 ++ k70)
--
--   (h_ktbl36 : s0[r (.GPR 3#5) s0 + 16*36, 16] = k73 ++ k72)
--   (h_ktbl37 : s0[r (.GPR 3#5) s0 + 16*37, 16] = k75 ++ k74)
--   (h_ktbl38 : s0[r (.GPR 3#5) s0 + 16*38, 16] = k77 ++ k76)
--   (h_ktbl39 : s0[r (.GPR 3#5) s0 + 16*39, 16] = k79 ++ k78)

  (h_run : sf = run 485 s0) :
  r .ERR sf = .None
  /-
  More generally:
  r .PC sf = (if ¬r (StateField.GPR 0x2#5) s0 - 0x1#64 = 0x0#64
              then 0x126500#64
              else 0x126c94#64)
  -/
  -- ∧ r .PC sf = 0x126c94#64
--   ∧ r (.SFP 1) sf = q1
  -- ∧ (r (.SFP 3) sf ++ r (.SFP 2) sf ++ r (.SFP 1) sf ++ r (.SFP 0) sf) = final_hash
  := by
  -- Symbolic Simulation
  sym_block 485 (block_size := 20) -- ceiling|485/20| blocks
  -- clear_named [h_s, blocki_]
  -- Reasoning
  -- subst h_N
  -- obtain ⟨_h_si_program, _h_si_pc, _h_si_err, _h_si_sp_aligned,
  --         _h_si_sp, h_si_num_blocks, _h_si_ctx_base,
  --         _h_si_input_base, _h_si_ktbl_base,
  --         _h_si_ctx, _h_si_ktbl, _h_si_separate,
  --         _h_si_q0, _h_si_q1, _h_si_q2, _h_si_q3,
  --         _h_si_16, _h_si_17, _h_si_18, _h_si_19,
  --         _h_si_20, _h_si_21, _h_si_22, _h_si_23⟩ := h_precondition
  -- simp only [num_blocks] at h_si_num_blocks
  -- simp [h_s485_err]
  -- -- simp (config := { ground := true }) only [h_si_num_blocks, minimal_theory]
  -- -- done
  -- done
