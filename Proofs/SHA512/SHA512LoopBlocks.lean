/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import Proofs.SHA512.SHA512Prelude
import Proofs.SHA512.SHA512_block_armv8_rules
import Arm.Cfg.Cfg
import Tactics.PruneUpdates
open BitVec

namespace SHA512

theorem extractLsb'_append_swap (x y : BitVec 128) :
    (x ++ y).extractLsb' 64 128 =
    BitVec.extractLsb' 0 64 x ++ BitVec.extractLsb' 64 64 y := by
  bv_decide

theorem extractLsb'_append_left_64 (x y : BitVec 64) :
    (x ++ y).extractLsb' 64 64 = x := by
  rw [extractLsb'_append_left]

theorem extractLsb'_append_right_64 (x y : BitVec 64) :
    (x ++ y).extractLsb' 0 64 = y := by
  rw [extractLsb'_append_right]

theorem extractLsb'_add_64 (x y : BitVec 128) :
  (x + y).extractLsb' 0 64 =
  (BitVec.extractLsb' 0 64 x) + (BitVec.extractLsb' 0 64 y) := by
  bv_decide

/-
Loop Body:

1. Prelude: 8 instructions (0x126500#64)
   ld1
   subs
   sub
   mov
   mov
   mov
   mov
   csel

2. The following sequence of 12 instructions are repeated 32 times:
   (Starting 0x126520#64)
   add
   ld1
   ext
   ext
   ext
   add
   sha512su0
   ext
   sha512h
   sha512su1
   add
   sha512h2

3. The following sequence of 11 instructions are repeated 7 times:
   (Starting 0x126b20#64)
   ld1
   add
   ld1
   ext
   ext
   ext
   add
   sha512h
   rev64
   add
   sha512h2

4. The following sequence of 11 instructions appears once:
   (Starting 0x126c54#64)
   sub
   add
   ld1
   ext
   ext
   ext
   add
   sha512h
   rev64
   add
   sha512h2


5. Epilogue:
   (Starting 0x126c80#64)
   add
   add
   add
   add
   cbnz
-/

-- Prelude
set_option trace.Tactic.prune_updates true in
-- set_option trace.Tactic.prune_updates.answer true in
-- set_option trace.Meta.isDefEq true in
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126500 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126500#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 8 s =
  w (StateField.GPR 0x1#5)
    (if ¬(AddWithCarry (r (StateField.GPR 0x2#5) s) 0xfffffffffffffffe#64 0x1#1).snd.z = 0x1#1 then
      r (StateField.GPR 0x1#5) s
    else r (StateField.GPR 0x1#5) s - 0x80#64)
    (w StateField.PC 0x126520#64
      (w (StateField.SFP 0x1d#5) (r (StateField.SFP 0x3#5) s)
        (w StateField.PC 0x126518#64
          (w (StateField.SFP 0x1c#5) (r (StateField.SFP 0x2#5) s)
            (w StateField.PC 0x126514#64
              (w (StateField.SFP 0x1b#5) (r (StateField.SFP 0x1#5) s)
                (w StateField.PC 0x126510#64
                  (w (StateField.SFP 0x1a#5) (r (StateField.SFP 0x0#5) s)
                    (w (StateField.GPR 0x4#5) (r (StateField.GPR 0x1#5) s - 0x80#64)
                      (w StateField.PC 0x12650c#64
                        (w (StateField.GPR 0x2#5) (r (StateField.GPR 0x2#5) s - 0x1#64)
                          (w (StateField.FLAG PFlag.V)
                            (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xfffffffffffffffe#64 0x1#1).snd.v
                            (w (StateField.FLAG PFlag.C)
                              (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xfffffffffffffffe#64 0x1#1).snd.c
                              (w (StateField.FLAG PFlag.Z)
                                (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xfffffffffffffffe#64 0x1#1).snd.z
                                (w (StateField.FLAG PFlag.N)
                                  (AddWithCarry (r (StateField.GPR 0x2#5) s) 0xfffffffffffffffe#64 0x1#1).snd.n
                                  (w StateField.PC 0x126508#64
                                    (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                      (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                        s))))))))))))))))))
  := by
  generalize h_run : run 8 s = sf
  replace h_run := h_run.symm
  sym_n 8
  simp (config := {decide := true}) only
    [h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     -- w_of_w_commute, w_of_w_shadow,
     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_8
  -- prune_updates h_step_8
  exact h_step_8
  done

-- #1/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126520 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126520#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126550#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
        (w (StateField.SFP 0x10#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (w StateField.PC 0x126548#64
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
              (w StateField.PC 0x126544#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
                  (w (StateField.SFP 0x10#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x11#5) s) (r (StateField.SFP 0x10#5) s))
                    (w StateField.PC 0x12653c#64
                      (w (StateField.SFP 0x3#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
                        (w StateField.PC 0x126534#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                            (w StateField.PC 0x126530#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                                (w StateField.PC 0x12652c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
                                    (w StateField.PC 0x126528#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126524#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x10#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp,
     state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,
     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule
     ]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #2/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126550 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126550#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126580#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
        (w (StateField.SFP 0x11#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (w StateField.PC 0x126578#64
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
              (w StateField.PC 0x126574#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
                  (w (StateField.SFP 0x11#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x12#5) s) (r (StateField.SFP 0x11#5) s))
                    (w StateField.PC 0x12656c#64
                      (w (StateField.SFP 0x2#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
                        (w StateField.PC 0x126564#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                            (w StateField.PC 0x126560#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                                (w StateField.PC 0x12655c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
                                    (w StateField.PC 0x126558#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126554#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x11#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #3/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126580 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126580#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x1265b0#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
        (w (StateField.SFP 0x12#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (w StateField.PC 0x1265a8#64
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
              (w StateField.PC 0x1265a4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
                  (w (StateField.SFP 0x12#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x13#5) s) (r (StateField.SFP 0x12#5) s))
                    (w StateField.PC 0x12659c#64
                      (w (StateField.SFP 0x4#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
                        (w StateField.PC 0x126594#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                            (w StateField.PC 0x126590#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                                (w StateField.PC 0x12658c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
                                    (w StateField.PC 0x126588#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126584#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x12#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #4/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1265b0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1265b0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x1265e0#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
        (w (StateField.SFP 0x13#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (w StateField.PC 0x1265d8#64
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
              (w StateField.PC 0x1265d4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
                  (w (StateField.SFP 0x13#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x14#5) s) (r (StateField.SFP 0x13#5) s))
                    (w StateField.PC 0x1265cc#64
                      (w (StateField.SFP 0x1#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
                        (w StateField.PC 0x1265c4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                            (w StateField.PC 0x1265c0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                                (w StateField.PC 0x1265bc#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
                                    (w StateField.PC 0x1265b8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1265b4#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x13#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #5/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1265e0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1265e0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x126610#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
        (w (StateField.SFP 0x14#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (w StateField.PC 0x126608#64
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
              (w StateField.PC 0x126604#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
                  (w (StateField.SFP 0x14#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x15#5) s) (r (StateField.SFP 0x14#5) s))
                    (w StateField.PC 0x1265fc#64
                      (w (StateField.SFP 0x0#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
                        (w StateField.PC 0x1265f4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                            (w StateField.PC 0x1265f0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                                (w StateField.PC 0x1265ec#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
                                    (w StateField.PC 0x1265e8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1265e4#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x14#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #6/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126610 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126610#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126640#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
        (w (StateField.SFP 0x15#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (w StateField.PC 0x126638#64
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
              (w StateField.PC 0x126634#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
                  (w (StateField.SFP 0x15#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x16#5) s) (r (StateField.SFP 0x15#5) s))
                    (w StateField.PC 0x12662c#64
                      (w (StateField.SFP 0x3#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
                        (w StateField.PC 0x126624#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                            (w StateField.PC 0x126620#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                                (w StateField.PC 0x12661c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
                                    (w StateField.PC 0x126618#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126614#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x15#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #7/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126640 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126640#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126670#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
        (w (StateField.SFP 0x16#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (w StateField.PC 0x126668#64
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
              (w StateField.PC 0x126664#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
                  (w (StateField.SFP 0x16#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x17#5) s) (r (StateField.SFP 0x16#5) s))
                    (w StateField.PC 0x12665c#64
                      (w (StateField.SFP 0x2#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
                        (w StateField.PC 0x126654#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                            (w StateField.PC 0x126650#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                                (w StateField.PC 0x12664c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
                                    (w StateField.PC 0x126648#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126644#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x16#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #8/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126670 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126670#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x1266a0#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
        (w (StateField.SFP 0x17#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (w StateField.PC 0x126698#64
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
              (w StateField.PC 0x126694#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
                  (w (StateField.SFP 0x17#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x10#5) s) (r (StateField.SFP 0x17#5) s))
                    (w StateField.PC 0x12668c#64
                      (w (StateField.SFP 0x4#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
                        (w StateField.PC 0x126684#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                            (w StateField.PC 0x126680#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                                (w StateField.PC 0x12667c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
                                    (w StateField.PC 0x126678#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126674#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x17#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #9/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1266a0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1266a0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x1266d0#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
        (w (StateField.SFP 0x10#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (w StateField.PC 0x1266c8#64
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
              (w StateField.PC 0x1266c4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
                  (w (StateField.SFP 0x10#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x11#5) s) (r (StateField.SFP 0x10#5) s))
                    (w StateField.PC 0x1266bc#64
                      (w (StateField.SFP 0x1#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
                        (w StateField.PC 0x1266b4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                            (w StateField.PC 0x1266b0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                                (w StateField.PC 0x1266ac#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
                                    (w StateField.PC 0x1266a8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1266a4#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x10#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #10/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1266d0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1266d0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x126700#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
        (w (StateField.SFP 0x11#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (w StateField.PC 0x1266f8#64
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
              (w StateField.PC 0x1266f4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
                  (w (StateField.SFP 0x11#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x12#5) s) (r (StateField.SFP 0x11#5) s))
                    (w StateField.PC 0x1266ec#64
                      (w (StateField.SFP 0x0#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
                        (w StateField.PC 0x1266e4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                            (w StateField.PC 0x1266e0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                                (w StateField.PC 0x1266dc#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
                                    (w StateField.PC 0x1266d8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1266d4#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x11#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #11/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126700 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126700#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126730#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
        (w (StateField.SFP 0x12#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (w StateField.PC 0x126728#64
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
              (w StateField.PC 0x126724#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
                  (w (StateField.SFP 0x12#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x13#5) s) (r (StateField.SFP 0x12#5) s))
                    (w StateField.PC 0x12671c#64
                      (w (StateField.SFP 0x3#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
                        (w StateField.PC 0x126714#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                            (w StateField.PC 0x126710#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                                (w StateField.PC 0x12670c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
                                    (w StateField.PC 0x126708#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126704#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x12#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #12/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126730 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126730#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126760#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
        (w (StateField.SFP 0x13#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (w StateField.PC 0x126758#64
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
              (w StateField.PC 0x126754#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
                  (w (StateField.SFP 0x13#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x14#5) s) (r (StateField.SFP 0x13#5) s))
                    (w StateField.PC 0x12674c#64
                      (w (StateField.SFP 0x2#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
                        (w StateField.PC 0x126744#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                            (w StateField.PC 0x126740#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                                (w StateField.PC 0x12673c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
                                    (w StateField.PC 0x126738#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126734#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x13#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #13/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126760 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126760#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x126790#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
        (w (StateField.SFP 0x14#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (w StateField.PC 0x126788#64
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
              (w StateField.PC 0x126784#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
                  (w (StateField.SFP 0x14#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x15#5) s) (r (StateField.SFP 0x14#5) s))
                    (w StateField.PC 0x12677c#64
                      (w (StateField.SFP 0x4#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
                        (w StateField.PC 0x126774#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                            (w StateField.PC 0x126770#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                                (w StateField.PC 0x12676c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
                                    (w StateField.PC 0x126768#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126764#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x14#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #14/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126790 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126790#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x1267c0#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
        (w (StateField.SFP 0x15#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (w StateField.PC 0x1267b8#64
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
              (w StateField.PC 0x1267b4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
                  (w (StateField.SFP 0x15#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x16#5) s) (r (StateField.SFP 0x15#5) s))
                    (w StateField.PC 0x1267ac#64
                      (w (StateField.SFP 0x1#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
                        (w StateField.PC 0x1267a4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                            (w StateField.PC 0x1267a0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                                (w StateField.PC 0x12679c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
                                    (w StateField.PC 0x126798#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126794#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x15#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #15/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1267c0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1267c0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x1267f0#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
        (w (StateField.SFP 0x16#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (w StateField.PC 0x1267e8#64
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
              (w StateField.PC 0x1267e4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
                  (w (StateField.SFP 0x16#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x17#5) s) (r (StateField.SFP 0x16#5) s))
                    (w StateField.PC 0x1267dc#64
                      (w (StateField.SFP 0x0#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
                        (w StateField.PC 0x1267d4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                            (w StateField.PC 0x1267d0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                                (w StateField.PC 0x1267cc#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
                                    (w StateField.PC 0x1267c8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1267c4#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x16#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #16/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1267f0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1267f0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126820#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
        (w (StateField.SFP 0x17#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (w StateField.PC 0x126818#64
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
              (w StateField.PC 0x126814#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
                  (w (StateField.SFP 0x17#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x10#5) s) (r (StateField.SFP 0x17#5) s))
                    (w StateField.PC 0x12680c#64
                      (w (StateField.SFP 0x3#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
                        (w StateField.PC 0x126804#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                            (w StateField.PC 0x126800#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                                (w StateField.PC 0x1267fc#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
                                    (w StateField.PC 0x1267f8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1267f4#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x17#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #17/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126820 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126820#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126850#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
        (w (StateField.SFP 0x10#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (w StateField.PC 0x126848#64
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
              (w StateField.PC 0x126844#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
                  (w (StateField.SFP 0x10#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x11#5) s) (r (StateField.SFP 0x10#5) s))
                    (w StateField.PC 0x12683c#64
                      (w (StateField.SFP 0x2#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
                        (w StateField.PC 0x126834#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                            (w StateField.PC 0x126830#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                                (w StateField.PC 0x12682c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
                                    (w StateField.PC 0x126828#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126824#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x10#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #18/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126850 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126850#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x126880#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
        (w (StateField.SFP 0x11#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (w StateField.PC 0x126878#64
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
              (w StateField.PC 0x126874#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
                  (w (StateField.SFP 0x11#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x12#5) s) (r (StateField.SFP 0x11#5) s))
                    (w StateField.PC 0x12686c#64
                      (w (StateField.SFP 0x4#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
                        (w StateField.PC 0x126864#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                            (w StateField.PC 0x126860#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                                (w StateField.PC 0x12685c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
                                    (w StateField.PC 0x126858#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126854#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x11#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #19/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126880 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s =  0x126880#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x1268b0#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
        (w (StateField.SFP 0x12#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (w StateField.PC 0x1268a8#64
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
              (w StateField.PC 0x1268a4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
                  (w (StateField.SFP 0x12#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x13#5) s) (r (StateField.SFP 0x12#5) s))
                    (w StateField.PC 0x12689c#64
                      (w (StateField.SFP 0x1#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
                        (w StateField.PC 0x126894#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                            (w StateField.PC 0x126890#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                                (w StateField.PC 0x12688c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
                                    (w StateField.PC 0x126888#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126884#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x12#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #20/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1268b0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1268b0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x1268e0#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
        (w (StateField.SFP 0x13#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (w StateField.PC 0x1268d8#64
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
              (w StateField.PC 0x1268d4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
                  (w (StateField.SFP 0x13#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x14#5) s) (r (StateField.SFP 0x13#5) s))
                    (w StateField.PC 0x1268cc#64
                      (w (StateField.SFP 0x0#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
                        (w StateField.PC 0x1268c4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                            (w StateField.PC 0x1268c0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                                (w StateField.PC 0x1268bc#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
                                    (w StateField.PC 0x1268b8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1268b4#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x13#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #21/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1268e0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1268e0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126910#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
        (w (StateField.SFP 0x14#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (w StateField.PC 0x126908#64
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
              (w StateField.PC 0x126904#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
                  (w (StateField.SFP 0x14#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x15#5) s) (r (StateField.SFP 0x14#5) s))
                    (w StateField.PC 0x1268fc#64
                      (w (StateField.SFP 0x3#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
                        (w StateField.PC 0x1268f4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                            (w StateField.PC 0x1268f0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                                (w StateField.PC 0x1268ec#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
                                    (w StateField.PC 0x1268e8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1268e4#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x14#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #22/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126910 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126910#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126940#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
        (w (StateField.SFP 0x15#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (w StateField.PC 0x126938#64
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
              (w StateField.PC 0x126934#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
                  (w (StateField.SFP 0x15#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x16#5) s) (r (StateField.SFP 0x15#5) s))
                    (w StateField.PC 0x12692c#64
                      (w (StateField.SFP 0x2#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
                        (w StateField.PC 0x126924#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                            (w StateField.PC 0x126920#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                                (w StateField.PC 0x12691c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
                                    (w StateField.PC 0x126918#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126914#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x15#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #23/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126940 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126940#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x126970#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
        (w (StateField.SFP 0x16#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (w StateField.PC 0x126968#64
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
              (w StateField.PC 0x126964#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
                  (w (StateField.SFP 0x16#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x17#5) s) (r (StateField.SFP 0x16#5) s))
                    (w StateField.PC 0x12695c#64
                      (w (StateField.SFP 0x4#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
                        (w StateField.PC 0x126954#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                            (w StateField.PC 0x126950#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                                (w StateField.PC 0x12694c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
                                    (w StateField.PC 0x126948#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126944#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x16#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #24/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126970 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126970#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x1269a0#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
        (w (StateField.SFP 0x17#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (w StateField.PC 0x126998#64
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
              (w StateField.PC 0x126994#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
                  (w (StateField.SFP 0x17#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x10#5) s) (r (StateField.SFP 0x17#5) s))
                    (w StateField.PC 0x12698c#64
                      (w (StateField.SFP 0x1#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
                        (w StateField.PC 0x126984#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                            (w StateField.PC 0x126980#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                                (w StateField.PC 0x12697c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
                                    (w StateField.PC 0x126978#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126974#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x17#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #25/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1269a0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1269a0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x1269d0#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
        (w (StateField.SFP 0x10#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (w StateField.PC 0x1269c8#64
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
              (w StateField.PC 0x1269c4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
                  (w (StateField.SFP 0x10#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x11#5) s) (r (StateField.SFP 0x10#5) s))
                    (w StateField.PC 0x1269bc#64
                      (w (StateField.SFP 0x0#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
                        (w StateField.PC 0x1269b4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                            (w StateField.PC 0x1269b0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                                (w StateField.PC 0x1269ac#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
                                    (w StateField.PC 0x1269a8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1269a4#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x10#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #26/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x1269d0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x1269d0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126a00#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
        (w (StateField.SFP 0x11#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (w StateField.PC 0x1269f8#64
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
              (w StateField.PC 0x1269f4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
                  (w (StateField.SFP 0x11#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x12#5) s) (r (StateField.SFP 0x11#5) s))
                    (w StateField.PC 0x1269ec#64
                      (w (StateField.SFP 0x3#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
                        (w StateField.PC 0x1269e4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                            (w StateField.PC 0x1269e0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                                (w StateField.PC 0x1269dc#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
                                    (w StateField.PC 0x1269d8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x1269d4#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x11#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #27/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126a00 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126a00#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126a30#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
        (w (StateField.SFP 0x12#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (w StateField.PC 0x126a28#64
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
              (w StateField.PC 0x126a24#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
                  (w (StateField.SFP 0x12#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x13#5) s) (r (StateField.SFP 0x12#5) s))
                    (w StateField.PC 0x126a1c#64
                      (w (StateField.SFP 0x2#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
                        (w StateField.PC 0x126a14#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                            (w StateField.PC 0x126a10#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                                (w StateField.PC 0x126a0c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
                                    (w StateField.PC 0x126a08#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126a04#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x12#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #28/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126a30 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126a30#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x126a60#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
        (w (StateField.SFP 0x13#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (w StateField.PC 0x126a58#64
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
              (w StateField.PC 0x126a54#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
                  (w (StateField.SFP 0x13#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x14#5) s) (r (StateField.SFP 0x13#5) s))
                    (w StateField.PC 0x126a4c#64
                      (w (StateField.SFP 0x4#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
                        (w StateField.PC 0x126a44#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                            (w StateField.PC 0x126a40#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                                (w StateField.PC 0x126a3c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
                                    (w StateField.PC 0x126a38#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126a34#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x13#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done

-- #29/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126a60 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126a60#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x126a90#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
        (w (StateField.SFP 0x14#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (w StateField.PC 0x126a88#64
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
              (w StateField.PC 0x126a84#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))
                  (w (StateField.SFP 0x14#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x15#5) s) (r (StateField.SFP 0x14#5) s))
                    (w StateField.PC 0x126a7c#64
                      (w (StateField.SFP 0x1#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
                        (w StateField.PC 0x126a74#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                            (w StateField.PC 0x126a70#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                                (w StateField.PC 0x126a6c#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
                                    (w StateField.PC 0x126a68#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126a64#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x14#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #30/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126a90 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126a90#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x126ac0#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
        (w (StateField.SFP 0x15#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (w StateField.PC 0x126ab8#64
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
              (w StateField.PC 0x126ab4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))
                  (w (StateField.SFP 0x15#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x16#5) s) (r (StateField.SFP 0x15#5) s))
                    (w StateField.PC 0x126aac#64
                      (w (StateField.SFP 0x0#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
                        (w StateField.PC 0x126aa4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                            (w StateField.PC 0x126aa0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                                (w StateField.PC 0x126a9c#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
                                    (w StateField.PC 0x126a98#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126a94#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x15#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #31/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126ac0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126ac0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126af0#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
        (w (StateField.SFP 0x16#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (w StateField.PC 0x126ae8#64
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
              (w StateField.PC 0x126ae4#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))
                  (w (StateField.SFP 0x16#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x17#5) s) (r (StateField.SFP 0x16#5) s))
                    (w StateField.PC 0x126adc#64
                      (w (StateField.SFP 0x3#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
                        (w StateField.PC 0x126ad4#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                            (w StateField.PC 0x126ad0#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                                (w StateField.PC 0x126acc#64
                                  (w (StateField.SFP 0x18#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
                                    (w StateField.PC 0x126ac8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x19#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126ac4#64
                                            (w (StateField.SFP 0x18#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x16#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #32/32
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126af0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126af0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 12 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126b20#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
        (w (StateField.SFP 0x17#5)
          (SHA2.message_schedule_word_aux (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) ++
            SHA2.message_schedule_word_aux (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (w StateField.PC 0x126b18#64
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
              (w StateField.PC 0x126b14#64
                (w (StateField.SFP 0x7#5)
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))
                  (w (StateField.SFP 0x17#5)
                    (DPSFP.sha512su0 (r (StateField.SFP 0x10#5) s) (r (StateField.SFP 0x17#5) s))
                    (w StateField.PC 0x126b0c#64
                      (w (StateField.SFP 0x2#5)
                        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                            (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                              extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
                        (w StateField.PC 0x126b04#64
                          (w (StateField.SFP 0x6#5)
                            (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                              extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                            (w StateField.PC 0x126b00#64
                              (w (StateField.SFP 0x5#5)
                                (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                                  extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                                (w StateField.PC 0x126afc#64
                                  (w (StateField.SFP 0x19#5)
                                    (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++
                                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                        extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
                                    (w StateField.PC 0x126af8#64
                                      (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                        (w (StateField.SFP 0x18#5) (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s)
                                          (w StateField.PC 0x126af4#64
                                            (w (StateField.SFP 0x19#5)
                                              (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 64 64 (r (StateField.SFP 0x17#5) s) ++
                                                (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                                  extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                                              s)))))))))))))))))))))
  := by
  generalize h_run : run 12 s = sf
  replace h_run := h_run.symm
  sym_n 12
  simp (config := {decide := true}) only
    [h_step_11, h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_12
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_12
  exact h_step_12
  done


-- #1/7
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126b20 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126b20#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x126b4c#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
        (w StateField.PC 0x126b44#64
          (w (StateField.SFP 0x10#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
              (w StateField.PC 0x126b40#64
                (w (StateField.SFP 0x4#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x10#5) s))))
                  (w StateField.PC 0x126b38#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                      (w StateField.PC 0x126b34#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                          (w StateField.PC 0x126b30#64
                            (w (StateField.SFP 0x18#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x10#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x10#5) s)))
                              (w StateField.PC 0x126b2c#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x10#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126b28#64
                                      (w (StateField.SFP 0x18#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x10#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x10#5) s)))
                                        (w StateField.PC 0x126b24#64
                                          (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                            (w (StateField.SFP 0x19#5)
                                              (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s) s)))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done

-- #2/7
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126b4c {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126b4c#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x126b78#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
        (w StateField.PC 0x126b70#64
          (w (StateField.SFP 0x11#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
              (w StateField.PC 0x126b6c#64
                (w (StateField.SFP 0x1#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x11#5) s))))
                  (w StateField.PC 0x126b64#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                      (w StateField.PC 0x126b60#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                          (w StateField.PC 0x126b5c#64
                            (w (StateField.SFP 0x19#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x11#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x11#5) s)))
                              (w StateField.PC 0x126b58#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x11#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126b54#64
                                      (w (StateField.SFP 0x19#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x11#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x11#5) s)))
                                        (w StateField.PC 0x126b50#64
                                          (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                            (w (StateField.SFP 0x18#5)
                                              (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s) s)))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done

-- #3/7
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126b78 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126b78#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x126ba4#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
        (w StateField.PC 0x126b9c#64
          (w (StateField.SFP 0x12#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
              (w StateField.PC 0x126b98#64
                (w (StateField.SFP 0x0#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x12#5) s))))
                  (w StateField.PC 0x126b90#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                      (w StateField.PC 0x126b8c#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                          (w StateField.PC 0x126b88#64
                            (w (StateField.SFP 0x18#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x12#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x12#5) s)))
                              (w StateField.PC 0x126b84#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x12#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126b80#64
                                      (w (StateField.SFP 0x18#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x12#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x12#5) s)))
                                        (w StateField.PC 0x126b7c#64
                                          (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                            (w (StateField.SFP 0x19#5)
                                              (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s) s)))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done

-- #4/7
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126ba4 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126ba4#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x3#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))))
    (w StateField.PC 0x126bd0#64
      (w (StateField.SFP 0x4#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
        (w StateField.PC 0x126bc8#64
          (w (StateField.SFP 0x13#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x3#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
              (w StateField.PC 0x126bc4#64
                (w (StateField.SFP 0x3#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x13#5) s))))
                  (w StateField.PC 0x126bbc#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                      (w StateField.PC 0x126bb8#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                          (w StateField.PC 0x126bb4#64
                            (w (StateField.SFP 0x19#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x13#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x13#5) s)))
                              (w StateField.PC 0x126bb0#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x13#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126bac#64
                                      (w (StateField.SFP 0x19#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x13#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x13#5) s)))
                                        (w StateField.PC 0x126ba8#64
                                          (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                            (w (StateField.SFP 0x18#5)
                                              (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s) s)))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done

-- #5/7
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126bd0 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126bd0#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x2#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))))
    (w StateField.PC 0x126bfc#64
      (w (StateField.SFP 0x1#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
        (w StateField.PC 0x126bf4#64
          (w (StateField.SFP 0x14#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x2#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
              (w StateField.PC 0x126bf0#64
                (w (StateField.SFP 0x2#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x14#5) s))))
                  (w StateField.PC 0x126be8#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                      (w StateField.PC 0x126be4#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                          (w StateField.PC 0x126be0#64
                            (w (StateField.SFP 0x18#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x14#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x14#5) s)))
                              (w StateField.PC 0x126bdc#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x14#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126bd8#64
                                      (w (StateField.SFP 0x18#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x14#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x14#5) s)))
                                        (w StateField.PC 0x126bd4#64
                                          (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                            (w (StateField.SFP 0x19#5)
                                              (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s) s)))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done

-- #6/7
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126bfc {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126bfc#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x4#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))))
    (w StateField.PC 0x126c28#64
      (w (StateField.SFP 0x0#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
        (w StateField.PC 0x126c20#64
          (w (StateField.SFP 0x15#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x4#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
              (w StateField.PC 0x126c1c#64
                (w (StateField.SFP 0x4#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x15#5) s))))
                  (w StateField.PC 0x126c14#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                      (w StateField.PC 0x126c10#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))
                          (w StateField.PC 0x126c0c#64
                            (w (StateField.SFP 0x19#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x15#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x15#5) s)))
                              (w StateField.PC 0x126c08#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x15#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126c04#64
                                      (w (StateField.SFP 0x19#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x15#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x15#5) s)))
                                        (w StateField.PC 0x126c00#64
                                          (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                            (w (StateField.SFP 0x18#5)
                                              (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s) s)))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done

-- #7/7
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126c28 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126c28#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x1#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))))
    (w StateField.PC 0x126c54#64
      (w (StateField.SFP 0x3#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
        (w StateField.PC 0x126c4c#64
          (w (StateField.SFP 0x16#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x1#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
              (w StateField.PC 0x126c48#64
                (w (StateField.SFP 0x1#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x16#5) s))))
                  (w StateField.PC 0x126c40#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x2#5) s))
                      (w StateField.PC 0x126c3c#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x0#5) s))
                          (w StateField.PC 0x126c38#64
                            (w (StateField.SFP 0x18#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x16#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x16#5) s)))
                              (w StateField.PC 0x126c34#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x16#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126c30#64
                                      (w (StateField.SFP 0x18#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x16#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x18#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x16#5) s)))
                                        (w StateField.PC 0x126c2c#64
                                          (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s + 0x10#64)
                                            (w (StateField.SFP 0x19#5)
                                              (read_mem_bytes 16 (r (StateField.GPR 0x3#5) s) s) s)))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done

-- #1/1
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126c54 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126c54#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 11 s =
  w (StateField.SFP 0x0#5)
    (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) ++
      (SHA2.compression_update_t1
          (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
          (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)) +
        SHA2.compression_update_t2
          (SHA2.compression_update_t2 (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s)) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
          (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s))))
    (w StateField.PC 0x126c80#64
      (w (StateField.SFP 0x2#5)
        (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
          (extractLsb' 0 64 (r (StateField.SFP 0x4#5) s) +
            SHA2.compression_update_t1
              (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
              (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
              (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
              (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
        (w StateField.PC 0x126c78#64
          (w (StateField.SFP 0x17#5) (DPSFP.vrev128_64_8 (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s))
            (w (StateField.SFP 0x0#5)
              (SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                SHA2.compression_update_t1
                  (extractLsb' 64 64 (r (StateField.SFP 0x4#5) s) +
                    SHA2.compression_update_t1 (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s))
                      (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s))
                      (extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                  (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                  (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s)) (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s))
                  (extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
              (w StateField.PC 0x126c74#64
                (w (StateField.SFP 0x0#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) +
                      (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) +
                      (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                        extractLsb' 64 64 (r (StateField.SFP 0x17#5) s))))
                  (w StateField.PC 0x126c6c#64
                    (w (StateField.SFP 0x6#5)
                      (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) ++ extractLsb' 64 64 (r (StateField.SFP 0x4#5) s))
                      (w StateField.PC 0x126c68#64
                        (w (StateField.SFP 0x5#5)
                          (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) ++
                            extractLsb' 64 64 (r (StateField.SFP 0x3#5) s))
                          (w StateField.PC 0x126c64#64
                            (w (StateField.SFP 0x19#5)
                              (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 0 64 (r (StateField.SFP 0x17#5) s) ++
                                (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                  extractLsb' 64 64 (r (StateField.SFP 0x17#5) s)))
                              (w StateField.PC 0x126c60#64
                                (w (StateField.GPR 0x1#5) (r (StateField.GPR 0x1#5) s + 0x10#64)
                                  (w (StateField.SFP 0x17#5) (read_mem_bytes 16 (r (StateField.GPR 0x1#5) s) s)
                                    (w StateField.PC 0x126c5c#64
                                      (w (StateField.SFP 0x19#5)
                                        (extractLsb' 64 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 64 64 (r (StateField.SFP 0x17#5) s) ++
                                          (extractLsb' 0 64 (r (StateField.SFP 0x19#5) s) +
                                            extractLsb' 0 64 (r (StateField.SFP 0x17#5) s)))
                                        (w (StateField.GPR 0x3#5) (r (StateField.GPR 0x3#5) s - 0x280#64)
                                          (w StateField.PC 0x126c58#64 s))))))))))))))))))))
  := by
  generalize h_run : run 11 s = sf
  replace h_run := h_run.symm
  sym_n 11
  simp (config := {decide := true}) only
    [h_step_10, h_step_9,
     h_step_8, h_step_7,  h_step_6,  h_step_5,
     h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,

     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_11
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_11
  exact h_step_11
  done


-- #1/1
set_option pp.maxSteps 50000 in
theorem program.blocki_eq_0x126c80 {s : ArmState}
  (h_program : s.program = program)
  (h_pc : r StateField.PC s = 0x126c80#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 5 s =
  w StateField.PC (if r (StateField.GPR 0x2#5) s = 0x0#64 then 0x126c94#64 else 0x126500#64)
    (w (StateField.SFP 0x3#5)
      (extractLsb' 64 64 (r (StateField.SFP 0x3#5) s) + extractLsb' 64 64 (r (StateField.SFP 0x1d#5) s) ++
        (extractLsb' 0 64 (r (StateField.SFP 0x3#5) s) + extractLsb' 0 64 (r (StateField.SFP 0x1d#5) s)))
      (w StateField.PC 0x126c8c#64
        (w (StateField.SFP 0x2#5)
          (extractLsb' 64 64 (r (StateField.SFP 0x2#5) s) + extractLsb' 64 64 (r (StateField.SFP 0x1c#5) s) ++
            (extractLsb' 0 64 (r (StateField.SFP 0x2#5) s) + extractLsb' 0 64 (r (StateField.SFP 0x1c#5) s)))
          (w StateField.PC 0x126c88#64
            (w (StateField.SFP 0x1#5)
              (extractLsb' 64 64 (r (StateField.SFP 0x1#5) s) + extractLsb' 64 64 (r (StateField.SFP 0x1b#5) s) ++
                (extractLsb' 0 64 (r (StateField.SFP 0x1#5) s) + extractLsb' 0 64 (r (StateField.SFP 0x1b#5) s)))
              (w StateField.PC 0x126c84#64
                (w (StateField.SFP 0x0#5)
                  (extractLsb' 64 64 (r (StateField.SFP 0x0#5) s) + extractLsb' 64 64 (r (StateField.SFP 0x1a#5) s) ++
                    (extractLsb' 0 64 (r (StateField.SFP 0x0#5) s) + extractLsb' 0 64 (r (StateField.SFP 0x1a#5) s)))
                  s)))))))
  := by
  generalize h_run : run 5 s = sf
  replace h_run := h_run.symm
  sym_n 5
  simp (config := {decide := true}) only
    [h_step_4,  h_step_3,  h_step_2,  h_step_1,
     binary_vector_op_aux_add_128_simp, state_value,
     extractLsb'_append_swap,
     extractLsb'_append_left_64,
     extractLsb'_append_right_64,
     extractLsb'_add_64,
     state_simp_rules, bitvec_rules, minimal_theory,
     sha512_message_schedule_rule,
     sha512h_and_sha512h2_rule]
    at h_step_5
  simp [sha512h_rule,
        state_value,
        extractLsb'_append_swap,
        extractLsb'_append_left_64,
        extractLsb'_append_right_64,
        extractLsb'_add_64,
        state_simp_rules, bitvec_rules, minimal_theory] at h_step_5
  exact h_step_5
  done
