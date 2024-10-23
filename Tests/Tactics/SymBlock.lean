import Tactics.SymBlock
import Tactics.StepThms

section Foo

def ugh_program : Program :=
  def_program
  [(0x12650c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
   (0x126510#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
   (0x126514#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
   (0x126518#64 , 0x4ea31c7d#32),      --  mov     v29.16b, v3.16b
   (0x12651c#64 , 0x4ea01c1a#32),      --  mov     v26.16b, v0.16b
   (0x126520#64 , 0x4ea11c3b#32),      --  mov     v27.16b, v1.16b
   (0x126524#64 , 0x4ea21c5c#32),      --  mov     v28.16b, v2.16b
   (0x126528#64 , 0x4ea31c7d#32)]      --  mov     v29.16b, v3.16b

set_option trace.gen_step.print_names true in
#genStepEqTheorems ugh_program

#time
-- set_option trace.Tactic.sym.info true in
theorem ugh_program.blocki_eq_0x12650c {s : ArmState}
  (h_program : s.program = ugh_program)
  (h_pc : r StateField.PC s = 0x12650c#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 4 s =
    w StateField.PC (1205532#64)
    (w (StateField.SFP 29#5) (r (StateField.SFP 3#5) s)
      (w StateField.PC (1205528#64)
        (w (StateField.SFP 28#5) (r (StateField.SFP 2#5) s)
          (w StateField.PC (1205524#64)
            (w (StateField.SFP 27#5) (r (StateField.SFP 1#5) s)
              (w StateField.PC (1205520#64) (w (StateField.SFP 26#5) (r (StateField.SFP 0#5) s) s))))))) := by
  -- generalize h_run : run 4 s = sf
  -- replace h_run := h_run.symm
  -- sym_n 4
  -- simp (config := {decide := true}) only [h_step_3, h_step_2, h_step_1, bitvec_rules, minimal_theory, state_simp_rules] at h_step_4
  -- assumption
  -- done
  sorry

theorem ugh_program.blocki_eq_0x12650c_alt {s : ArmState}
  (h_program : s.program = ugh_program)
  (h_pc : r StateField.PC s = 0x12650c#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 4 s = w StateField.PC (1205532#64)
    (w (StateField.SFP 29#5) (r (StateField.SFP 3#5) s)
        (w (StateField.SFP 28#5) (r (StateField.SFP 2#5) s)
            (w (StateField.SFP 27#5) (r (StateField.SFP 1#5) s)
              (w (StateField.SFP 26#5) (r (StateField.SFP 0#5) s) s)))) := by
  -- sym_n 4
  -- simp (config := {decide := true})
  -- [h_step_3, h_step_2, h_step_1, state_simp_rules] at h_step_4
  sorry
theorem ugh_program.blocki_eq_0x12651c {s : ArmState}
  (h_program : s.program = ugh_program)
  (h_pc : r StateField.PC s = 0x12651c#64)
  (h_err : r StateField.ERR s = StateError.None) :
  run 4 s = w StateField.PC (0x12652c#64)
    (w (StateField.SFP 29#5) (r (StateField.SFP 3#5) s)
        (w (StateField.SFP 28#5) (r (StateField.SFP 2#5) s)
            (w (StateField.SFP 27#5) (r (StateField.SFP 1#5) s)
              (w (StateField.SFP 26#5) (r (StateField.SFP 0#5) s) s)))) := by
  -- sym_n 4
  -- simp (config := {decide := true})
    -- [h_step_3, h_step_2, h_step_1, state_simp_rules] at h_step_4
  sorry

#time
theorem test_orig {s0 : ArmState}
  (h_program : s0.program = ugh_program)
  (h_pc : r StateField.PC s0 = 0x12650c#64)
  (h_err : r StateField.ERR s0 = StateError.None)
  (h_run : sf = run 8 s0) :
  sf.program = ugh_program := by
  sym_n 8 (add_hyps := true)


#time
-- set_option trace.Tactic.sym.info true in
theorem test {s0 : ArmState}
  (h_program : s0.program = ugh_program)
  (h_pc : r StateField.PC s0 = 0x12650c#64)
  (h_err : r StateField.ERR s0 = StateError.None)
  (h_run : sf = run 8 s0) :
  sf.program = ugh_program := by
  sym_block 8 (block_size := 4) -- 2 blocks: size 4 each
  done
