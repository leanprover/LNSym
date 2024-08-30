import Tests.«AES-GCM».GCMGmultV8Program
import Tactics.Sym
import Tactics.StepThms
import Specs.GCMV8

namespace GCMGmultV8Program

#genStepEqTheorems gcm_gmult_v8_program

theorem gcm_gmult_v8_program_run_27 (s0 sf : ArmState)
    (h_s0_program : s0.program = gcm_gmult_v8_program)
    (h_s0_err : read_err s0 = .None)
    (h_s0_pc : read_pc s0 = gcm_gmult_v8_program.min)
    (h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run gcm_gmult_v8_program.length s0) :
    read_err sf = .None
    ∧ let xiAddr := r (.GPR 0#5) s0
      let hTableAddr := r (.GPR 1#5) s0
      let xiInput := read_mem_bytes 16 xiAddr s0
      let hTable := read_mem_bytes (16) hTableAddr s0
      let xiOut := read_mem_bytes 16 xiAddr sf
      xiOut = GCMV8.GCMGmultV8' hTable xiInput
    := by
  simp (config := {ground := true}) only at h_s0_pc
  -- ^^ Still needed, because `gcm_gmult_v8_program.min` is somehow
  --    unable to be reflected
  sym_n 27
  conv => {
    rhs;
    simp [GCMV8.GCMGmultV8', GCMV8.gcm_polyval,
      GCMV8.gcm_polyval_red,
      GCMV8.gcm_polyval_mul,
      GCMV8.gcm_init_H,
      GCMV8.pmult,
      GCMV8.pmod,
      GCMV8.lo,
      GCMV8.hi,
      GCMV8.irrepoly,
      bitvec_rules,
      minimal_theory
      ]
  }
  sorry
  done
