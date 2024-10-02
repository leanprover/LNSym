import Arm
import Arm.Memory.SeparateAutomation

set_option maxHeartbeats 0
set_option trace.profiler true 
set_option profiler true

/-
tactic execution of Lean.Parser.Tactic.omega took 3.67s
instantiate metavars took 15.3s
share common exprs took 3.28s
type checking took 742ms
process pre-definitions took 475ms
linting took 262ms
elaboration took 2.07s
-/
theorem memcpy_extracted_0_line_585
(s0 si : ArmState)
(h_si_x0_nonzero : si.x0 ≠ 0)
(h_s0_x1 : s0.x1 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x1 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)))
(h_s0_x2 : s0.x2 + 0x10#64 * (s0.x0 - si.x0) + 0x10#64 = s0.x2 + 0x10#64 * (s0.x0 - (si.x0 - 0x1#64)))
(h_assert_1 : si.x0 ≤ s0.x0)
(h_assert_3 : si.x1 = s0.x1 + 0x10#64 * (s0.x0 - si.x0))
(h_assert_4 : si.x2 = s0.x2 + 0x10#64 * (s0.x0 - si.x0))
(h_assert_6 : ∀ (n : Nat) (addr : BitVec 64),
  mem_separate' s0.x2 (0x10#64 * (s0.x0 - si.x0)).toNat addr n →
    Memory.read_bytes n addr si.mem = Memory.read_bytes n addr s0.mem)
(h_assert_5 : ∀ (i : BitVec 64),
  i < s0.x0 - si.x0 →
    Memory.read_bytes 16 (s0.x2 + 0x10#64 * i) si.mem = Memory.read_bytes 16 (s0.x1 + 0x10#64 * i) s0.mem)
(h_pre_1 : mem_separate' s0.x1 (s0.x0.toNat * 16) s0.x2 (s0.x0.toNat * 16))
(h_pre_2 : r StateField.PC s0 = 0x8e0#64)
(h_pre_6 : 16 * s0.x0.toNat < 2 ^ 64)
(h_subset_2 : mem_subset' s0.x2 (0x10#64 * (s0.x0 - si.x0)).toNat s0.x2 (s0.x0.toNat * 16))
(h_subset_1 : mem_subset' (s0.x1 + 0x10#64 * (s0.x0 - si.x0)) 16 s0.x1 (s0.x0.toNat * 16))
(s2_sum_inbounds : s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)
(hi : s0.x0 - si.x0 < s0.x0 - (si.x0 - 0x1#64))
(i_sub_x0_mul_16 : 16 * (s0.x0 - si.x0).toNat < 16 * s0.x0.toNat)
(hmemSeparate_omega : s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
  s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
    (s0.x1.toNat + s0.x0.toNat * 16 ≤ s0.x2.toNat ∨ s0.x1.toNat ≥ s0.x2.toNat + s0.x0.toNat * 16))
(hmemLegal_omega : s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)
(hmemLegal_omega : s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)
(hmemSubset_omega : s0.x2.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - si.x0.toNat + s0.x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤ 2 ^ 64 ∧
  s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
    s0.x2.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - si.x0.toNat + s0.x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤
      s0.x2.toNat + s0.x0.toNat * 16)
(hmemLegal_omega : s0.x2.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - si.x0.toNat + s0.x0.toNat) % 2 ^ 64) % 2 ^ 64 ≤ 2 ^ 64)
(hmemLegal_omega : s0.x2.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)
(hmemSubset_omega : (s0.x1.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - si.x0.toNat + s0.x0.toNat) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 + 16 ≤ 2 ^ 64 ∧
  s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64 ∧
    s0.x1.toNat ≤ (s0.x1.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - si.x0.toNat + s0.x0.toNat) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 ∧
      (s0.x1.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - si.x0.toNat + s0.x0.toNat) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 + 16 ≤
        s0.x1.toNat + s0.x0.toNat * 16)
(hmemLegal_omega : (s0.x1.toNat + 16 % 2 ^ 64 * ((2 ^ 64 - si.x0.toNat + s0.x0.toNat) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 + 16 ≤ 2 ^ 64)
(hmemLegal_omega : s0.x1.toNat + s0.x0.toNat * 16 ≤ 2 ^ 64)
: s0.x2.toNat + (0x10#64 * (s0.x0 - si.x0)).toNat ≤ 2 ^ 64 ∧
  (s0.x1 + 0x10#64 * (s0.x0 - si.x0)).toNat + 16 ≤ 2 ^ 64 ∧
    (s0.x2.toNat + (0x10#64 * (s0.x0 - si.x0)).toNat ≤ (s0.x1 + 0x10#64 * (s0.x0 - si.x0)).toNat ∨
      s0.x2.toNat ≥ (s0.x1 + 0x10#64 * (s0.x0 - si.x0)).toNat + 16) := by
  bv_omega


