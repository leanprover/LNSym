/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

Provide convenient syntax for writing down state manipulation in Arm programs.
-/
import Arm.State
import Arm.Memory.Separate

namespace ArmStateNotation

/-! We build a notation for `read_mem_bytes $n $base $s` as `$s[$base, $n]` -/
@[inherit_doc read_mem_bytes]
syntax:max term noWs "[" withoutPosition(term)  ","  withoutPosition(term) noWs "]" : term
macro_rules | `($s[$base,$n]) => `(read_mem_bytes $n $base $s)


/-! Notation to specify the frame condition for non-memory state components. E.g.,
`REGS_UNCHANGED_EXCEPT [.GPR 0, .PC] (sf, s0)` is sugar for
`∀ f, f ∉ [.GPR 0, .PC] → r f sf = r f s0`
-/
syntax:max "REGS_UNCHANGED_EXCEPT" "[" term,* "]"
            "(" withoutPosition(term) "," withoutPosition(term) ")" : term
macro_rules
| `(REGS_UNCHANGED_EXCEPT [$regs:term,*] ($sf, $s0)) =>
    `(∀ f, f ∉ [$regs,*] → r f $sf = r f $s0)

/-! Notation to specify the frame condition for memory regions. E.g.,
`MEM_UNCHANGED_EXCEPT [(x, m), (y, k)] (sf, s0)` is sugar for
`∀ n addr, Memory.Region.pairwiseSeparate [(addr, n), (x, m), (y, k)] → sf[addr, n] = s0[addr, n]`
-/
syntax:max "MEM_UNCHANGED_EXCEPT" "[" term,* "]"
            "(" withoutPosition(term) "," withoutPosition(term) ")" : term
macro_rules |
  `(MEM_UNCHANGED_EXCEPT [$mem:term,*] ($sf, $s0)) =>
            `(∀ (n : Nat) (addr : BitVec 64),
                  Memory.Region.pairwiseSeparate (List.cons (addr, n) [$mem,*]) →
                  read_mem_bytes n addr $sf = read_mem_bytes n addr $s0)

end ArmStateNotation
