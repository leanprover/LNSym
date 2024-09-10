/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

Provide convenient syntax for writing down state manipulation in ARM programs.
-/
import Arm.State

namespace ArmStateNotation

/-! We build a notation for `read_mem_bytes $n $base $s` as `$s[$base, $n]` -/
@[inherit_doc read_mem_bytes]
syntax:max term noWs "[" withoutPosition(term)  ","  withoutPosition(term) noWs "]" : term
macro_rules | `($s[$base,$n]) => `(read_mem_bytes $n $base $s)
end ArmStateNotation
