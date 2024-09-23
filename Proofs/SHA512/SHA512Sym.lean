/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

import Proofs.SHA512.SHA512Prelude
import Proofs.SHA512.SHA512Loop

/-! ### Symbolic Simulation for SHA512 (1 message block)
In this experiment to stress-test our symbolic simulation and memory reasoning
automation, we fix the number of blocks to be hashed (in register `x2`) to `1`,
which essentially transforms the SHA512 program into a straight-line one.

We attempt to prove that the final state after symbolically simulating a fixed
number of SHA512 instructions is error free and that register x2 is 0 --- note
that the register `x2` is decremented early on in this program:

    (0x126504#64 , 0xf1000442#32),      --  subs    x2, x2, #0x1

In the near future, we'd like to prove that the hash computed for this
one input block matches the expected value, i.e., one dictated by
`SHA2.sha512`.

Also see `Tests.SHA2.SHA512ProgramTest` for an example of a concrete
run that checks the implementation against the specification.
-/
