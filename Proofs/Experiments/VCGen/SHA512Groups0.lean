/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.Experiments.VCGen.SHA512Groups

/-! Two-round groups 0–9 of SHA512's loop body (see `SHA512Groups.lean`). -/

open Std.WP ArmVCGen BitVec SHA2 sha512_helpers DPSFP
set_option experimental.vcgen true

namespace SHA512VCGen

#sha512_group g0 0
#sha512_group g1 1
#sha512_group g2 2
#sha512_group g3 3
#sha512_group g4 4
#sha512_group g5 5
#sha512_group g6 6
#sha512_group g7 7
#sha512_group g8 8
#sha512_group g9 9

end SHA512VCGen
