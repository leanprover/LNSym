/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.Experiments.VCGen.SHA512Groups

/-! Two-round groups 10–19 of SHA512's loop body (see `SHA512Groups.lean`). -/

open Std.WP ArmVCGen BitVec SHA2 sha512_helpers DPSFP
set_option experimental.vcgen true

namespace SHA512VCGen

#sha512_group g10 10
#sha512_group g11 11
#sha512_group g12 12
#sha512_group g13 13
#sha512_group g14 14
#sha512_group g15 15
#sha512_group g16 16
#sha512_group g17 17
#sha512_group g18 18
#sha512_group g19 19

end SHA512VCGen
