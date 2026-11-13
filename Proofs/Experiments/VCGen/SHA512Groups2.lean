/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.Experiments.VCGen.SHA512Groups

/-! Two-round groups 20–29 of SHA512's loop body (see `SHA512Groups.lean`). -/

open Std.WP ArmVCGen BitVec SHA2 sha512_helpers DPSFP
set_option experimental.vcgen true

namespace SHA512VCGen

#sha512_group g20 20
#sha512_group g21 21
#sha512_group g22 22
#sha512_group g23 23
#sha512_group g24 24
#sha512_group g25 25
#sha512_group g26 26
#sha512_group g27 27
#sha512_group g28 28
#sha512_group g29 29

end SHA512VCGen
