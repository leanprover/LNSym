/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proofs.Experiments.VCGen.SHA512Groups

/-! Two-round groups 30–39 of SHA512's loop body (see `SHA512Groups.lean`). -/

open Std.WP ArmVCGen BitVec SHA2 sha512_helpers DPSFP
set_option experimental.vcgen true

namespace SHA512VCGen

#sha512_group g30 30
#sha512_group g31 31
#sha512_group g32 32
#sha512_group g33 33
#sha512_group g34 34
#sha512_group g35 35
#sha512_group g36 36
#sha512_group g37 37
#sha512_group g38 38
#sha512_group g39 39

end SHA512VCGen
