import Lean

open Lean Meta Elab Tactic

namespace SkipProof

register_option skip_proof.skip : Bool := {
  defValue := False
  descr := "If `skip` is true, `skip_proof p` skips running `p` and closes the goal with `skipProofAx`."
}

/--
Surrounding a tactic with `skip_proof` will skip running the tactic and close the goal with `skipProofAx`.
We only skip proofs `skip_proof.skip` is set to `true`,
and we emit a warning to remind the user that proofs are being skipped.
-/
syntax (name := skip_proof) "skip_proof" tactic : tactic
axiom skipProofAx {α : Sort _} : α

@[tactic skip_proof]
def skipProof : Tactic := fun
  | `(tactic| skip_proof $x) => do
    let opts ← Lean.getBoolOption `skip_proof.skip
    if opts then
      logWarningAt x "Skipped by `skip_proof`"
      evalTactic (← `(tactic| exact skipProofAx))
    else
      evalTactic x
  | _ => throwUnsupportedSyntax

end SkipProof
