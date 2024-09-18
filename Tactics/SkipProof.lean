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

This is to be used, during development, with expensive tactics such as `omega`, `bv_omega`, `bv_decide`, `simp_mem`.
This allows one to run `have expensive_hyp : ... := by omega`, check that this can be proven,
and to then replace this with `have expensive_hyp : ... := by skip_proof omega`,
which will skip the use of `omega`, and instead of `skipProoxAx`, ensuring Lean stays interactive.

`skip_proof p` signals that when `set_option skip_proof.skip false` is set, the proof `p` *will go through*.
This makes `skip_proof p` morally different from a `sorry`:
- It still retains the proof `p`. This signals the intent of a completed proof that has been skipped for performance.
- It uses a different axiom (`skipProofAx` instead of `sorryAx`).
  This allows `#print axioms in thm` to distinguish between skipped proofs and genuine `sorry`s.
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
