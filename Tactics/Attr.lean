import Lean

open Lean

initialize
  registerTraceClass `Tactic.cse -- high level info.

initialize
  registerTraceClass `Tactic.cse.info -- low level debugging info.
