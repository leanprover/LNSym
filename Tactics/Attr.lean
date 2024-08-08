import Lean

open Lean

initialize
  registerTraceClass `Tactic.cse -- high level info.

initialize
  registerTraceClass `Tactic.cse.info -- low level debugging info.
  registerTraceClass `Tactic.cse.collection -- low level debugging info.
  registerTraceClass `Tactic.cse.summary -- low level debugging info.
  registerTraceClass `Tactic.cse.generalize -- low level debugging info.
