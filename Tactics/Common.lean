/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

import Lean
import Arm.Exec
open Lean Elab Tactic Expr Meta
open BitVec


/- Obtain `Array α` from `Array (Option α)` by discarding any `none`
elements. -/
private def optionArraytoArray (array : Array (Option α)) : Array α :=
  Array.foldl (fun acc val =>
    match val with
    | none => acc
    | some v => acc.append #[v])
  #[] array

/- Find all declarations in the `LocalContext` whose username begins
with `pfxUserName`. -/
def filterDeclsWithPrefix (lctx : LocalContext) (pfxUserName : Name)
  : (Array LocalDecl) :=
  optionArraytoArray
  (PersistentArray.toArray
    (PersistentArray.filter
      lctx.decls
      (fun decl =>
        match decl with
          | none      => false
          | some decl => String.isPrefixOf (toString pfxUserName)
                                           (toString decl.userName))))
