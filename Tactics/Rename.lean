/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat
-/

/--
rename an old term `old` identifier a new identifier `new`, and replace
all occurrences of `old` with `new`.
-/
macro "rename" old:ident "to" new:ident : tactic =>
  `(tactic|
    generalize h_rename : $old = $new <;> subst $old)
