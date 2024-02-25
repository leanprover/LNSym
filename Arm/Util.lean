/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Leonardo de Moura
-/

-- Helper macro for disabling code
macro "FIXME " tacticSeq : tactic =>
  `(tactic| sorry)
