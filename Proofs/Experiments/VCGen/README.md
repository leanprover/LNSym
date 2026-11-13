# Lean `vcgen` for LNSym (experimental)

Library: `Tactics/VCGen.lean` (program type, specs, tactics, composing
triples) and `Correctness/VCGen.lean` (bridges to the cut-point method, partial
and total correctness). Pilots in this directory:

- `Popcount32VCGen.lean`: `popcount32_sym_meets_spec` (functional result,
  register and memory frames) as one `vcgen` triple over a straight-line
  segment, plus the same statement in `run 27` form.
- `AddLoopVCGen.lean`: `AddLoop.partial_correctness` by the cut-point method,
  each cut-to-cut segment (including both sides of the loop's conditional
  branch) proved by `vcgen`; and total correctness (`correctness_vcgen`) by
  `Correctness.by_the_method`.
- `SHA512VCGen.lean` (with `SHA512Rounds.lean`, `SHA512Groups*.lean`): total
  correctness of `sha512_block_armv8` (504 instructions, any number of blocks)
  against the specification's `processBlocks_alt`; see below.

## The approach

`ArmCmd` describes control flow only (`stepAt pc`, `seq`, `ite_pc`), and its
weakest precondition `wpCmd` is defined by LNSym's `stepi`, so the ISA model is
unchanged. `wpCmd_run` shows that a provable triple describes real execution
(`run`); the bridges in `Correctness/VCGen.lean` turn triples about segments
between cut points into the obligations of LNSym's cut-point method.

Commands are built from the program's control-flow graph (`buildSeg`,
`#genVCGenSegment`). The specs `vcgen` uses are generated from the step
theorems of `#genStepEqTheorems`, one per address. They name the next state
instead of substituting it (`Next f s s'`) and hand the next step its side
conditions (`Side`), proved once per instruction, so each step's verification
condition closes by `assumption` and the work per condition does not grow with
the program. Only a postcondition expands the chain of state writes of its
path (`arm_vc_final`).

For long programs, prove short segments separately and compose their triples
(`triple_seq`): each `vcgen` run then sees only its own instructions.

## How a proof goes

1. `#genStepEqTheorems prog` (existing), then `#genVCGenSpecs prog` inside a
   namespace: one `@[spec]` per address, scoped to that namespace.
2. `#genVCGenSegment seg := buildSeg prog stop fuel pc`: the control flow from
   `pc` as an `ArmCmd` literal.
3. State the specification as a triple `⦃ pre ⦄ seg ⦃ post ⦄` and run `vcgen`.
4. `all_goals first | arm_vc_step | (…; arm_vc_final)`: `arm_vc_step` closes
   every step's side conditions; the remaining VCs are postconditions, which
   `arm_vc_final` simplifies; finish those as usual (`bv_decide`, `simp_mem`, …).
5. For long segments, prove short pieces separately and compose them with
   `triple_seq`.
6. Bridge to LNSym's statements: `run_of_triple` (straight line),
   `nextc_of_triple` (cut points, partial correctness) or
   `by_the_method_v4_of_triple` (cut points with a rank, total correctness).

## SHA512 (`SHA512VCGen.sha512_correct`)

`sha512_correct` is total correctness (`Correctness`: partial correctness and
termination) for the specification `preS`/`postS`/`exit`:

- `preS`: the program is loaded and at its entry, `N = x2 ≥ 1` blocks of input
  at `x1`, the table `flatten k_512.reverse` at `kt`, and the 16-byte stack frame
  below `sp` separate from the context (64 bytes at `x0`), the input and the
  table.
- `postS`, at the `ret`: the context holds
  `(processBlocks_alt 80 H k_512 blocks).toBitVec`, where `H` is the hash the
  context held on entry and `blocks` are the input's big-endian 64-bit words;
  `x0`, `x29`, `x30`, `sp` and every register the program does not write are
  unchanged, and so is memory outside the stack frame and the context.

`preS_satisfiable` exhibits a state satisfying `preS`. Besides `propext`,
`Classical.choice` and `Quot.sound`, the proof uses the axioms `bv_decide`
introduces for its native checking (LNSym's instruction-rule lemmas and a few
small lemmas in these files), which trust the Lean compiler.

The proof is by the cut-point method, with cut points at the entry, the loop
head and the `ret`, and a rank that decreases from one to the next (`x2`, the
number of blocks left, decreases around the loop). One trip around the loop is
composed from the header, 40 two-round groups, the tail and the branch, each its
own triple. Group `k`'s precondition `GI P k` states the registers in terms of
the specification: the working state after `2k` rounds, the message window and
the next round-constant pair. `#sha512_group` proves all 40 group triples with one
script; the SHA-specific facts are `group_ok` (from `two_rounds`) and `sched_Wp`
(from `sched_step`). `correctness` is the same theorem with the context and the
input as the program loads them (128-bit lanes, `rev64` of 16-byte loads);
`sha512_correct` follows from it.

Addresses: the entry is `SHA512.program`'s lowest address; the other code
addresses are offsets from it fixed by the code's shape (`SHA512Groups.lean`);
the table is where the prologue's `adrp`/`add` point. `arm_lit%` evaluates each to
a literal. A rebuild that moves the code or the table needs only a new
`SHA512.program`; a change to the code needs new offsets.

| file | time |
|---|---:|
| `SHA512Groups.lean` (definitions, 502 specs) | 17 s |
| `SHA512Groups0`–`3.lean` (10 group triples each, built in parallel) | 7 s each |
| `SHA512VCGen.lean` (the rest, and the theorems) | 16 s |

Notes:

- Triples are composed with `triple_seq` rather than verified as one long
  command, so each value-dependent postcondition expands only a group's chain
  of writes.
- A plain `assumption` or `exact` on a goal about SHA values can unfold
  `sha512h` against every hypothesis; the closers use `with_reducible`.
- Register indices are dependent arguments (`r (.SFP i) s : state_value
  (.SFP i)`), so `simp` cannot rewrite `i` with ordinary lemmas; definitional
  simprocs (`Nat.reduceMod`, `↓dreduceIte`, …) evaluate a computed index.
- `decide` and a single `simp` exceed the recursion limit on hundreds of
  addresses; `arm_pcs` checks a command's addresses one instruction at a time.

## Limitations and next steps

- `Side` includes `CheckSPAlignment`, so preconditions must assume it.
- Specs are keyed on the address and scoped to the namespace where they are
  generated: two programs at the same addresses must not have both namespaces
  open.
- Per-instruction-word specs: SHA512 has 111 distinct words in 504
  instructions, the AES-GCM kernel 263 in 718. Generating specs per word and
  instantiating them per address would cut generation time.
- Per-instruction-class specs (symbolic register fields) would go further, but
  need the decoded instruction in `ArmCmd` and a fast fetch lemma per address.
- `ite_pc`'s spec uses `⇨`/`⊓`; `vcgen` also splits `if`s in program position,
  which may make a plainer spec possible.
- Compiling a large `ArmCmd` literal crashes the Lean compiler (an IR check
  failure): `#eval` of a generated command, or a `def` of a composed one (mark
  it `noncomputable`). `#genVCGenSegment` adds its definition without compiling
  it.
