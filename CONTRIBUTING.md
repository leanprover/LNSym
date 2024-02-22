# External Contribution Guidelines

Thank you for your interest in contributing to LNSym! We greatly value
feedback and contributions from the community. Please read this
document before submitting any pull requests or issues.

### Submitting a Pull Request

**Focused Changes**: Create small, focused PRs that address a single
issue or implement a specific feature.

**Maintainable Proofs**: Write your proofs in a maintainable way, even
if doing so causes them to become more verbose. LNSym follows the
***no nonterminal `simp`*** rule, which says that unless `simp` is
closing the goal, it should always be converted to a `simp only [X, Y,
Z]` call.

**External Dependencies**: Do not introduce any new external
dependencies into LNSym's codebase -- be mindful of what you
import. Exceptions are possible, but only when absolutely necessary.

**Documentation**: Add relevant documentation and comments to your
code.

**Continuous Integration**: Please ensure that all CI checks pass on
your PR. During development, you can test your contribution on your
local machine by following the build instructions in the
[README.md](https://github.com/leanprover/LNSym?tab=readme-ov-file#build-instructions).

### Filing an Issue

When filing an issue, first check whether the same issue has already
been reported previously by someone else. In your issue, include
details like:

- Illustrative, minimal, and reproducible test cases
- Commit hash of LNSym that you used
- Suggested modifications, if any

### Licensing

See the
[LICENSE](https://github.com/leanprover/LNSym/blob/main/LICENSE) file
for LNSym's licensing. All files in this project will be copyright
only by "Amazon.com, Inc. or its affiliates". The PR template will
prompt you to confirm the licensing of your contribution.

### What to Expect

**Be Patient**: Reviewing your contribution may take some time!

**Not All PRs Get Merged**: We value every contribution. However, to
enable code maintainability and quality, we will merge only those PRs
that align with our priorities and goals.

**Work in Progress**: LNSym is under development and things can change
rapidly.
