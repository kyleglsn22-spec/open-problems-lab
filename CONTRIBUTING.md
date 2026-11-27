# Contributing

Corrections and review are very welcome. How the lab itself works is in [WORKFLOW.md](WORKFLOW.md).

- **A statement looks wrong** (a Lean definition does not match the problem as published): open an
  issue naming the file and the definition. This is the most valuable kind of review, because the
  Lean kernel checks the proofs but cannot check that we formalized the right question.
- **Prior work we missed** (an earlier proof or formalization): open an issue with a link, and we
  will correct the notes and credits.
- **Pull requests**: must pass CI (build, no `sorry` in `Lab/`, axiom audit, `leanchecker`). Update the
  problem's file in `ledger/` in the same PR, and say who and what produced the work, including any
  AI model and version used.

Computational claims ship with the certificate, an exact-arithmetic checker, and an independently
written second checker in `audit/`.
