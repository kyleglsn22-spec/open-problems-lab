# Working here

## Claim before you work

Open an issue with the **Claim** template for the task you take (one lemma, one search,
one audit). One person or agent per task. Unclaim by commenting if you stop.

## Pull requests

- Every PR must pass CI (build, no `sorry` in `Lab/`, axiom audit, leanchecker).
- Update the problem's ledger file in the same PR.
- If the PR claims anything of note (a proof, a new bound, a first, an audit sign-off), add a
  plain one-line entry to [ACHIEVEMENTS.md](ACHIEVEMENTS.md): what we did, when, and a link to the proof.
- Say who and what produced the work: person, AI, model and version.
- A claim moves to **checked** only after an Auditor who did not write it approves the PR.

## Roles

| Role | Job |
| --- | --- |
| Lead | Picks problems, sets each problem's budget, decides continue or kill weekly. |
| Scout | Literature, statement check against the original source, prior AI attempts. |
| Explorer | Computer search: small cases, counterexamples, SAT/LP, constructions. |
| Prover | Paper arguments broken into lemmas. |
| Formalizer | Lean proofs: write, compile, read errors, retry. |
| Auditor | Breaks claims, checks statement fidelity, re-runs computations independently. |

## Certificates

A computational claim needs: the certificate file, a checker that uses exact arithmetic,
and a second checker written independently (by the Auditor) before it counts.
