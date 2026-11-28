# How we work

Since 2026-11-27 this public repository is the lab's working repository: all Lean proofs,
ledger notes, audits and their pull requests happen here, in the open. That includes work in
progress and failed attempts; dead ends are results too.

## Rules

1. **Lean is the only judge.** A result counts as checked only when it builds here with no
   `sorry`, `scripts/Axioms.lean` shows only `propext`, `Classical.choice` and `Quot.sound`,
   and `leanchecker` re-checks it. CI enforces all of this on every pull request.
2. **Statements come from formal-conjectures** (pinned in `lakefile.toml`) whenever they exist
   there, so we prove exactly the reviewed statement.
3. **The author never audits their own claim.** An Auditor (a fresh AI session, or an outside
   reviewer) checks that each Lean statement says what the problem says, and re-runs every
   computation with independently written code. Verdicts go in `ledger/audits.md`.
4. **Dead ends are results too.** Every refuted claim or abandoned approach goes in the ledger
   with the reason.
5. **Record who and what produced the work**: person, AI, model and version.

## Pull requests

- Branch from `main`, open a pull request here. CI must be green (build, no `sorry` in `Lab/`,
  axiom audit, leanchecker).
- Update the problem's file in `ledger/` in the same PR (new problems start from
  `ledger/TEMPLATE.md`).
- If the PR claims anything of note (a proof, a new bound, a first, an audit sign-off), add a
  plain one-line entry to [ACHIEVEMENTS.md](ACHIEVEMENTS.md): what we did, when, and a link to the
  proof. New results also get a row in the README's results table.
- A PR is merged once CI is green and an Auditor who did not write it has signed off.
- Never put anything here that is not lab work: no private notes, credentials, emails or
  links to private pages.

## Roles

| Role | Job |
| --- | --- |
| Lead | Picks problems, decides continue or kill. |
| Scout | Literature, statement check against the original source, prior AI attempts. |
| Explorer | Computer search: small cases, counterexamples, SAT/LP, constructions. |
| Prover | Paper arguments broken into lemmas. |
| Formalizer | Lean proofs: write, compile, read errors, retry. |
| Auditor | Breaks claims, checks statement fidelity, re-runs computations independently. |

## Certificates

A computational claim needs the certificate file, a checker that uses exact arithmetic, and a
second checker written independently (by the Auditor, in `audit/`) before it counts.

## CI and cost

CI runs on GitHub Actions, free for public repositories. Pull requests rebuild and kernel-replay
only what changed (cached); every push to `main` replays every module from scratch. See
`.github/workflows/lean.yml` and `scripts/check_kernel.sh`.

## Local build

```
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
lake exe cache get
lake build
bash scripts/check_no_sorry.sh && bash scripts/check_axioms.sh && bash scripts/check_kernel.sh
```
Pass `-DautoImplicit=false` when running `lake env lean` on a single file.
