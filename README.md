# Open Problems Lab

A small, serious attempt at lesser-known open problems in mathematics, run by one person with AI
agents. Every result marked "Lean-checked" here is a formal Lean 4 / mathlib proof that this
repository's CI rebuilds and re-checks on every change.

This is the public copy of the lab folder of a private working repository. "PR #n" in the notes
refers to pull requests there; the proof files themselves are all here.

## Results so far

See [ACHIEVEMENTS.md](ACHIEVEMENTS.md) for a dated, plain-language log. In short:

| Problem | What is proved here | Lean file |
| --- | --- | --- |
| [Erdős #757](https://www.erdosproblems.com/757) | upper bounds 7/12, 4/7 and 5/9 | `Lab/Erdos757/UpperBound.lean`, `FourSevenths.lean`, `FiveNinths.lean` |
| Erdős #757 | lower bound 9/17, conditional on Henning–Yeo (2021), stated as an explicit hypothesis | `Lab/Erdos757/LowerBound.lean` |
| Tao's C37 (degree vs sensitivity) | no Boolean function of degree ≤ 4 has sensitivity 10 | `Lab/C37/Degree4.lean` |
| Tao's C44 (relevant variables) | C44 ≥ 3/2 (Chiarelli–Hatami–Saks construction, all degrees) | `Lab/C44/LowerBound.lean` |
| Davenport constant | the van Emde Boas–Kruyswijk conjecture fails for C_6^15 (Gao–Geroldinger–Wang–Zeng counterexample) | `Lab/Davenport/VanEmdeBoasKruyswijk.lean` |

Constructions credited to others are theirs; what we add is the machine-checked proof. Details,
sources and dead ends are in [ledger/](ledger/).

## Rules

1. **Lean is the only judge.** A result counts as checked only when it builds here with no
   `sorry`, and `scripts/Axioms.lean` shows only `propext`, `Classical.choice` and
   `Quot.sound`. CI also replays every module with `leanchecker`.
2. **Statements come from formal-conjectures** (pinned in `lakefile.toml`) whenever they
   exist there, so we prove exactly the reviewed statement.
3. **The author never audits their own claim.** An Auditor (a separate AI session) checks that
   each Lean statement says what the problem says, and re-runs every computation with
   independently written code. Outside review is very welcome: open an issue.
4. **Dead ends are results too.** Every refuted claim or abandoned approach goes in the
   ledger with the reason.
5. **Record which AI produced what**, with model and version.

## Layout

| Path | What it holds |
| --- | --- |
| `ledger/` | One Markdown file per problem: statement, status, claims, attempts, dead ends. `shortlist.md` is the candidate list. |
| `Lab/` | Lean proofs, one folder per problem. |
| `explorer/` | Search code and certificates. Every certificate has its own checker. |
| `audit/` | The Auditor's independent re-checks. |
| `scripts/` | CI checks: no `sorry`, axiom audit, kernel replay. CI runs from `.github/workflows/lean.yml`. |

## Check it yourself

```
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
lake update
lake exe cache get
lake build
bash scripts/check_no_sorry.sh && bash scripts/check_axioms.sh && bash scripts/check_kernel.sh
```
