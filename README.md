# Open Problems Lab

[![Lean checks](https://github.com/kyleglsn22-spec/open-problems-lab/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/kyleglsn22-spec/open-problems-lab/actions/workflows/lean.yml)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)

Machine-checked proofs, in [Lean 4](https://lean-lang.org) with [mathlib](https://github.com/leanprover-community/mathlib4),
of results on lesser-known open problems in combinatorics and Boolean function analysis.

Every theorem listed below builds in this repository's CI with **no `sorry`**, depends only on
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`; no `native_decide`),
and is re-checked by the independent kernel checker `leanchecker`. Where a statement exists in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(pinned in `lakefile.toml`), we prove exactly that statement.

## Results

| Problem | Result | Lean theorem | Origin of the mathematics |
| --- | --- | --- | --- |
| [Erdős #757](https://www.erdosproblems.com/757): the largest c such that every finite (4,5)-set A ⊂ ℝ has a Sidon subset of size ≥ c·\|A\| | c ≤ 5/9 | [`sSup_le_five_ninths`](Lab/Erdos757/FiveNinths.lean) | construction posted online (Oct 2026); Lean proof for every size is ours |
| | c ≤ 4/7 | [`sSup_le_four_sevenths`](Lab/Erdos757/FourSevenths.lean) | Ma–Tang, [arXiv:2602.23282](https://arxiv.org/abs/2602.23282) |
| | c < 3/5 (via c ≤ 7/12) | [`erdos_757_upperBound`](Lab/Erdos757/UpperBound.lean) | Gyárfás–Lehel (1995) |
| | c ≥ 9/17, with no assumptions: includes a full Lean proof of the Henning–Yeo (2021) hypergraph transversal theorem it relies on | [`erdos_757_lowerBound`](Lab/Erdos757/Unconditional.lean) | Ma–Tang; Henning–Yeo |
| Davenport constant: van Emde Boas–Kruyswijk conjecture D(C_n^r) = r(n−1)+1 (1969) | false for C_6^15 | [`not_vanEmdeBoasKruyswijk`](Lab/Davenport/VanEmdeBoasKruyswijk.lean) | Gao–Geroldinger–Wang–Zeng, [arXiv:2611.24775](https://arxiv.org/abs/2611.24775) |
| | false for all n ≡ 2 (mod 4), n ≥ 6, r ≥ 5n/2 | [`vEBK_fails`](Lab/Davenport/GeneralFamily.lean) | Gao–Geroldinger–Wang–Zeng |
| | D(C_n^r) ≥ r(n−1)+1+⌊(r−1)/(5k−1)⌋ for n = 2k ≡ 2 (mod 4), n ≥ 6, every r (their Theorem 1.1 in full) | [`ggwz_floor`](Lab/Davenport/FloorTerm.lean) | Gao–Geroldinger–Wang–Zeng |
| List Total Colouring Conjecture: χ''_ℓ(G) = χ''(G) for every (multi)graph (late 1990s) | false: a cubic 20-vertex graph with χ'' = 4 that is not totally 4-choosable | [`not_listTotalColouringConjecture`](Lab/ListTotal/Counterexample.lean) | Noel, [arXiv:2609.38417](https://arxiv.org/abs/2609.38417) |
| Non-abelian Gyarmati–Matolcsi–Ruzsa inequality (2010, Problem 1.3) | false for four sets in a class-two group of order 2^17 = 131,072 (**new**: smallest published four-set example had order 518,400) | [`not_nonAbelianGMR`](Lab/GMR/Counterexample.lean) | Ours, building on Elsholtz's template ([arXiv:2611.12776](https://arxiv.org/abs/2611.12776)); disproof by Nair–Namayandeh–Zhu ([arXiv:2611.00156](https://arxiv.org/abs/2611.00156)) |
| Claw-free Schur-positivity conjecture (Stanley 1998, credited to Gasharov): X_G is Schur-positive for every claw-free graph | false: the 12-vertex line graph G = L(H), with [s_(3,3,3,3)] X_G = −64 | [`not_clawFreeSchurPositivity`](Lab/ClawFree/Counterexample.lean) | Prajapati, [arXiv:2607.26364](https://arxiv.org/abs/2607.26364); independently Matherne–Morales, [arXiv:2607.21508](https://arxiv.org/abs/2607.21508) |
| [Degree vs sensitivity](https://teorth.github.io/optimizationproblems/constants/37a.html) (Tao's constant C37) | no Boolean function of degree ≤ 4 has sensitivity 10 | [`no_degree4_sensitivity10`](Lab/C37/Degree4.lean) | Koshta (2026) result; our shorter two-block proof |
| [Relevant variables](https://teorth.github.io/optimizationproblems/constants/44a.html) (Tao's constant C44) | C44 ≥ 3/2 | [`three_halves_le`](Lab/C44/LowerBound.lean) | Chiarelli–Hatami–Saks, [arXiv:1801.08564](https://arxiv.org/abs/1801.08564) |

Where the mathematics is someone else's, our contribution is the formal verification; as far as
we could find, these are the first machine-checked proofs of these results (we may have missed
something, and corrections are welcome). A dated plain-language log is in
[ACHIEVEMENTS.md](ACHIEVEMENTS.md), and each problem's full notes, sources, computations and dead
ends are in [`ledger/`](ledger/).

## Verify it yourself

You need [elan](https://github.com/leanprover/elan) (the Lean version manager); everything else is
pinned (`lean-toolchain`, `lake-manifest.json`).

```sh
git clone https://github.com/kyleglsn22-spec/open-problems-lab && cd open-problems-lab
lake exe cache get          # download prebuilt mathlib
lake build                  # compile every proof
bash scripts/check_no_sorry.sh
lake env lean scripts/Axioms.lean   # prints the axioms each main theorem uses
bash scripts/check_kernel.sh        # independent kernel re-check (needs ~8 GB RAM)
```

The same steps run on every push; see the [Actions tab](https://github.com/kyleglsn22-spec/open-problems-lab/actions).

## Repository layout

| Path | Contents |
| --- | --- |
| [`Lab/`](Lab/) | Lean proofs, one folder per problem |
| [`ledger/`](ledger/) | One file per problem: statement, known results, our claims, attempts and dead ends |
| [`explorer/`](explorer/) | Computer searches, certificates and their exact checkers (Python/C) |
| [`audit/`](audit/) | Independent re-implementations used to cross-check computations |
| [`scripts/`](scripts/) | CI checks: no `sorry`, axiom audit, kernel replay |
| [`ACHIEVEMENTS.md`](ACHIEVEMENTS.md) | Dated log of results |

## How this was made

This is a one-person project run with AI assistance: Claude (Anthropic) wrote the Lean proofs and
search code, and a separate AI session reviewed each claim, checking that every Lean statement
matches the problem as published and re-running computations with independently written code.
The Lean kernel, not any AI or person, is the judge of correctness; the remaining human-trust
points are the *statements* (please check them).
This repository is a public mirror of the project's working folder; "PR #n" in the notes refers to
the working repository's pull requests.

## Citing

See [CITATION.cff](CITATION.cff) (GitHub's "Cite this repository" button). Please also cite the
original authors of each result listed above.

## Contact

Found a mistake, or a prior formalization we missed? Please [open an issue](https://github.com/kyleglsn22-spec/open-problems-lab/issues).
See [CONTRIBUTING.md](CONTRIBUTING.md).
