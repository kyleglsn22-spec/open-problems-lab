---
problem: Claw-free Schur-positivity conjecture (Stanley 1998, Conjecture 1.4, credited to Gasharov)
source: https://arxiv.org/abs/2607.26364 (Prajapati, disproof) and https://arxiv.org/abs/2607.21508 (Matherne–Morales, independent)
lean_statement: Lab/ClawFree/Defs.lean (`ClawFreeSchurPositivity`, our own statement; not in formal-conjectures)
status: solved (formalized, merged 2026-11-26 8:36 PM ET, squash 569c2aa)
---

# Claw-free Schur-positivity conjecture

## Statement
For every finite claw-free graph `G` (no induced `K_{1,3}`), Stanley's chromatic symmetric function
`X_G = ∑_{proper κ} ∏_v x_{κ(v)}` is a non-negative integer combination of Schur functions.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| True for incomparability graphs of (3+1)-free posets | Gasharov 1996 | No |
| False: line graph of a 4-cycle with triangles at two opposite vertices and pendant edges at the other two (12 vertices, 22 edges), `[s_{3333}] X_G = −64` | Prajapati, arXiv 2607.26364, Theorem 1 | **Lean-checked (CF-1)** |
| 12 vertices is the minimum; exactly two counterexamples on 12 vertices (the other has `[s_{3333}] = −40`) | Prajapati, Proposition 4 (exhaustive census, 1.9 million claw-free graphs) | The second graph is **Lean-checked (CF-2)**; the census itself is not re-run |
| Two infinite families (adjoin a clique `K_t`, `t ≥ 4`, by one edge); the −40 graph is also the smallest counterexample ordered by edges first | Wang–Zhang–Zhao, arXiv 2607.27166 | No (families); the −40 graph itself: yes (CF-2) |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| CF-1 | `¬ ClawFreeSchurPositivity`: the 12-vertex line graph `G` above is claw-free and `X_G` (in four variables) is not a non-negative combination of Schur polynomials | Kyle + Claude, 2026-11-27 (mathematics: Prajapati; Matherne–Morales) | Lean-checked, audited (internal; verdict in ledger/audits.md) | `not_clawFreeSchurPositivity`, `not_schurPositive`, `G_isClawFree` in `Lab/ClawFree/` |
| CF-2 | `¬ ClawFreeSchurPositivity` via the second minimal counterexample (graph6 ``K?`CR@`bAbRB``, 12 vertices, 21 edges): claw-free, and `X_G` in four variables is not Schur-positive (forced `[s_{3333}] = 1056 − 3·24 − 2·152 − 3·240 = −40`) | Kyle + Claude (Opus 5.5), 2026-11-26 (mathematics: Prajapati) | Lean-checked; audit pending | `OpenProblemsLab.ClawFree.Second.not_clawFreeSchurPositivity` in `Lab/ClawFree2/`; Python cross-check `explorer/clawfree2/check.py` |

Statement notes for the Auditor:
- `chromSym G n` and `schurPoly n μ` are the standard combinatorial formulas restricted to the variables
  `x_0 … x_{n-1}` (proper colourings `V → Fin n`; semistandard fillings of a Mathlib `YoungDiagram` with entries in
  `Fin n`, rows weakly increasing, columns strictly increasing). Setting the other variables to zero maps the usual
  `X_G` and `s_μ` to these, so the usual conjecture implies ours for every `n`; refuting ours at `n = 4` refutes it.
- `SchurPositive f` = `∃` finite set of diagrams and natural-number coefficients with `f = ∑ c_μ s_μ` (any sizes of
  `μ` allowed, which only makes the refuted statement stronger).
- `IsClawFree`: among any three distinct neighbours of a vertex, two are adjacent. `G` is defined directly as the
  line graph of `H` (vertices = the 12 edges of `H`, adjacent iff distinct and sharing an endpoint, `adjN`).
- Proof = the paper's triangular inversion. Kernel-computed facts: monomial coefficients `[x^{4422}] = 128`,
  `[x^{4332}] = 320`, `[x^{3333}] = 768` (proper 4-colourings by class sizes, 5,376 colourings), every
  non-increasing class-size vector of a proper colouring is one of these three, and nine Kostka numbers.
  Counting uses a verified backtracking enumerator (`Enum.lean`: `mem_gen`, `nodup_gen`, `card_filter_eq`), not
  `native_decide`. We do not prove the uniqueness of the Schur expansion, so the value −64 appears only as the
  forced value `768 − 2·128 − 3·192` inside the contradiction.
- Novelty: not on AFTD (kb.json.gz checked 2026-11-27 for both arXiv ids and "Schur-positive"), no Lean/Mathlib
  mention in either paper or web search; Mathlib has no Schur polynomials.

## Log
- 2026-11-27: internal audit pass (ledger/audits.md); moved with the lab to the public repository.
- 2026-11-27: CF-1 Lean proof done. Build peak 7.4 GB per file (colouring count split by the colours of the first
  four vertices into 84 kernel checks over 6 files; one-file version needed 12.8 GB). Standard axioms.
- 2026-11-27: smaller counterexample: according to the paper's computer census (Prajapati Prop. 4, not re-checked
  by us), 12 vertices is the minimum (all 216,777 connected claw-free graphs on ≤ 11 vertices are Schur-positive).

- 2026-11-26 (evening ET): CF-2, the second minimal counterexample, Lean-checked with the same method (four shapes:
  `5322`, `4422`, `4332`, `3333`; 7,680 proper 4-colourings, split into 256 prefixes over 8 files, each ~8.3 GB to
  build and ~6.5 GB to replay). Graph given by its edge list decoded from the graph6 code; the 16 Kostka numbers and
  the four monomial counts are kernel-computed.

## Dead ends
- Single `decide` over all 4^12 colourings: hopeless; a single backtracking list in one file: 12.8 GB.

## Open leads
- Lean-check one of the infinite families of arXiv 2607.27166.
- Re-run (or Lean-check) the minimality census: 216,777 graphs, too large for the kernel as is.
