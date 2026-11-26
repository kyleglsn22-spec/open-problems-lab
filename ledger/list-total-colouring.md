---
problem: List Total Colouring Conjecture (Borodin–Kostochka–Woodall 1997; Juvan–Mohar–Škrekovski 1998; Hilton–Johnson 1999)
source: https://arxiv.org/abs/2609.38417 (Noel, disproof, 29 Sep 2026)
lean_statement: Lab/ListTotal/Counterexample.lean (total colouring definitions from formal-conjectures FormalConjecturesForMathlib/Combinatorics/SimpleGraph/TotalColouring.lean; list version defined by us)
status: solved (formalized)
---

# List Total Colouring Conjecture

## Statement
For every multigraph `G`, the list total chromatic number equals the total chromatic number:
`χ''_ℓ(G) = χ''(G)`. A total colouring colours vertices and edges so that adjacent vertices, edges sharing an
endpoint, and a vertex with its own edges all differ; `χ''_ℓ(G)` is the least `k` such that any lists of `k`
colours on the vertices and edges allow a total colouring from the lists.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False: a cubic graph on 20 vertices (four `K_{2,3}` joined pairwise by single edges, House of Graphs 27005) has `χ'' = 4`, `χ''_ℓ = 5` | Noel, arXiv 2609.38417 (counterexample found by ChatGPT 6 Astra Ultra) | Yes: `χ'' = 4` and "not totally 4-choosable" Lean-checked (LTC-1). The upper bound `χ''_ℓ ≤ 5` (Juvan–Mohar–Škrekovski 1998, cubic graphs) is not formalized and not needed. |
| Cubic graphs have `χ''_ℓ ≤ 5`; LTCC holds for max degree ≤ 2 | Juvan–Mohar–Škrekovski 1998 | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| LTC-1 | Lean: Noel's graph has `totalChromaticNumber = 4` and is not `TotalChoosable 4`; hence `¬ ListTotalColouringConjecture` (simple-graph form) | Kyle + Claude (Opus 5.5), 2026-11-26 | audited (internal audit PASS, PR 41 review; merged PR 41, squash f101900) | `not_listTotalColouringConjecture`, `exists_counterexample` in `Lab/ListTotal/Counterexample.lean`; Python cross-checks in `explorer/list-total/` |

Statement notes for the Auditor:
- `IsTotalColoring`, `TotalColorable`, `totalChromaticNumber` are formal-conjectures' definitions (pinned commit).
- `TotalChoosable k`: every list assignment `L : V ⊕ G.edgeSet → Finset ℕ` with all lists of size `≥ k`
  admits a total colouring `c` with `c x ∈ L x`. `listTotalChromaticNumber = sInf {k | TotalChoosable k}`.
- The conjecture is stated for finite simple graphs only (a special case of multigraphs), so refuting it
  refutes the original.
- Proof follows the paper: Lemma 2.1 (`k23_private_eq`), cross-edge colour in `{i, s_i}` (`cross_mem`, `block`),
  then a kernel `decide` over the 4 private colours (`final`).

## Log
- 2026-11-26: picked in round-4 scouting (shortlist). Not on AFTD, press coverage (Post-Cutoff, 7 Oct) says no
  Lean formalization. Lean proof written and checked locally in about an hour: builds in ~12 s, standard axioms,
  leanchecker 6.9 GB peak.

## Dead ends
- (none)
