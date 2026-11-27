---
problem: List Total Colouring Conjecture (Borodin–Kostochka–Woodall 1997; Juvan–Mohar–Škrekovski 1998; Hilton–Johnson 1999)
source: https://arxiv.org/abs/2609.38417 (Noel, disproof, 29 Sep 2026)
lean_statement: Lab/ListTotal/Counterexample.lean, Lab/ListTotal/General.lean (total colouring definitions from formal-conjectures FormalConjecturesForMathlib/Combinatorics/SimpleGraph/TotalColouring.lean; list version defined by us)
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
| LTC-2 | Lean: for every `k ≥ 4` there is a finite simple graph with maximum degree `≤ k − 1`, `χ'' = k`, not totally `k`-choosable (generalized Noel graph: `k` copies of `K_{k−2,k−1}` joined pairwise by single cross edges) | Kyle + Claude (Opus 5.5), 2026-11-27 | audited (internal audit PASS, PR 21 review) | `exists_counterexample`, `totalChromaticNumber_G`, `not_totalChoosable`, `degree_le` in `Lab/ListTotal/General.lean`; CP-SAT cross-check of the same lists and colouring for `d = 3, 4, 5` in `explorer/list-total/general_d_check.py` |

Statement notes for the Auditor:
- `IsTotalColoring`, `TotalColorable`, `totalChromaticNumber` are formal-conjectures' definitions (pinned commit).
- `TotalChoosable k`: every list assignment `L : V ⊕ G.edgeSet → Finset ℕ` with all lists of size `≥ k`
  admits a total colouring `c` with `c x ∈ L x`. `listTotalChromaticNumber = sInf {k | TotalChoosable k}`.
- The conjecture is stated for finite simple graphs only (a special case of multigraphs), so refuting it
  refutes the original.
- Proof follows the paper: Lemma 2.1 (`k23_private_eq`), cross-edge colour in `{i, s_i}` (`cross_mem`, `block`),
  then a kernel `decide` over the 4 private colours (`final`).

LTC-2 statement notes:
- Same definitions as LTC-1 (reused from `Lab/ListTotal/Counterexample.lean`). Parameter `n`, degree `d = n + 3`,
  `k = n + 4`. Vertex type `Fin (n+4) × (Fin (n+2) ⊕ Fin (n+4))`; the `d + 1` vertices `(i, inr i)` are isolated
  dummies (they only make indexing simple and do not affect `χ''`, choosability, or the degree bound).
- Lists use colours `0..d+1`: block `i` gets everything but `i`; cross edge `{p, q}` omits `om p q` (see file).
- Proof: `priv_eq` (all private vertices of a `K_{d−1,d}` block share a colour, for any `d`), `block` (cross
  edge colour in `{i, sᵢ}`), `star` (pairwise-meeting pairs `{i, sᵢ}` share an element `t`), then the cross
  edge omitting `t` fails. Explicit `(d+1)`-colouring `colT` over `Fin (n+3)` arithmetic.
- `k = 4` is Noel's graph again (up to relabelling), so LTC-2 contains LTC-1.

## Log
- 2026-11-27: LTC-2. Generalized Noel's construction to every maximum degree `d ≥ 3` (question raised by his
  closing remarks on extending the construction). Hand proof, CP-SAT check for `d = 3, 4, 5` (`d = 6` does not
  finish in 10 min), Lean proof for all `d`: builds in ~40 s, standard axioms, leanchecker passes.
  Web search (27 Nov) found no published generalization; Noel's acknowledgements mention unpublished
  discussions on extensions, so priority is uncertain.
- 2026-11-26: picked in round-4 scouting (shortlist). Not on AFTD, press coverage (Post-Cutoff, 7 Oct) says no
  Lean formalization. Lean proof written and checked locally in about an hour: builds in ~12 s, standard axioms,
  leanchecker 6.9 GB peak.

## Dead ends
- **Gap 2 (`χ''_ℓ ≥ χ'' + 2`), attempted 2026-11-27, no result.**
  - Necessary conditions (easy, by hand). Colour the vertices first (lists of size `≥ Δ + 1` suffice), then
    the edges from their lists minus the two endpoint colours. This gives `χ''_ℓ ≤ χ'_ℓ + 2`. So a gap-2 graph
    either disproves the List Edge Colouring Conjecture, or is Type 1 (`χ'' = Δ + 1`), class 2
    (`χ' = Δ + 1`) and has `χ''_ℓ = χ'_ℓ + 2 = Δ + 3` exactly. Also `Δ ≥ 4`, since cubic graphs are totally
    5-choosable (Juvan–Mohar–Škrekovski) and the conjecture holds for `Δ ≤ 2`.
  - Why Noel's method does not extend: his blocks are rigid because each block's palette is exactly `Δ + 1`,
    the minimum a vertex star needs. For gap 2 the lists have size `Δ + 2`. A block that is rigid at `Δ + 2`
    colours would need its own `χ''` to be `Δ + 2`, which contradicts the whole graph being Type 1. So the
    forcing must come from lists that differ inside a block, not from uniform block lists.
  - Computer search (`explorer/list-total/cegar_bad_lists.py`, CEGAR with two SAT solvers). Lists are a
    palette of `P` colours minus `P − k` colours.
    - `K_5` (`Δ = 4`, Type 1, class 2), `k = 6`: every assignment from a 7-colour palette is colourable (39 s).
      An 8-colour palette did not finish in 30 min.
    - Complement of `C_3 ∪ C_4` (4-regular on 7 vertices, Type 1, class 2), `k = 6`, `P = 7`: did not finish
      in 50 min.
    - Fat-triangle multigraphs `(m, m, m)` (`χ'' = χ' = 3m`). For `m = 2`, `k = 7`: colourable for
      `P = 8, 9, 10`. For `m = 3`, `k = 10`: colourable for `P = 11`; `P = 12` did not finish.
    - The complement of `C_7` is Type 2 (`χ'' = 6`), so it is not a candidate.
  - These palette-limited checks do not rule anything out in general (a bad assignment may need many more
    colours). The naive CEGAR does not scale past about 15 elements. A real attempt needs either a new forcing
    gadget or a much stronger solver.
