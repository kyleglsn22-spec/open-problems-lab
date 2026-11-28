---
problem: Mizzi's cycle conjecture for unstable graphs, as stated in v1/v2 of arXiv:2603.27559 (every nontrivially unstable graph contains C_k and C_2k, k odd)
source: https://arxiv.org/abs/2608.15281 (P. R. Srivastava, Aug 2026); conjecture in R. Mizzi, arXiv:2603.27559 v1/v2, abstract and Section 7
lean_statement: Lab/Unstable/Mizzi.lean (all definitions stated by us)
status: v1/v2 statement refuted (formalized); current v3/v4 statement (asymmetric graphs) open
---

# Unstable graphs and Mizzi's cycle conjecture

## Statement
`G` is unstable if `Aut(G × K₂)` is larger than `Aut(G) × ℤ₂`. Bipartite graphs and graphs with two vertices of equal
neighbourhood are unstable for trivial reasons; Mizzi works with connected graphs and excludes these. In versions 1 and 2
of arXiv:2603.27559 he conjectured that every such unstable graph contains cycles `C_k` and `C_{2k}` for some odd `k`.

Versions 3 and 4 (Sep and Nov 2026) restrict the conjecture to **asymmetric** unstable graphs. Srivastava's graph has
`|Aut(G)| = 2`, so it does not refute the current version; Mizzi's v4 §7 discusses it as a counterexample to the earlier
statement and also gives a smaller one (`C_6` with a pendant on an antipodal pair, 7 vertices).

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| v1/v2 statement false: 10 vertices, 11 edges, two-fold automorphism `α = (1 6)`, `β = (2 3)`, cycle lengths `5, 5, 6` | Srivastava 2608.15281 | Yes (UG-1) |
| v1/v2 statement false: 7-vertex example; conjecture restated for asymmetric graphs | Mizzi 2603.27559 v4 §7 | No |
| Asymmetric version (current) | Mizzi v3/v4 | Open |
| No connected, non-bipartite, vertex-determining asymmetric unstable graph on ≤ 9 vertices, so a counterexample to the current version needs ≥ 10 vertices (exhaustive computer search, not Lean) | our search, `explorer/unstable-asymmetric/` (2026-11-28) | Computation only |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| UG-1 | Lean: Mizzi's conjecture for unstable graphs, as stated in v1/v2, is false, via Srivastava's 10-vertex graph (not a counterexample to the current asymmetric version) | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, internal audit pass | `not_mizziConjectureV1`, `G_unstable`, `not_cycle_pair` in `Lab/Unstable/Mizzi.lean` |

Statement notes for the Auditor:
- `cdc G` is `G × K₂` on `V × Bool`. `IsUnstable G`: some automorphism of `cdc G` is not `(v, a) ↦ (φ v, a xor c)`
  for any automorphism `φ` of `G` and `c : Bool` (these are exactly `Aut(G) × ℤ₂`).
- Hypotheses of `MizziConjectureV1`: finite, connected, not 2-colourable (non-bipartite), vertex-determining
  (`neighborSet` injective), unstable. Excluding all bipartite graphs (Mizzi excludes those with nontrivial `Aut`)
  only narrows the hypotheses.
- "Contains `C_n`" is read as: some cycle walk (`Walk.IsCycle`) of length `n`, i.e. a subgraph. The counterexample
  has no odd `k` with both, so it refutes the induced reading too. (v1's §7 verification reads `C_{2k}` inside the double
  cover; under that reading the conjecture holds trivially for every non-bipartite graph, as v4 remarks, so the
  both-in-`G` reading of the abstract and of Srivastava is the meaningful one.)
- Cycles: length `≤ 10` (tail is a path), no triangle (`decide`), no 10-cycle (it would pass through the leaf `8`,
  which has one neighbour, but every cycle vertex has two cycle neighbours).
