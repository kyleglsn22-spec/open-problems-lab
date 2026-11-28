---
problem: Mizzi's cycle conjecture for unstable graphs (every nontrivially unstable graph contains C_k and C_2k, k odd)
source: https://arxiv.org/abs/2608.15281 (P. R. Srivastava, Aug 2026); conjecture in R. Mizzi, arXiv:2603.27559, abstract and Section 7
lean_statement: Lab/Unstable/Mizzi.lean (all definitions stated by us)
status: solved (formalized)
---

# Unstable graphs and Mizzi's cycle conjecture

## Statement
`G` is unstable if `Aut(G × K₂)` is larger than `Aut(G) × ℤ₂`. Bipartite graphs and graphs with two vertices of equal
neighbourhood are unstable for trivial reasons; Mizzi works with connected graphs and excludes these. He conjectured
that every such unstable graph contains cycles `C_k` and `C_{2k}` for some odd `k`, and checked it by computer for all
connected graphs on at most 9 vertices.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| Conjecture holds for connected graphs on `≤ 9` vertices | Mizzi 2603.27559 §7 (computer) | No |
| False: 10 vertices, 11 edges, two-fold automorphism `α = (1 6)`, `β = (2 3)`, cycle lengths `5, 5, 6` | Srivastava 2608.15281 | Yes (UG-1) |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| UG-1 | Lean: Mizzi's conjecture for unstable graphs is false, via Srivastava's 10-vertex graph | Kyle + Claude (Opus 5.5), 2026-11-28 | proved (awaiting internal audit) | `not_mizziConjecture`, `G_unstable`, `not_cycle_pair` in `Lab/Unstable/Mizzi.lean` |

Statement notes for the Auditor:
- `cdc G` is `G × K₂` on `V × Bool`. `IsUnstable G`: some automorphism of `cdc G` is not `(v, a) ↦ (φ v, a xor c)`
  for any automorphism `φ` of `G` and `c : Bool` (these are exactly `Aut(G) × ℤ₂`).
- Hypotheses of `MizziConjecture`: finite, connected, not 2-colourable (non-bipartite), vertex-determining
  (`neighborSet` injective), unstable. Excluding all bipartite graphs (Mizzi excludes those with nontrivial `Aut`)
  only narrows the hypotheses.
- "Contains `C_n`" is read as: some cycle walk (`Walk.IsCycle`) of length `n`, i.e. a subgraph. The counterexample
  has no odd `k` with both, so it refutes the induced reading too. (Reading cycles inside `cdc G` instead makes the
  conjecture vacuous for odd `k`, since `cdc G` is bipartite.)
- Cycles: length `≤ 10` (tail is a path), no triangle (`decide`), no 10-cycle (it would pass through the leaf `8`,
  which has one neighbour, but every cycle vertex has two cycle neighbours).
