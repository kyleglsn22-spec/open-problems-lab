---
problem: Bougard–Joret conjecture on the least number of edges of a k-connected graph with given order and independence number
source: https://arxiv.org/abs/2608.18828 (Das and Gupta, Aug 2026, v1 only); conjecture: Bougard and Joret, J. Graph Theory 58 (2008), Conjecture 1 in Section 6
lean_statement: Lab/BougardJoret/Basic.lean (all definitions stated by us)
status: first regime refuted (formalized); second regime open
---

# Bougard–Joret conjecture

## Statement
`f(n, α, k)` = least number of edges of a `k`-connected graph on `n` vertices with independence number `α`. For
`n ≥ 2α`, `n ≥ α + k`, `α ≥ 2`, `k ≥ 3`, Bougard and Joret conjectured `f = ⌈nk/2⌉` when `n ≤ kα` and
`f = t(n, α) + ⌈kα/2⌉` when `n > kα` (`t` = edges of the balanced union of `α` cliques).

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| First regime fails exactly when `k − α = 1`, `k ≥ 4`; then `f = k² − 1`, extremal graphs `K̄_{k−1} ∨ T` (`T` a tree on `k` vertices) | Das–Gupta 2608.18828 | Only the smallest case `f(7,3,4) ≥ 15` (BJ-1) |
| Smallest counterexample order is 7 | Das–Gupta, Prop. 4.1 | No |
| Second regime | — | Open |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| BJ-1 | Lean: every 4-connected graph on 7 vertices with an independent 3-set has at least 15 edges, so the first regime of the Bougard–Joret conjecture fails at `(7, 3, 4)` | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, internal audit pass | `fifteen_le_card_edges`, `not_bougardJoretFirstRegime` in `Lab/BougardJoret/Basic.lean` |

Statement notes for the Auditor:
- `KConnected G k`: more than `k` vertices, and `G.induce Sᶜ` is connected for every vertex set `S` with `|S| < k`
  (the standard definition). Independence number: Mathlib's `indepNum`. Edge count: `G.edgeSet.ncard`.
- `BougardJoretFirstRegime` asserts, for admissible `(n, α, k)` with `n ≤ kα`, that a graph with `⌈nk/2⌉ = (nk+1)/2`
  edges exists and that every such graph has at least that many. We refute the existence half at `(7, 3, 4)`.
- The upper bound `f(7,3,4) ≤ 15` (`K̄_3 ∨ P_4`) is not formalized.
