---
problem: Bencs–Csikvári conjecture on the number of spanning forests (F(G) ≤ ∏ deg(v) when min degree ≥ 3)
source: https://arxiv.org/abs/2611.18076 (Wu–Lu–Dong, Nov 2026, Section 1)
lean_statement: Lab/SpanningForests/Counterexample.lean (all definitions stated by us)
status: solved (formalized)
---

# Number of spanning forests vs. the degree product

## Statement
`F(G)` is the number of spanning forests of a finite simple graph `G` (edge subsets with no cycle). Bencs and
Csikvári (European J. Combin. 2023) proved `F(G) ≤ r^n` for `r`-regular graphs and conjectured that every graph
with minimum degree at least `3` satisfies `F(G) ≤ ∏_v deg(v)`.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| `F(G) ≤ r^n` for `r`-regular `G` | Bencs–Csikvári 2023 | No |
| False: `K_{a,b}` for fixed `a ≥ 3` and large `b`; smallest stated example `K_{3,14}` (via Stark's exact formula) | Wu–Lu–Dong, arXiv 2611.18076 | Yes, with `K_{3,38}` and `K_{a,4a³}` (SF-1) |
| New upper bounds for `F(G)` in terms of degrees | Wu–Lu–Dong | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| SF-1 | Lean: `F(K_{a,b}) ≥ (a+1)^b` and `∏ deg = b^a a^b`, so the conjecture fails for `K_{3,38}`, and for every `a ≥ 3` some `K_{a,b}` (we take `b = 4a³`) is a counterexample | Kyle + Claude, 2026-11-27 | pending audit | `card_le_numSpanningForests`, `prod_degree`, `not_conjecture`, `counterexample_for_every_a` in `Lab/SpanningForests/Counterexample.lean` |

Statement notes for the Auditor:
- `numSpanningForests G` = number of `S ⊆ G.edgeFinset` with `(fromEdgeSet S).IsAcyclic` (Mathlib's acyclicity).
  Isolated vertices are allowed, so this counts all spanning forests, including the empty one.
- `Conjecture` quantifies over every finite vertex type `V : Type` with decidable equality and every
  `G` with decidable adjacency; the degree product is `∏ v, G.degree v`.
- The lower bound uses "star forests": each `b`-side vertex is isolated or joined to one `a`-side vertex
  (`f : Fin b → Option (Fin a)`), each such graph is acyclic (every edge is a bridge), and `f ↦ graph` is injective.
- The concrete inequality `38^3 · 3^38 < 4^38` is checked by `norm_num`; no `decide`, no `set_option`.

## Dead ends and notes
- Not formalized: the paper's exact `K_{3,14}` example (needs Stark's closed formula for `F(K_{a,b})`) and its
  positive upper bounds.
