---
problem: Leaf conjecture for the local antimagic chromatic number of trees
source: https://arxiv.org/abs/2610.22783 (Brondani–França, disproof, Oct 2026)
lean_statement: Lab/LocalAntimagic/Basic.lean (all definitions stated by us)
status: solved (formalized)
---

# Local antimagic chromatic number: the leaf conjecture

## Statement
For a graph with `m` edges, a bijection `f : E → {1,…,m}` gives each vertex the weight `f⁺(v)`, the sum of the labels
at `v`. `f` is local antimagic if adjacent vertices get different weights; `χ_la(G)` is the least number of distinct
weights of such an `f`. For a tree `T` with `ℓ(T)` leaves, Arumugam et al. (2017) proved `χ_la(T) ≥ ℓ(T) + 1`, and
the leaf conjecture (Bača et al. 2022; Premalatha et al. 2020) says `χ_la(T) ≤ ℓ(T) + 2` for every tree with at least
three vertices.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False: caterpillars `T₃ = Cat(8,7,25)` (`χ_la = ℓ + 3`) and `T₄ = Cat(21,20,99,100)` (`ℓ + 4`); for every `r`, infinitely many caterpillars `H_{r,t}` with `r` internal vertices on which every labelling is antimagic, so `χ_la = ℓ + r`; no constant `C` works | Brondani–França, arXiv 2610.22783 | Yes: `H_{r,t}` for all `r ≥ 2`, `t ≥ 1` (LA-1); not `T₃`, `T₄` |
| `χ_la(T) ≥ ℓ(T) + 1` | Arumugam et al. 2017 | No |
| Leaf conjecture holds for paths, stars, complete full `t`-ary trees, several spider classes | Arumugam et al.; Bača et al.; Lau–Shiu–Soo | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| LA-1 | Lean: Brondani–França Theorem 5.2 for `r ≥ 2` (up to the non-isomorphism remark, which follows from the vertex count growing with `t`) and Corollary 5.3. For `r ≥ 2`, `t ≥ 1`, the caterpillar `H_{r,t}` (spine degrees `t·4^(2^r − 2^(r−i))`) is a tree with at least 3 vertices, every labelling has pairwise distinct weights, and `χ_la = ℓ + r`. Hence `¬ LeafConjecture`, and for every `C` some tree has `χ_la > ℓ + C` | Kyle + Claude, 2026-11-27 | audited (internal audit PASS, PR 24 review) | `family`, `not_leafConjecture`, `no_constant` in `Lab/LocalAntimagic/Family.lean` (general caterpillar lemma `chiLA_eq` in `Caterpillar.lean`, degree bounds `wt_bounds` in `Basic.lean`); cross-check `explorer/local-antimagic/check.py` |

Statement notes for the Auditor:
- A labelling is `f : G.edgeSet ≃ Fin m` with `m = |E|`; the label of edge `e` is `f e + 1`, so labels are exactly
  `1,…,m`. `wt f v` sums the labels over `G.incidenceFinset v`.
- `chiLA G = sInf {n | ∃ f, IsLocalAntimagic G f ∧ |{wt f v : v}| = n}`. For `H_{r,t}` the set is nonempty
  (every labelling works), so `sInf` is a genuine minimum there.
- `numLeaves G` counts vertices of degree 1. `LeafConjecture` quantifies over finite trees (`IsTree`) with at least
  3 vertices; the decidability instances in the statement are arbitrary.
- `Cat d` (ours): spine `Fin r`, leaves `Σ i, Fin (pl d i)` with `pl d i = dᵢ − 1` at the ends and `dᵢ − 2` inside,
  so spine degrees are `dᵢ` (`degree_spine`) and leaves have degree 1. Tree via `isTree_iff_connected_and_card`, with
  the edge count from the handshake lemma.
- `Separated d` is the paper's degree-separation (Section 5.1) specialised to increasing degrees, in doubled form:
  `2m < dᵢ(dᵢ+1)` for all `i` and `2dᵢm + dᵢ < d_{i+1}(d_{i+1}+1) + dᵢ²`. These say `L_m(dᵢ) > m` and
  `U_m(dᵢ) < L_m(d_{i+1})`; spine weights then strictly increase along the spine.
- `a r i = 4^(2^r − 2^(r−(i+1)))` is the paper's `a_{i+1}` (`a r 0`, `a r 1` give `H_{2,1} = Cat(15, 63)`).
- The case `r = 1` (stars) of Theorem 5.2 is not formalized; it is not needed for the corollary.
- No `decide`, no `set_option`.

## Dead ends and notes
- `T₃` (43 vertices) is not covered: its two adjacent degree-9 vertices have overlapping weight intervals, so
  `χ_la(T₃) = 43` needs the existence of a local antimagic labelling (the paper cites Haslegrave 2018). An explicit
  labelling would make it a short follow-up.
- Open (from the paper): the minimum order of a tree with `χ_la − ℓ = r`; which trees have `χ_la = |V|`.
