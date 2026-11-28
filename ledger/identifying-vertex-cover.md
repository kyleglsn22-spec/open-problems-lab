---
problem: Henning–Yeo conjecture on identifying vertex covers (τ_D ≤ (Δ(Δ−1)n + 2m)/(Δ²+1))
source: https://arxiv.org/abs/2608.19455 (Y. Wang, Aug 2026, Theorem 3.1 and Corollary 3.2); conjecture: Henning and Yeo, Electron. J. Combin. 19(4) (2012) P32, Conjecture 3
lean_statement: Lab/IdentifyingCover/Counterexample.lean (all definitions stated by us)
status: solved (formalized)
---

# Henning–Yeo conjecture on identifying vertex covers

## Statement
An identifying vertex cover of a graph `G` is a vertex set `T` meeting every edge such that distinct edges have
distinct traces on `T`; `τ_D(G)` is the minimum size. Henning and Yeo (2012) conjectured that every finite graph of
order `n`, size `m` and maximum degree `Δ` has `τ_D(G) ≤ (Δ(Δ − 1) n + 2 m) / (Δ² + 1)`. No extra hypotheses
(connectedness etc.) appear in the conjecture.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| True for regular graphs and for `Δ ≤ 3` | Henning–Yeo 2012 | No |
| False: `H_{t,r}` (`t, r ≥ 2`), diameter two, `τ_D = n − 1` exceeds the bound by `(t − 1)(r − 1)/(Δ² + 1)`; fails for every `Δ ≥ 4` | Wang 2608.19455, Thm 3.1, Cor 3.2 | Yes (IDC-1) |
| Unbounded additive gap for every fixed `Δ ≥ 4` (Petersen fibres, block chains); `Δ c_Δ → 1` | Wang 2608.19455, §4–5 | No |
| `H_{2,2}` (8 vertices) is order-minimal (computer search over all graphs on ≤ 7 vertices) | Wang 2608.19455, Prop 6.1 | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| IDC-1 | Lean: the Henning–Yeo conjecture is false. For all `t, r ≥ 2`, `H_{t,r}` is connected, has maximum degree `t + r`, `τ_D = t + 2r + 1`, and violates the bound; hence a connected counterexample with maximum degree exactly `Δ` exists for every `Δ ≥ 4` | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, audited (pass with notes, applied) | `not_henningYeoConjecture`, `H_counterexample`, `idCoverNumber_H`, `exists_counterexample_of_maxDegree` in `Lab/IdentifyingCover/Counterexample.lean`; independent brute-force check `audit/idcover_check.py` (`2 ≤ t, r ≤ 5`) |

Statement notes for the Auditor:
- `IsIdCover G T`: every edge `e` (an element of `G.edgeSet : Set (Sym2 V)`) has a vertex in `T`, and edges with
  equal traces `{v | v ∈ e ∧ v ∈ T}` are equal.
- `idCoverNumber G = sInf {k | ∃ T, IsIdCover G T ∧ T.card = k}`; the set is nonempty (`isIdCover_univ`).
- `HenningYeoConjecture` uses `G.maxDegree`, `Fintype.card V`, `G.edgeFinset.card`, with the bound computed in `ℚ`
  (so `Δ − 1` is rational subtraction).
- Proof: the general lemma `card_le_card_add_one_of_diam_two` (if every two vertices are adjacent or share a
  neighbour, an identifying vertex cover misses at most one vertex) is Moncel's packing observation specialised to
  diameter two. Degrees are computed exactly, `2m = 4t + 5r + r²` comes from the handshake lemma, and the final
  inequality is `(Δ² + 1)(n − 1) − Δ(Δ − 1)n − 2m = (t − 1)(r − 1) > 0`.

## Dead ends
None.
