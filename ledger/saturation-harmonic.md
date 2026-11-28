---
problem: TxGraffiti conjecture μ*(G) ≤ H(G) (saturation number vs harmonic index)
source: https://arxiv.org/abs/2606.15761 (C. Gupta, Jun 2026, Theorem 1); first disproof: Bıyıkoğlu (2026); conjecture: TxGraffiti (2023), listed as Conjecture 4 in Davila–Brimkov–Pepper (2025)
lean_statement: Lab/Saturation/Harmonic.lean (all definitions stated by us)
status: solved (formalized)
---

# TxGraffiti: saturation number vs harmonic index

## Statement
`μ*(G)` is the minimum size of a maximal matching; `H(G) = ∑_{uv ∈ E} 2/(d(u) + d(v))`. Conjecture: every nontrivial
connected graph has `μ*(G) ≤ H(G)`.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False: joins of a matching with an independent set; ratio `μ*/H` unbounded | Bıyıkoğlu 2026 | No |
| False: friendship graph `F_k`, `μ* = k > 2k/(k+1) + k/2 = H` for all `k ≥ 4` (`F_4`, 9 vertices) | Gupta 2606.15761, Thm 1 | Yes (SAT-1) |
| 9 vertices is the smallest order; trees fail too (subdivided stars `S_k`, `k ≥ 5`); `μ*(T) < (3/2) H(T)` for trees | Gupta 2606.15761 | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| SAT-1 | Lean: the conjecture is false. `μ*(F_k) = k`, `H(F_k) = 2k/(k+1) + k/2`, and `F_k` is a connected counterexample for every `k ≥ 4` | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, internal audit pass | `not_txGraffitiConjecture`, `F_counterexample`, `saturationNumber_F`, `harmonicIndex_F` in `Lab/Saturation/Harmonic.lean`; independent check `audit/saturation_harmonic_check.py` (`k ≤ 6`) |

Statement notes for the Auditor:
- `IsMaximalMatching G M`: `M` is a set of edges of `G`, pairwise vertex-disjoint, and every edge of `G` shares a
  vertex with an edge of `M`. `saturationNumber` is the `sInf` of their sizes (every finite graph has one, so this
  is a true minimum; for `F_k` the rim matching is exhibited).
- `harmonicIndex` sums `2/(d(u) + d(v))` over `edgeFinset` in `ℚ` (via `Sym2.lift`).
- Proof of `μ* ≥ k`: each rim edge must meet an edge of `M`, and an edge of `F_k` meets the rim of only one triangle.

## Dead ends
None.
