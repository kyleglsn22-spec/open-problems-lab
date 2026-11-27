---
problem: Chen–van der Holst–Luo–Ma conjecture on edge-colouring cyclic odd-fold covers (s_ℓ(G) = L_ℓ(G))
source: https://arxiv.org/abs/2611.13394 (R. Wang, Nov 2026, Corollary 1.4)
lean_statement: Lab/OddFoldCovers/Petersen.lean (all definitions stated by us)
status: solved (formalized, case ℓ = 3)
---

# Edge-colouring odd-fold covers

## Statement
For a loopless multigraph `G` and odd `ℓ ≥ 3`, `s_ℓ(G)` is the least chromatic index of a cyclic `ℓ`-fold cover of
`G` (vertex set `V × ℤ/ℓ`; edge `e = uv` with voltage `α(e)` lifts to `(u,i)(v,i+α(e))`), and
`L_ℓ(G) = max(Δ(G), max_{S odd, |S| ≥ 3} ⌈2ℓ|E(G[S])| / (ℓ|S| − 1)⌉)`. Always `L_ℓ ≤ s_ℓ`. Chen, van der Holst,
Luo and Ma (Conjecture 1 of their paper on edge-colouring spectra of cyclic covers) conjectured `s_ℓ(G) = L_ℓ(G)`.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| `L_ℓ ≤ a_ℓ ≤ s_ℓ ≤ max(Δ + 1, L_ℓ)` | Wang, Thm 1.2 | No |
| False: Petersen-based `F_ℓ` (multigraph, 30 vertices) and `G_ℓ` (simple) have `L_ℓ = 3ℓ`, `s_ℓ = 3ℓ + 1` | Wang, Cor 1.4 | Yes for `F_3`, lower bound `s_3 ≥ 10` (OFC-1) |
| Spectrum of connected cyclic / all covers is an interval | Wang, Thm 1.5 | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| OFC-1 | Lean: for Wang's 9-regular multigraph `F_3` (Petersen graph with each vertex replaced by a triangle with 4 parallel edges per side), `L_3(F_3) = 9` but no cyclic 3-fold cover is 9-edge-colourable, so `s_3(F_3) ≥ 10` and the conjecture is false | Kyle + Claude, 2026-11-27 | audited (internal audit PASS, PR 34 review) | `F_L`, `no_nine_colouring`, `F_sCyc`, `not_conjecture` in `Lab/OddFoldCovers/Petersen.lean` |

Statement notes for the Auditor:
- `Multigraph V E`: maps `src tgt : E → V` with `src e ≠ tgt e` (loopless; parallel edges allowed; the orientation is
  the paper's reference orientation for voltages). `cover G ℓ α` has vertices `V × ZMod ℓ`, edges `E × ZMod ℓ`, and
  `(e, i)` joins `(src e, i)` to `(tgt e, i + α e)`.
- `IsProper c` (for `c : E → Fin k`): distinct edges with a common end get different colours.
  `chromaticIndex = sInf {k | ∃ proper c : E → Fin k}`; `sCyc G ℓ = sInf {χ'(cover G ℓ α) | α}`.
- `L G ℓ = max (sup of degrees) (sup over odd S with |S| ≥ 3 of ⌈(2ℓ·edgesIn S : ℚ) / (ℓ|S| − 1)⌉₊)`;
  `edgesIn S` counts edges with both ends in `S`, `degree v` counts edges with `v` as an end.
- `Conjecture` quantifies over all finite `V`, `E` and all odd `ℓ ≥ 3`. We refute it at `ℓ = 3`.
- Proof follows Wang's Lemma 3.1 and the spoke count in Section 4. Finite facts use `decide +kernel` (Petersen odd
  cuts over all 1024 vertex sets, degrees of `F`, a small search over Petersen perfect matchings). No `set_option`.

## Dead ends and notes
- Not formalized: the matching upper bound `s_3(F_3) = 10`, general odd `ℓ`, and the simple-graph family `G_ℓ`.
