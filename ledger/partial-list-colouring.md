---
problem: Partial List Colouring Conjecture (Albertson–Grossman–Haas 2000)
source: https://arxiv.org/abs/2609.23291 (Noel, disproof, Sep 2026)
lean_statement: Lab/PartialList/Counterexample.lean (list colouring definitions from formal-conjectures FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/List.lean; the conjecture stated by us)
status: solved (formalized)
---

# Partial List Colouring Conjecture

## Statement
Let `G` have `n` vertices and list chromatic number `χ_ℓ(G) = k ≥ 2`, and let `1 ≤ ℓ < k`. For every assignment
`L` of lists of `ℓ` colours, at least `n ℓ / k` vertices of `G` can be properly coloured from their lists.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False: 14 vertices (four triangles `T₁..T₄`, two non-adjacent terminals joined to the two non-private vertices of each triangle), `χ_ℓ = 3`, a 2-list assignment with at most 9 < 28/3 colourable vertices | Noel, arXiv 2609.23291 (found by ChatGPT 6 Astra Ultra) | Yes (PLC-1) |
| At least `(6/7) n ℓ / k` vertices always | Chappell 1999 | No |
| At least `n / ⌈k/ℓ⌉` vertices; conjecture true when `ℓ ∣ k` | Haas–Hanson–MacGillivray 2003 | No |
| True if `Δ(G) ≤ k`, or if the union of lists has at most `k` colours | Janssen 2001 | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| PLC-1 | Lean: Noel's graph has `listChromaticNumber = 3`, and every proper partial colouring from his 2-lists colours at most 9 vertices; hence `¬ PartialListColouringConjecture` | Kyle + Claude (Opus 5.5), 2026-11-27 | checked (Lean, CI pending); audit pending | `not_partialListColouringConjecture`, `exists_counterexample` in `Lab/PartialList/Counterexample.lean`; Python cross-check `explorer/partial-list/check.py` (exhaustive: maximum is exactly 9) |

Statement notes for the Auditor:
- `IsKChoosable G k` and `listChromaticNumber G = sInf {k | G.IsKChoosable k}` are formal-conjectures' definitions
  (pinned commit): lists of exactly `k` colours from `ℕ`, and a proper colouring `C : G.Coloring ℕ` with `C v ∈ L v`.
- `PartialListColouringConjecture` (ours): for every finite type `V`, graph `G`, and `1 ≤ ℓ < χ_ℓ(G)`, every `L` with
  `|L v| = ℓ` admits a set `S` and colours `c` with `c v ∈ L v` on `S`, `c u ≠ c v` for adjacent `u, v ∈ S`, and
  `|V| · ℓ ≤ |S| · χ_ℓ(G)` (the bound `|S| ≥ nℓ/k` without division). `k ≥ 2` follows from `1 ≤ ℓ < k`.
- Colours are natural numbers, as in formal-conjectures; this loses nothing for finite graphs.
- Proof follows the paper: `partial_le_nine` (triangles with a common 2-list, plus the terminal pair argument),
  `terminal_choice` (common colour, or the 8 < 9 counting of bad pairs), `tri_extend` (greedy triangle colouring),
  and `not_isKChoosable_of_le_two` (the triangle 2, 3, 4).

## Log
- 2026-11-27: picked as the "easier" slot (round-4 shortlist #4). Not on AFTD (kb.json searched for the arXiv id,
  "partial list", "Albertson") and not in formal-conjectures (latest commit ea8e3e1 has only the choosability
  definitions). Lean proof written and checked locally: builds in ~50 s, standard axioms, leanchecker 7.2 GB peak.

## Dead ends
- (none)

## Leads
- Noel asks for *connected* counterexamples whose gap from `nℓ/k` is large (disjoint copies give a large gap
  trivially). A computer search over small connected graphs built from the same triangle-and-terminal gadget is a
  natural hard follow-up.
