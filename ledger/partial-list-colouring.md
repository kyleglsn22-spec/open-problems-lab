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
| PLC-1 | Lean: Noel's graph has `listChromaticNumber = 3`, and every proper partial colouring from his 2-lists colours at most 9 vertices; hence `¬ PartialListColouringConjecture` | Kyle + Claude (Opus 5.5), 2026-11-27 | audited (internal audit PASS, PR 10 review) | `not_partialListColouringConjecture`, `exists_counterexample` in `Lab/PartialList/Counterexample.lean`; Python cross-check `explorer/partial-list/check.py` (exhaustive: maximum is exactly 9) |
| PLC-2 | Lean: answers Noel's question about connected counterexamples with a large gap. For every `t ≥ 1`, the chain of `t` copies of Noel's graph (vertex 3 of copy `j+1` joined to vertex 2 of copy `j`) is connected, has `listChromaticNumber = 3`, and from Noel's lists on each copy at most `9t` of its `n = 14t` vertices can be coloured, against the promised `28t/3`. So the gap is at least `t/3 = n/42`, linear in `n` (Chappell's bound caps it at `2n/21`) | Kyle + Claude (Opus 5.5), 2026-11-27 | pending audit | `connected_gap`, `chain_connected`, `listChromaticNumber_chain`, `chain_partial_le` in `Lab/PartialList/Connected.lean`; cross-check `explorer/partial-list/connected_check.py` (CP-SAT: maximum is exactly `9t` for `t ≤ 5`; 6000 random 3-list assignments colourable) |

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

Statement notes for PLC-2:
- `connected_gap t` (for `t ≥ 1`) gives a graph `H` on `Fin t × Fin 14` with `H.Connected`,
  `H.listChromaticNumber = 3`, and 2-lists `L` such that every proper partial colouring `(S, c)` from `L` has
  `|S| ≤ 9t` and `|V| · 2 ≥ |S| · χ_ℓ(H) + t`, i.e. the deficit `nℓ/k − |S|` is at least `t/3`.
- Upper bound: within a copy the chain contains Noel's graph, so `partial_le_nine` applies to each copy.
- 3-choosability: copies are coloured in order. The new lemma `colour_avoid` says Noel's graph is colourable from
  any 3-lists even when vertex 3 must avoid one given colour `f`. Proof: Noel's terminal-pair count still works,
  because the first triangle (now with the 2-list `X = L 3 \ {f}` on vertex 3) rules out at most 2 of the 9 pairs:
  every bad pair lies inside `Y = L 4` if `X ⊆ Y`, and inside `X` otherwise (`bad_cases`, `bad_sub`).
- Making a *private* vertex or a *terminal* the attachment point fails (found by brute force: some 3-lists
  then have no colouring), which is why the link goes into vertex 3.

## Log
- 2026-11-27: PLC-2. Chain of copies of Noel's graph gives connected counterexamples with gap `n/42`; Lean proof for all `t`, builds locally, standard axioms. Novelty: no follow-up to Noel's question found on arXiv or the web.
- 2026-11-27: picked as the "easier" slot (round-4 shortlist #4). Not on AFTD (kb.json searched for the arXiv id,
  "partial list", "Albertson") and not in formal-conjectures (latest commit ea8e3e1 has only the choosability
  definitions). Lean proof written and checked locally: builds in ~50 s, standard axioms, leanchecker 7.2 GB peak.

## Dead ends
- Attaching new copies through a single hub vertex adjacent to each copy's private vertex: the copy is then
  not always colourable when the private vertex loses a colour, so 3-choosability can fail.
- Attaching through a terminal: same problem (brute force finds 3-lists with no colouring).

## Leads
- Noel's connected-large-gap question: answered by PLC-2 (gap `n/42`). Still open: the best constant. The gap
  lies between `n/42` (ours) and `2n/21` (Chappell). Also open: whether other `(k, ℓ)` admit connected linear-gap
  examples (our chain trick needs a base example plus a vertex whose list can lose a colour).
