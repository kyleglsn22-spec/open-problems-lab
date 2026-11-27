---
problem: Bipanchromatic number conjecture of Lalou–Mbarek–Skender–Togni (χ_B = χ_P − ⌈α/2⌉)
source: https://arxiv.org/abs/2610.27133 (Novaković–Jojić, sunflower counterexamples, Oct 2026); first disproof https://arxiv.org/abs/2610.08042
lean_statement: Lab/Bipanchromatic/Sunflower.lean (all definitions stated by us)
status: solved (formalized)
---

# Bipanchromatic colourings of hypergraphs

## Statement
A panchromatic `k`-colouring of a hypergraph gives every hyperedge all `k` colours; `χ_P` is the largest such `k`.
A colour is unique if exactly one vertex has it; `α` is the least number of unique-colour vertices over panchromatic
`χ_P`-colourings. A bipanchromatic colouring is a panchromatic one with no unique colour; `χ_B` is the largest such
`k`. Lalou, Mbarek, Skender and Togni (Discrete Appl. Math. 2026, Conjecture 1), motivated by completely independent
spanning trees in split graphs, conjectured `χ_B = χ_P − ⌈α/2⌉` (pairing the unique colours is optimal).

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False: three-hyperedge sunflowers `H_{d,q}`, excess exactly `d` | Lalou et al., arXiv 2610.08042 | No |
| False: sunflowers `S_n` (`n ≥ 3`) have `χ_P = n+1`, `α = n`, `χ_B = n`, excess `⌈n/2⌉ − 1`; `S_3` is smallest | Novaković–Jojić, arXiv 2610.27133, Thm 3.1 | Yes (BP-1) |
| Minimum order of an excess-`d` counterexample is `4d + 2`; ratio `χ_B/β < 2`, sharp | Novaković–Jojić | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| BP-1 | Lean: Novaković–Jojić Theorem 3.1. For every `n ≥ 3` the sunflower `S_n` has `χ_P = n + 1`, `α = n`, `χ_B = n`. Hence the conjecture is false (already for `S_3`, 6 vertices, 3 hyperedges), and no added constant repairs it | Kyle + Claude, 2026-11-27 | pending audit | `sunflower_parameters`, `not_conjecture`, `excess_unbounded` in `Lab/Bipanchromatic/Sunflower.lean` |

Statement notes for the Auditor:
- Hypergraph = finite vertex type `V` with `E : Finset (Finset V)`. A `k`-colouring is `c : V → Fin k`;
  `IsPanchromatic E c` says every hyperedge meets every colour (so all `k` colours are used once `E` is nonempty).
- `uniqueVerts c` = vertices `v` such that no other vertex has colour `c v`.
- `chiP = sSup {k | ∃ panchromatic c : V → Fin k}`, `alphaK E k = sInf {#uniqueVerts c | c panchromatic k-colouring}`,
  `alpha = alphaK E (chiP E)`, `chiB = sSup {k | ∃ panchromatic c with no unique vertex}`. For `S_n` every set is
  shown to have a greatest/least element, so `sSup`/`sInf` are genuine maxima/minima there.
- `Conjecture` is stated with extra hypotheses (at least 2 vertices, a hyperedge, all hyperedges of size `≥ 2`),
  which only makes the disproof stronger; `⌈α/2⌉` is written `(α + 1)/2`.
- No `decide`, no `set_option`.

## Dead ends and notes
- Not formalized: the paper's minimum-order classification (order `4d + 2`) and the ratio results.
