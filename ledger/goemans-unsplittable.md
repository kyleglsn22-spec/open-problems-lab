---
problem: Goemans's unsplittable-flow conjecture (single source; cost-preserving 1-admissible rounding)
source: https://arxiv.org/abs/2611.23244 (Ge, Xie, Li, Li, Sep 2026, Section 2.2.2; counterexample credited to Rybin)
lean_statement: Lab/Goemans/Unsplittable.lean (all definitions stated by us)
status: solved (formalized)
---

# Goemans's unsplittable-flow conjecture

## Statement
Single-source network with nonnegative arc costs and terminals `t_i` with positive demands `d_i`, `D = max d_i`.
Dinitz–Garg–Goemans (1999): every fractional flow `f` can be rounded to an unsplittable flow `g` with
`load_g(a) ≤ load_f(a) + D` on every arc. Goemans conjectured (personal communication, January 2000, cited by
Salazar–Skutella 2009) that this is possible with `cost(g) ≤ cost(f)` as well.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| 1-admissible rounding always exists (no cost condition) | Dinitz–Garg–Goemans 1999 | No |
| False: 7 vertices, 9 arcs, demands `15, 10, 15`, fractional cost `58`, every 1-admissible unsplittable flow costs `≥ 60` | Ge–Xie–Li–Li 2611.23244 §2.2.2 (Rybin) | Yes (GUF-1) |
| Characterization of seven-vertex counterexamples; census of arborescence shapes | same paper, §§3–4, App. A–D | No |

AFTD (checked 2026-11-28) has definitions for this paper's seven-vertex network but no theorem.

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| GUF-1 | Lean: Goemans's conjecture is false, via the seven-vertex network of 2611.23244 §2.2.2 | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, internal audit pass | `not_goemansConjecture`, `unsplittable_bad`, `fracFlow_isFlow`, `fracCost_eq` in `Lab/Goemans/Unsplittable.lean` |

Statement notes for the Auditor:
- `Network V`: a decidable arc relation (so no parallel arcs), real costs `≥ 0`, a source. `IsPath`: a duplicate-free
  vertex list from `a` to `b` whose consecutive vertices are arcs.
- A fractional flow is a finite path decomposition `List (terminal × path × amount)`, amounts `≥ 0`, paths `s`–`t_i`,
  amounts per terminal summing to `d i`. Arc load is the sum of amounts of entries whose path uses that arc.
- The conjecture quantifies over every finite vertex type, every network, `k + 1 ≥ 1` terminals, positive demands
  and every fractional flow, and asks for one path per terminal with `load ≤ fractional load + max demand` on every
  ordered pair and total cost `≤` the fractional cost. Restricting to simple digraphs and simple paths only narrows
  the hypotheses, so the disproof also refutes the original.
- Path enumeration: every `s`–`t_i` path lies in `walks 6 0` (bounded DFS, completeness lemma `mem_walks`, length
  `≤ 7` by `Nodup`); `walks_end` (by `decide`) leaves only the two paths per terminal.
