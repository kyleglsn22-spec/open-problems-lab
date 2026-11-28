---
problem: Smallest bridgeless cubic graph without a Petersen colouring (counterexample to Jaeger's Petersen Colouring Conjecture)
source: https://arxiv.org/abs/2608.10028 (Goedgebeur et al., Aug 2026)
lean_statement: none
status: open (gap 40 ≤ n ≤ 52); attempted 2026-11-28, no improvement
---

# Petersen colouring: smallest counterexample

## Statement
Jaeger's Petersen Colouring Conjecture (every bridgeless cubic graph has a P-colouring, i.e. a normal 5-edge-colouring) is
false: Goedgebeur et al. give two 52-vertex counterexamples with a theoretical proof, and show by computer that every
counterexample has at least 40 vertices. Open: the exact minimum order.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| No counterexample on ≤ 38 vertices (weak snarks on 38: 12 CPU years) | 2608.10028 | No |
| Counterexamples on 52 vertices (`G52` = ring of three 17-vertex 5-poles `F` plus a centre) | 2608.10028 | Yes, by SAT (not Lean) |
| Infinite family for every even order ≥ 60 | 2608.10028 | No |

## Claims
None. Attempt notes and scripts: `explorer/petersen-colouring/` (all searches negative; key facts: `|Col(W)| = 315`,
`|Col(F)| = 1380`, complement set `|S| = 1740`, parity universe 23,220 boundary tuples for 5-poles).

## Dead ends
- Shrinking `W` inside `F`: no 4-pole on ≤ 6 vertices has `Col ⊆ Col(W)`.
- Random 5-pole replacements (≤ 17 vertices) and random bridgeless assemblies on 40–50 vertices: all colourable.
- Lesson: random cubic graphs are 3-edge-colourable almost always; only weak-snark generation is meaningful.
