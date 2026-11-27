---
problem: Albertson–Berman induced-forest ratio c_P and the Chappell–Pelsmajer bounded-degree conjecture (planar graphs)
source: https://arxiv.org/abs/2608.23260 (Cames van Batenburg–Goedgebeur–Jooken, Aug 2026, Problems 5.1 and 5.3)
lean_statement: none (search only)
status: open (attempted, no improvement)
---

# Albertson–Berman ratio and Chappell–Pelsmajer for d = 2..6

## Statement
- `a(G)` = largest induced forest. `c_P = inf a(G)/|V(G)|` over planar `G`. Known: `2/5 ≤ c_P ≤ 25/52`
  (Borodin; `G52` of 2608.23260). Problem 5.1 asks to improve either bound.
- `f_d(G)` = largest induced forest with maximum degree `≤ d`. Chappell–Pelsmajer (2013) conjecture:
  `f_d(G) > 2dn/(4d+1)` for planar `G`. The `G52` family disproves it for `d ≥ 7`. Problem 5.3: open for `2 ≤ d ≤ 6`.
  For `d = 6` the threshold is `12/25 = 0.48`, just below `25/52 ≈ 0.4808`.

## What we checked (2026-11-27, hard slot)
| Item | Result |
| --- | --- |
| Recompute the paper's graphs (`Q`, `R`, `G29`, `G41`, `G52`, edge lists transcribed from the TikZ figures) | `a` matches the paper. Also `f_2 = f_3 = … = f_6 = a` for all five: each has a maximum induced forest that is a linear forest, so the degree bound costs nothing there. `G52` misses `d = 6` by `25` vs `24.96`. `check_paper.py` |
| Small triangulations (random flips, essentially all up to 10 vertices) | min `f_2/n = 1/2`; nothing near `4/9` |
| Edge-gadget calculus: skeleton triangulation `H`; on each edge glue copies of a 2-port gadget with profile `p'(X)` (interior forest value for port set `X`); `a = max_S |S| + Σ p'`. ILP over integer multiplicities, target ratio `12/25` | Infeasible for every skeleton `H` up to 11 vertices with `R`, `Q` (1146 of 1249 triangulations on 11 vertices hit), and up to 9 vertices with 13 extra Pareto gadgets and 4 vertex gadgets. Even target `0.4807` infeasible up to 9 vertices. `skel.py`, `skel2.py` |
| Gadget search: Pareto fronts of random triangulation gadgets (edge, vertex and face ports); annealing seeded from `R` and `Q` with flips, vertex insertion and deletion | Nothing beats `25/52` (hub template) or `19/39` (triangle template). `gadgets.py`, `gad_anneal.py`, `gad3.py` |
| Face-gadget calculus (3-port gadgets in triangular faces, 44 Pareto gadgets) plus the edge and vertex gadgets | Infeasible at `12/25` up to 9 skeleton vertices. `skel3.py` |
| Degree forcing by gluing `m` copies of a small gadget at one vertex (`onesum.py`) | Cannot work alone: `f_d` of the sum is at least `m·a(J − v)`, so the gadget minus its port must already be a dense Albertson–Berman example. Best scores stay above the threshold. |

## Take-aways
- `25/52` looks locally optimal for gadget-gluing constructions over small skeletons. A better ratio likely needs a
  gadget that is not a small modification of `Q`/`R` (both icosahedron variants), or ports that are not adjacent.
- For `d ≤ 6` the degree bound only helps once the forests a construction allows are forced to branch. In all known
  examples the maximum forests are paths, so Problem 5.3 for `d = 6` is essentially as hard as beating `0.48` for `a`.

## Next ideas if revisited
- 2-port gadgets with non-adjacent ports (needs a "connected inside" flag in the profile).
- Exhaustive gadget generation from icosahedron-like 5-regular cores instead of random triangulations.
