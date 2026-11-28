# Petersen colouring: searching for a counterexample below 52 vertices

Hard-slot attempt, 2026-11-28. Target: Problem in Goedgebeur et al., arXiv:2608.10028, "What is the smallest bridgeless
cubic graph that does not admit a P-colouring?" They give two 52-vertex counterexamples (a theoretical proof) and show
by computer (all 7.1 billion weak snarks on 38 vertices, about 12 CPU years) that every counterexample has at least 40
vertices. A smallest counterexample is a weak snark (cyclically 4-edge-connected, not 3-edge-colourable).

Result: **nothing below 52 found.** Everything here is negative evidence and tooling.

## Tools
- `pcol.py`: SAT encoding of P-colourings (a P-colouring is the same as a normal 5-edge-colouring). `colourable`
  (with symmetry breaking at vertex 0) and `pcol_set` (all colour tuples on the dangling edges of a multipole).
  `hog` reads a House of Graphs JSON adjacency list.
- `multi.py`: cubic multipoles; `W` = Petersen graph minus two adjacent vertices (8 vertices, 4 dangling edges),
  `F` = two copies of `W` plus a subdivision vertex (17 vertices, 5 dangling edges), `ring3` = the paper's `G52`
  (three `F`s in a ring plus a central vertex). Reproduces: `G52` has no P-colouring.
- `colF.py`: `|Col(W)| = 315`, `|Col(F)| = 1380` boundary colourings.
- `compl.py`: the boundary colourings `S` of the complement of one `F` in `G52` (`|S| = 1740`, disjoint from `Col(F)`).
  A 5-pole `X` can replace that `F` iff, for some ordering of its dangling edges, `Col(X) ∩ S = ∅`.
- `univ.py`: parity constraint. For each of the 6 perfect matchings `M` of the Petersen graph, the preimage of `M`
  is a perfect matching of the cubic graph, so a multipole with `k` vertices has `#(dangling edges coloured in M) ≡ k
  (mod 2)`. For 5-poles (k odd) this leaves 23,220 possible boundary tuples; `S ∪ Col(F)` uses only 3,120 of them.
- `orbits.py`: `S` and `Col(F)` split into 18 and 13 orbits under `Aut(P)` (orders 120 and 60).

## Searches (all negative)
| Search | Size | Result |
| --- | --- | --- |
| `small4.py`: every 4-pole on ≤ 6 vertices, test `Col ⊆ Col(W)` up to relabelling | 2, 4, 6 vertices | none (so `W` cannot be shrunk inside `F`) |
| `search5.py`: random 5-poles from pieces `W`, single vertices, Petersen-minus-a-vertex, replacing one/two/three `F`s | ≤ 17 vertices | ~5,000 tried, none |
| `search6.py`: random bridgeless cubic assemblies of `F`, `W`, vertices, Petersen-minus-a-vertex | 40–50 vertices | ~43,000 tested, all P-colourable |
| `rand5.py`: random general 5-poles (configuration model), replacing one `F` in `G52` via the `S` test | 7–15 vertices (graphs of 42–50) | ~2,800 tested, none (`verify.py` showed earlier "hits" were bridged graphs, now filtered) |

## Why this is hard, and what would be needed
- Random assemblies are almost always 3-edge-colourable, hence trivially P-colourable; a real search must generate weak
  snarks only. The 38-vertex case alone took the authors 12 CPU years; exhaustive 40–50 is far out of reach for us.
- A targeted approach that might still work: exhaustive (not random) generation of cyclically 4-edge-connected
  5-poles on 9–15 vertices whose colouring sets avoid `S`, i.e. structured replacements inside `G52`. This needs an
  orderly generator (nauty/geng); building downloaded C code was not possible in our sandbox.
