# Albertson–Berman ratio / Chappell–Pelsmajer searches

Search code for Problems 5.1 and 5.3 of arXiv 2608.23260. No improvement found; see `ledger/albertson-berman.md`.

- `fd.py`: exact `a(G)` and `f_d(G)` with OR-tools CP-SAT plus lazy cycle cuts.
- `check_paper.py`: recomputes `a` and `f_2..f_6` for the paper's graphs (`paper_graphs.json`).
- `skel.py`, `skel2.py`, `skel3.py`: skeleton ILP. Glue gadgets on edges, vertices or triangular faces of a small
  triangulation; find integer multiplicities with `a ≤ (num/den)·n`.
- `gadgets.py`, `gad3.py`: Pareto search for 2-port and 3-port gadget profiles. `gad_anneal.py`: annealing of gadgets
  against fixed templates (hub of three, triangle, single edge).
- `onesum.py`: degree forcing by gluing copies at one vertex (Chappell–Pelsmajer `d = 2..6`).
- `anneal_tri.py`: random planar triangulations and edge flips.

Requires `networkx` and `ortools`.

## Claim AB-1 (Lean disproof of the conjecture with `G₂₉`)
- `ab1_check.py`: Python cross-check of the Lean data (`a(G29) = 14`, drawing has no crossings, cycle lists
  hit every large vertex set on both sides of the separating edge).
- `g29_coords.json`: integer drawing (rounded Tutte embedding of a triangulation containing `G₂₉`).
- `g29_cycles.json`: hitting cycle lists per side and port case (greedy cover).
- `lean-gen/`: regenerates `Lab/AlbertsonBerman/*.lean` (`python3 gen_lean.py && python3 gen_lean2.py`).
