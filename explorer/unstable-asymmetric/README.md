# Asymmetric unstable graphs (Mizzi's current conjecture): search notes

This is a hard-slot attempt, and the result is negative. Mizzi (arXiv:2603.27559 v3/v4) conjectures that every
connected, non-bipartite, vertex-determining, **asymmetric** unstable graph contains cycles `C_k` and `C_{2k}` for
some odd `k`. A graph `G` is unstable if `Aut(G × K₂)` is larger than `Aut(G) × ℤ₂`. For an asymmetric `G`, that
means `G × K₂` has more than 2 automorphisms.

## Result
There is **no** connected, non-bipartite, vertex-determining, asymmetric unstable graph on 9 or fewer vertices. So
any counterexample to the current conjecture has at least 10 vertices. This is a computation (Python and
networkx), not a Lean proof.

| n | method | asymmetric candidates tested | asymmetric unstable |
| --- | --- | --- | --- |
| ≤ 7 | all graphs in the networkx atlas (`atlas.py`) | 149 | 0 |
| 8 | every one-vertex extension of every 7-vertex graph (`ext.py`) | 47,278 (with repeats) | 0 |
| 9 | every one-vertex extension of every 8-vertex graph (`ext.py`) | 1,639,902 (with repeats) | 0 |

Every `n`-vertex graph is a one-vertex extension of an `(n−1)`-vertex graph, so the extensions cover all
graphs. The deduplicated 8-vertex list has 12,346 graphs, which matches OEIS A000088.

**Sanity check.** Mizzi's 7-vertex example is `C_6` plus a vertex joined to an antipodal pair. It has
`|Aut(G)| = 4` and `|Aut(G × K₂)| = 16 > 8`, so the instability test flags it as unstable. That example is not
asymmetric.

## Random search (`random_tf.py`)
This script builds random graphs that are closed under a random two-fold automorphism `(α, β)` with `α ≠ β`, on
7–20 vertices. About 1,500 connected, non-bipartite, vertex-determining graphs came out of it, and none was
asymmetric. Graphs built this way almost always pick up an ordinary automorphism, so random search is a poor
way to find asymmetric unstable graphs.

## Next step if resumed
Exhaustive `n = 10` (about 12 million graphs) needs nauty's `geng`, which is not available here. Pure Python
would take days.
