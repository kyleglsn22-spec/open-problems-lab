# Non-abelian GMR: a smaller four-set counterexample (GMR-1)

Scripts behind the order-`2^17` counterexample in `Lab/GMR/Counterexample.lean`.

* `find_disjoint_blocks.py W NB`: enumerates the label sets of one full `3 x 3` block
  (`{a, b, a+b, c, d, c+d, a+c, b+d, a+b+c+d}` for `a, b, c, d` in `F_2^W`) and finds `NB`
  pairwise disjoint ones avoiding `0`. `python3 find_disjoint_blocks.py 5 3` finds three, so
  27 distinct nonzero labels fit in `W = F_2^5`.
* `verify_order_2_17.py`: builds the class-two group `F_2^6 x F_2^6 x F_2^5` from those
  blocks, checks associativity on random triples, and computes `|ABCD|` and the four slice
  maxima by brute force: `|S| = 114688`, `N = (2368, 16384, 16384, 2368)`,
  `|S|^3 = 1508529953308672 > 1505231418425344 = N1 N2 N3 N4` (ratio `1372/1369`).
* `block_designs.py`: within the "blocks of `d`-dimensional row and column spaces" family
  (Elsholtz's sparse single-coordinate template, arXiv:2611.12776 Proposition 6.8, with block incidences), lists
  designs with ratio `> 1` by total dimension `k1 + k2 + w` (group order `2^(k1+k2+w)`).
  The minimum is 17, from three `(2,2)` blocks. Next: 19 (e.g. two `(3,3)` blocks, ratio 1.187).
  This is a search over one family only; it does not rule out smaller groups of other shapes.

Why this group cannot shrink further inside this family: `|S| = 64 * 64 * 28 = 114688 > 2^16`,
so any 2-group containing this configuration has order at least `2^17`.
