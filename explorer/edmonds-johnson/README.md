# Edmonds–Johnson property (Del Pia, arXiv:2611.28580)

Scripts behind `Lab/EdmondsJohnson/` and claims EJ-1 to EJ-4 (see `ledger/edmonds-johnson.md`).
Need Python 3 with numpy, scipy and sympy. Run from this folder.

| Script | What it does |
| --- | --- |
| `search.py A6p` / `search.py A7` | Searches for integral data `b, c, l, u` and a point `z ∈ (⅓ℤ)ⁿ` where every side has slack ⅓ or ≥ 1, the slack-⅓ normals are distinct and nonzero mod 2, and `z` is outside the integer hull (LP over the integral points). Found the data used for `A₆⁺` and `A₇`. |
| `gen.py` | Vertices of `P` (all bases, exact), the box that a counterexample `w` to the integer statement must lie in, a brute-force check of that box, and a separating inequality for the integer hull. |
| `leangen.py` | Writes `Lab/EdmondsJohnson/A6.lean`, `A6plus.lean`, `A7.lean` (picks a small set of vertices that still gives a small box). |
| `thmgen.py`, `thmgen2.py` | THM certificates (`2S⁻¹` or a kernel vector for every increasing square submatrix) and the `THM*/Size*.lean` files. |
| `minors.py` | Closure of `A₆` under the minor operations, up to row/column permutation and sign (full canonical form; slow). |
| `minors2.py A6` / `A6p` / `A7` | Same with a faster canonical form (permutes only within invariant classes); reports whether `A₃, A₄, A₆, A₆⁺, A₇` occur. |

Results of `minors2.py` (2026-11-28): `A₆` 3,388 classes, `A₆⁺` 4,874, `A₇` 5,156; entries stay in
`{0, ±1, ±2}`; none contains `A₃` or `A₄`, and none of `A₆, A₆⁺, A₇` is a minor of another. `minors.py`
reproduces 3,388 for `A₆`.
