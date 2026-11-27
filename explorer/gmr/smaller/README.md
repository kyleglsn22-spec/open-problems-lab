# Can the GMR counterexample get smaller than 131,072? (round 2, negative so far)

Goal: a four-set counterexample to the non-abelian Gyarmati–Matolcsi–Ruzsa inequality in a group of
order below `2^17 = 131,072` (our GMR-1). Result of this round: **no smaller group found**. What we
can say is a size floor: for the whole "commuting background" family, which contains every published
four-set example and ours, the only shapes that could go below 131,072 are listed below, and our
shape is within 14% of its floor.

Notation (Elsholtz's double-coset template, arXiv:2611.12776, §5): `A = H`, `D = J` are subgroups with
`H ∩ J = 1`; `B ⊂ J`, `C ⊂ H`. The cell `(y, z) ∈ B × C` gets the label `H y z J`. The label `HJ` is the
"background"; other labels are "rare". In a **block design**, `B = Y_1 ⊔ … ⊔ Y_m`, `C = Z_1 ⊔ … ⊔ Z_m`,
`|Y_i| = k_i`, `|Z_i| = l_i`. Cells inside a block are rare with pairwise distinct labels, and cells
between different blocks are background. GMR-1 is three `3 × 3` blocks; Elsholtz's Theorem 5.1 examples
are two `r × s` blocks in `G0 × G0`.

## 1. Floor for commuting background (paper proof, not Lean-checked, not audited)

**Lemma.** Suppose `y z = z y` for every background cell (`y ∈ Y_i`, `z ∈ Z_j`, `i ≠ j`). Then
`|H| ≥ ∏ (l_i + 1)` and `|J| ≥ ∏ (k_i + 1)`.

*Proof.* Let `F_i = C_H(⋃_{j≠i} Y_j)`. It is a subgroup and contains `Z_i`. Fix `y_i ∈ Y_i`. For `z ∈ H`,
`H y_i z J = H (z⁻¹ y_i z) J`. So the `l_i` rare labels in row `y_i` and the background label (`z = e`) come
from pairwise distinct conjugates `z⁻¹ y_i z`, `z ∈ Z_i ∪ {e}`. So the conjugacy orbit of `y_i` under `F_i`
has at least `l_i + 1` elements. Pick `R_i ⊂ F_i` with `|R_i| = l_i + 1` and the elements `f y_i f⁻¹`
(`f ∈ R_i`) pairwise distinct. If `f_1 ⋯ f_m = f'_1 ⋯ f'_m` with `f_i, f'_i ∈ R_i`, then conjugating `y_1` by
both sides gives `f_1 y_1 f_1⁻¹ = f'_1 y_1 f'_1⁻¹`, because `f_2, …, f_m` lie in `F_2, …, F_m`, which centralise
`Y_1`. So `f_1 = f'_1`. Cancel `f_1` and repeat with `y_2`, and so on. So `R_1 × ⋯ × R_m → H` is injective.
The `J` side is symmetric, using `H y z J = H (y z y⁻¹) J` and `E_j = C_J(⋃_{i≠j} Z_i) ⊇ Y_j`. ∎

When all rare double cosets are free (size `|H||J|`; a smaller one only lowers the ratio), the ratio of a
block design is exactly `L³ / (R_1 R_4 r_2 r_3)`. Here `L = 1 + Σ k_i l_i`, `R_4 = Σ k_i (l_i + 1)`,
`R_1 = Σ l_i (k_i + 1)`, `r_2 = 1 + max l_i` and `r_3 = 1 + max k_i`, with the identity excluded from
`B` and `C` (including it is the "+e" variant, which never helps). Also `|G| ≥ |S| = L |H| |J|`.

`floor_enumeration.py` lists every block design (any number of blocks, any block sizes) with ratio above 1
and `L ∏(k_i+1)(l_i+1) < 131,072`:

| blocks | ratio | floor for `|S|` (so for `|G|`) |
| --- | --- | --- |
| two `4 × 6` | 1.0004 | 60,025 |
| two `5 × 5` | 1.0235 | 66,096 |
| two `4 × 7` | 1.0334 | 91,200 |
| two `5 × 6` | 1.0723 | 107,604 |
| three `3 × 3` (GMR-1's shape) | 1.0586 | 114,688 |

So with commuting background, a group below 131,072 needs a **two-block** design. Three `3 × 3`
blocks can only fit in orders 114,688 to 131,071. That is also the
`H = J = 64`, `|S| = 64 · 64 · 28` count of GMR-1, which is optimal for its shape.

Side note: GMR-1's group gives the larger ratio `343/324 ≈ 1.0586` when the identity is left out of `B`
and `C`. GMR-1 has `1372/1369` because it includes it. The group order is unchanged.

## 2. Our group family is exhausted, even for non-block patterns

Within class-two groups `V1 × V2 × W` over `F_2` (GMR-1's family), "block" is not essential: any rare
pattern where every row and column has 3 rare cells (`n = 9` rows and columns) gives ratio 1.0586 with
`L = 28`. A naive count suggested such a pattern might fit in `2^5 × 2^5 × 2^5`. It cannot. Write
`X = Yᵀ M Z` for each coordinate `M` of the form. The rows of `X` lie in `R = rowspace(Z)`, with
`dim R ≤ dim V1`. In row `i`, the three rare values are distinct and nonzero only if `R` contains the
even-weight vectors on that row's three rare columns. So `dim R ≥ 9 − (#connected components)`. A
3-regular bipartite component has at least 3 columns, so `dim V1 ≥ 6`, and `dim V2 ≥ 6` by symmetry. Then
`2^(6+6+5) = 2^17` again. (Unfinished CP-SAT runs on the `5,5,5` and `5,5,6` cases also found nothing, which agrees.) The affine version `F_2^n ⋊ J`, with background columns fixed by the
background rows, gives `|J| ≥ 64` by the same product argument.

## 3. Computer searches (no hits)

Tool: `pairs.g` (GAP) lists subgroup pairs `(H, J)`, `H ∩ J = 1`, up to conjugacy. `ev.py` builds the exact
label, coset and double-coset data. `sat.py` (CP-SAT) decides whether a given block shape exists, and
`drive.py` runs the shapes. `validate_on_gmr1.py` re-finds GMR-1's three blocks in 1 s and proves
`5×(2×2)` and `13×(1×1)` impossible there. CP-SAT also handles **non-commuting** background, which
the floor above does not cover.

Searched, all pairs with `|H|, |J| ≥ 10`, every uniform block shape (`m` blocks of `k × l`, `k, l ≤ 7`)
that can give ratio above 1. There was a 4 s cap per shape; a few checks timed out, mostly in `A7` and
`PSL(2,16)`, and the logs list them. The groups: `PSL(2,q)` for `q = 11, 13, 16, 17, 19, 23, 27, 29`,
`PGL(2,11)`, `PGL(2,13)`, `A7`, `PSL(3,3)`. Two-block shapes only, `25 ≤ |H|, |J| ≤ 100`: `M12`
(order 95,040, 237 pairs). The rest of the sweep is listed in the ledger log. No block design was found.
An earlier plain annealing search was useless: it could not even re-find GMR-1.

## 4. What is still open

* **Two-block designs with commuting background** in a group of order 60,025 to 131,071. The two blocks
  generate subgroups `U_1, U_2` of order at least 936 (for `5 × 5`), so they must overlap in at least 7
  elements while `Y_2` centralises `Z_1` and `Y_1` centralises `Z_2`. Direct products (Elsholtz) need
  `|U|²/|Z|`. We know no construction.
* **Non-commuting background.** Background cells only need `y z ∈ HJ`. For the slice counts to stay small,
  all background cells in a row or column must share their `H`- or `J`-part, which means `y z = h_z j_y`.
  When `j_y ≠ y`, the background columns of a row lie in a non-identity coset of `H ∩ y⁻¹Hy`, and the
  lemma's proof breaks. This is the one route that could reach a few tens of thousands; it needs a
  concrete group with that coset structure.
