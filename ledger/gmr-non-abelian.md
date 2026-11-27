---
problem: Non-abelian Gyarmati–Matolcsi–Ruzsa inequality (GMR 2010, Combinatorica 30, Problem 1.3)
source: https://arxiv.org/abs/2611.00156 (Nair–Namayandeh–Zhu, disproof) and https://arxiv.org/abs/2611.12776 (Elsholtz)
lean_statement: Lab/GMR/Counterexample.lean (`NonAbelianGMR`, our own statement; not in formal-conjectures)
status: solved (formalized); smaller-group search active
---

# Non-abelian Gyarmati–Matolcsi–Ruzsa inequality

## Statement
For finite nonempty sets `A_1, …, A_n` in any group, `|A_1 ⋯ A_n|^(n-1) ≤ ∏ N_i`, where
`N_i = max_{a ∈ A_i} |A_1 ⋯ A_{i-1} a A_{i+1} ⋯ A_n|`. (True in abelian groups, GMR Thm 1.2; true for `n = 3`.)

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False for `n = 4` in `D_4^14` (order `8^14`) | Nair–Namayandeh–Zhu, arXiv 2611.00156 (30 Oct 2026) | No |
| Double-coset mechanism; smallest four-set group found `A_6^2 × C_2^2`, order 518,400 ("no minimality claimed"); class-two 2-group of order `2^23`; open whether the sparse template beats 518,400 | Elsholtz, arXiv 2611.12776 (9 Nov 2026), Theorem 6.7 (class-two 2-group), Proposition 6.8 (sparse single-coordinate template), Table 3 and Question 9.1 | Our GMR-1 is his sparse-template proposition with a new incidence/realisation |
| **Four-set counterexample in a class-two group of order `2^17 = 131,072`** | Ours (GMR-1) | Lean-checked |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| GMR-1 | The four-set inequality fails in the class-two group `G = F_2^6 × F_2^6 × F_2^5`, `(c,b,w)(c',b',w') = (c+c', b+b', w+w'+ω(b,c'))`, `ω` block diagonal with three `2×2` blocks; ratio `1372/1369`. Hence `¬ NonAbelianGMR`, in a group of order 131,072 (published smallest for four and five sets: 518,400). Padding with a singleton (his Lemma 2.2) gives a five-set counterexample in the same group. Smaller groups are already known for six or more sets (1728 for n = 6–9, 243 for n ≥ 10) | Kyle + Claude, 2026-11-26 | Lean-checked, audited (internal; verdict on PR 43) | `not_nonAbelianGMR`, `exists_counterexample_card` in `Lab/GMR/Counterexample.lean`; brute force in `explorer/gmr/verify_order_2_17.py` |

Statement notes for the Auditor:
- `sliceMax A i = (A i).sup (fun a => card (List.ofFn (update A i {a})).prod)`; product is the ordered pointwise
  product `A_1 * (A_2 * ( … * 1))`. For `i = 0` this is `|{a} A_2 ⋯ A_n|`, which equals `|A_2 ⋯ A_n|` (as in the paper).
- `NonAbelianGMR` quantifies over `G : Type` with `[Group G] [DecidableEq G]`, all `n`, all families of nonempty Finsets.
- The proof gives only what is needed: `|S| ≥ 64·64·28` and upper bounds `N_1, N_4 ≤ 37·64`, `N_2, N_3 ≤ 64·64·4`
  (the brute force shows these are equalities). Label counts (28 labels, rows/columns ≤ 4, 37 pairs) are kernel `decide`s.
- Novelty: Elsholtz explicitly leaves open whether the sparse template beats 518,400 (end of §6, after Proposition 6.8). No later paper
  (arXiv search, 26 Nov 2026); not on AFTD; not in formal-conjectures.

## Log
- 2026-11-27: smaller-group search, round 2 (Kyle + Claude). **No group below 131,072 found.** Details and
  scripts: `explorer/gmr/smaller/`. Findings: (1) a size floor (paper proof, not Lean-checked; internal audit PASS with notes on PR 12) for block designs with free rare double cosets: if the background pairs commute, `|H| ≥ ∏(l_i+1)` and `|J| ≥ ∏(k_i+1)`. An exhaustive list then
  shows that the only block designs that could fit below 131,072 are two-block designs (`4×6`: floor
  60,025; `5×5`: 66,096; `4×7`: 91,200; `5×6`: 107,604) and GMR-1's three `3×3` blocks (floor 114,688,
  so GMR-1 is within 14% of optimal for its shape). (2) In GMR-1's class-two `F_2` family, non-block
  patterns where every row and column has 3 rare cells also need `6 + 6 + 5` dimensions. (3) A CP-SAT pattern
  finder (it re-finds GMR-1 in 1 s) found no block design in `PSL(2,q)` (`q ≤ 29`), `PGL(2,11/13)`, `A7`,
  `PSL(3,3)` (all subgroup pairs of order ≥ 10), or in `M12` and `S4 ≀ S3` (two-block shapes, `25 ≤ |H|,|J| ≤ 100`).
  Side note: GMR-1's group gives ratio `343/324 ≈ 1.0586` when the identity is dropped from `B` and `C`.
- 2026-11-26: PR 43 merged 5:28 PM ET (squash d4a0cda) after CI green and internal audit PASS (Thm 6.7/Prop 6.8 citations, scope to n = 4, 5).
- 2026-11-26: Lean proof done (build 8.05 GB, leanchecker 6.8 GB, ~30 s, standard axioms). Kernel pitfall: any
  instance mismatch (e.g. a separate `Mul H` instance vs. the one inside `Group H`) or `rw`/`simp` closing the goal
  by evaluation makes the kernel compute the 2^17-element products and run out of memory. Fixes in the file:
  one `Group H` instance holding `mul/one/inv`, arithmetic lemmas stated on variables (`arith`, `absurd_aux`).
- 2026-11-26: found the order-2^17 example: Elsholtz's `2^23` example uses 9 independent row/column vectors;
  replacing his 9×9 circulant pattern by three full 3×3 blocks, each living on a 2-dim row space and 2-dim column
  space (rows `y1, y2, y1+y2`), drops the dimension from 9+9+5 to 6+6+5. Three disjoint 9-label blocks fit in
  `F_2^5` (`explorer/gmr/find_disjoint_blocks.py`). Brute-force verified.
- 2026-11-26: annealing over general bilinear maps did not even recover the known example (search landscape too flat).

## Dead ends
- Three-block designs with commuting background below order 114,688: impossible (floor above).
- Class-two `F_2` groups with any 3-regular 9×9 rare pattern: need `dim V1, dim V2 ≥ 6`, so no gain over `2^17`.
- Plain simulated annealing over `B, C` in a fixed group: it cannot even re-find GMR-1, so don't use it. Use the CP-SAT finder.
- Odd `p` in the same family: scalar multiples repeat labels; best designs need far more dimensions (3^16+).
- Within block designs, 17 dimensions is optimal (`block_designs.py`); `|S| > 2^16` rules out a smaller 2-group for this configuration.

## Open leads
- (Round 2) Two-block designs with commuting background in a group of order 60,025 to 131,071 (needs two
  subgroups `U_1, U_2` of order ≥ 936 overlapping in ≥ 7 elements, with `Y_2` centralising `Z_1` and `Y_1`
  centralising `Z_2`). Direct products cannot do it.
- (Round 2) Non-commuting background (`y z = h_z j_y` with `j_y ≠ y`): the floor's proof breaks here, and
  this is the only route we see to orders of a few tens of thousands. It needs a concrete group.
- Non-class-two groups for the sparse template: needs subgroups `H, J` of order ≥ 10 with 27 distinct double cosets
  and commuting non-incident pairs; `|S|` could in principle be as small as a few thousand.
- Multi-rare `m = 3` (`r = s = 3`) with central twisting: `|S| = 114,688` at best, so no better than ours.
- Lean-check the published 518,400 example or the general double-coset theorem (lower priority now).
