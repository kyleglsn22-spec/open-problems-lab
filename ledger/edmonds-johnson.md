---
problem: Gerards–Schrijver conjecture on the Edmonds–Johnson property of totally half-modular matrices
source: https://arxiv.org/abs/2611.28580 (Del Pia, v1, 20 Nov 2026; the only version as of 2026-11-28)
lean_statement: Lab/EdmondsJohnson/Basic.lean, Lab/EdmondsJohnson/THMBasic.lean (definitions stated by us)
status: disproved (paper); Lean: the failure of the Edmonds–Johnson property and total half-modularity are formalized, the "no A₃/A₄ minor" clause is computer-checked only
---

# The Gerards–Schrijver conjecture (Edmonds–Johnson property)

## Statement
An integral matrix `A` has the *Edmonds–Johnson (EJ) property* if for all integral `b, c, l, u` the first
Chvátal closure of `P(A; b, c, l, u) = {x : b ≤ Ax ≤ c, l ≤ x ≤ u}` equals its integer hull. `A` is
*totally half-modular* (THM) if every nonsingular square submatrix has a half-integral inverse. Gerards and
Schrijver conjectured (communicated 2007) that a THM matrix has the EJ property if and only if it has no minor
equal to `A₃` or `A₄` (two specific 3 × 3 and 3 × 4 matrices). Minors: delete, permute or negate rows and
columns; halve an all-even row; pivot on an entry equal to 1.

## Known results
| Result | Reference | Checked by us? |
| --- | --- | --- |
| `A₆` (5 × 6) is THM, fails EJ, has no `A₃`/`A₄` minor, so the conjecture is false | Del Pia 2611.28580, Thm 1.2 | THM and failure of EJ: Lean (EJ-1, EJ-2). No minor: computer (EJ-4) |
| `A₆` is a minimal obstruction | same, Thm 1.4 | No |
| `A₆⁺` and `A₇` are also THM, fail EJ, have no `A₃`/`A₄` minor | same, §6, stated **without proof** | THM and failure of EJ: Lean (EJ-3). No minor: computer (EJ-4) |
| Open: are `A₃, A₄, A₆, A₆⁺, A₇` all the minimal obstructions? Finitely many? | same, Question 6.1 | Open |

AFTD (checked 2026-11-28) lists only Question 6.1; no formalization of the paper's theorems.

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| EJ-1 | Lean: `A₆` does not have the EJ property (Del Pia, Prop. 3.3, with the paper's data) | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, internal audit pass with notes | `not_hasEJProperty_A6` in `Lab/EdmondsJohnson/A6.lean` |
| EJ-2 | Lean: `A₆` is THM (Prop. 2.4) | same | proved, internal audit pass with notes | `isTHM_A6` in `Lab/EdmondsJohnson/THM6/Main.lean` |
| EJ-3 | Lean: `A₆⁺` and `A₇` do not have the EJ property and are THM. These are Del Pia's claims (§6, stated without proof); ours are the first proofs we know of, with our own data `b, c, l, u, z` | same | proved, internal audit pass with notes | `not_hasEJProperty_A6plus`, `not_hasEJProperty_A7`, `isTHM_A6plus`, `isTHM_A7` |
| EJ-4 | Computer (exact, not Lean): the minors of `A₆`, `A₆⁺`, `A₇` form 3,388, 4,874 and 5,156 classes up to row/column permutation and sign (counting the empty matrix; 3,387 / 4,873 / 5,155 without it, as the Auditor's own search found). None is `A₃` or `A₄`, and none of the three matrices is a minor of another. All entries stay in `{0, ±1, ±2}` | same | computed | `explorer/edmonds-johnson/minors2.py` (and the slower full-canonical `minors.py`, which reproduces 3,388 for `A₆`) |

## How the Lean proof avoids LP duality
The paper shows that its point `z` is in the Chvátal closure with the Appa–Kotnyek description of the closure of
THM systems by `{0, ½}`-cuts, which rests on LP duality (not in Mathlib). We use a primal criterion instead
(`mem_chvatalClosure_of_witness` in `Basic.lean`): a CG cut `w·x ≤ ⌊δ⌋` holds at `z` as soon as some point
`v ∈ P` has `w·v ≥ ⌈w·z⌉`, since then `δ ≥ w·v ≥ ⌈w·z⌉`, an integer. We take `v` among vertices of `P` (all
half-integral), so the statement "for every integral `w` some vertex has `w·v ≥ ⌈w·z⌉`" is about integers only.
A would-be counterexample `w` satisfies `w·(v − z) ≤ 2/3 − 1/2` for every vertex `v`, which bounds it to a box of
9 points (18 for `A₇`); `omega` derives the bounds and checks each point. This needs no structure of `A` beyond
the vertices, so it applies to other bounded instances whose vertices share a small denominator and whose point
`z` is interior (so that the box is finite), as long as the point really is in the closure.

Statement notes for the Auditor:
- `poly`, `chvatalClosure` (all `w ∈ ℤⁿ`, all real `δ` with `w·x ≤ δ` valid on `P`), `integerHull`
  (`convexHull` of the integral points of `P`) and `HasEJProperty` (all integral `b, c, l, u`) follow §1 of the paper.
- `IsTHM A`: for every `k`, injective `r : Fin k → rows`, injective `c : Fin k → columns` with `det ≠ 0`, every
  entry of `2 S⁻¹` is an integer (over `ℚ`). The proof covers singular `S` too (where Mathlib's `S⁻¹ = 0`).
- `A6`, `A6plus`, `A7` are transcribed from the paper (§1 and §6). `A₆`'s data are the paper's `(3)`.
- The "no `A₃`/`A₄` minor" clause of Theorem 1.2 (needed to call `A₆` a counterexample to the conjecture) is
  **not** in Lean; EJ-4 checks it by computer. A Lean proof would need a formal theory of minors (pivots, halving)
  and a closure certificate over ~3,400 classes, or the paper's graph-encoding argument (§4). Minimality (Thm 1.4)
  is not checked.
- Generators: `explorer/edmonds-johnson/` (`search.py` finds data for `A₆⁺`, `A₇`; `leangen.py` writes the
  instance files; `thmgen2.py` writes the THM certificates). Independent checker: `audit/edmonds_johnson_check.py`.
