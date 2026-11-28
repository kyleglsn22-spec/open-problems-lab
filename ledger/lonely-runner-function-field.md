---
problem: Chow–Rimanić conjecture (lonely runners in function fields): |F| < 1 + q + ⋯ + q^k implies δ(F) ≥ q^{-k}
source: https://arxiv.org/abs/2608.18818 (X. Hu, Aug 2026, Theorem 1.2 and Proposition 3.1); conjecture: S. Chow and L. Rimanić, Mathematika 65 (2019) 677–701 (arXiv:1711.01207)
lean_statement: Lab/LonelyRunner/FunctionField.lean (all definitions stated by us; case q = 2)
status: solved (formalized)
---

# Chow–Rimanić lonely runner conjecture over function fields

## Statement
For `α ∈ T^{-1}𝔽_q[[T^{-1}]]` and `f ∈ 𝔽_q[T]`, `‖α f‖` is `q^{-m}` for the highest power `T^{-m}` with nonzero
coefficient in the fractional part of `α f`. For a finite family `F` of nonzero polynomials,
`δ(F) = sup_α min_{f ∈ F} ‖α f‖`. Conjecture: `|F| < 1 + q + ⋯ + q^k` implies `δ(F) ≥ q^{-k}`.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| True when `|F| ≤ q^k` (union bound); true under a small-degree hypothesis; `C₂(q) ≥ q² + 0.4877q − O(1)` | Chow–Rimanić 2019 | No |
| False: 13 monic polynomials over `𝔽₂` with `δ = 2^{-4}`, so `C₃(2) ≤ 13 < 15` | Hu 2608.18818, Thm 1.2 | Yes (LR-1, the bound `δ ≤ 2^{-4}`) |
| `C_k(q) ≥ q^k + c_k q^{2/3}` for large `q`; `k = 2` refinement | Hu 2608.18818, Thms 1.3–1.5 | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| LR-1 | Lean: the conjecture is false (already for `q = 2`, `k = 3`): Hu's 13 nonzero polynomials over `𝔽₂` have `δ(F*) ≤ 2^{-4} < 2^{-3}` | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, internal audit pass with notes | `not_chowRimanicConjectureTwo`, `delta_Fstar_le`, `cover` in `Lab/LonelyRunner/FunctionField.lean`; independent check `audit/lonely_runner_ff_check.py` |

Statement notes for the Auditor:
- A time `α` is a sequence `α : ℕ → ZMod 2`, `α n` = coefficient of `T^{-n}` (`α 0` unused). The coefficient of
  `T^{-m}` in `α f` is `fracCoeff α f m = ∑_j f_j α_{m+j}`. `lonelyNorm α f = 2^{-m₀}` for the least `m₀ ≥ 1`
  with a nonzero coefficient, `0` if none.
- `delta F hne = sSup` over all `α` of `F.inf' (lonelyNorm α)` (in `ℝ`). Nonemptiness of `F` matches the original's
  `1 ≤ |F|` (Chow–Rimanić, Conjecture "LRC in function fields").
- Only the case `q = 2` is stated; refuting it refutes the all-`q` conjecture. Lean proves `δ(F*) ≤ 2^{-4}`; the
  paper's matching lower bound (`α = T^{-4}`) is not needed and not formalized.

## Dead ends
None.
