---
problem: Hinrichs–Vybíral conjecture on positive positive-definite functions ([f(x_j − x_k)] ⪰ J_n / n)
source: https://arxiv.org/abs/2609.21733 (J. Vybíral, Sep 2026, v1 only); conjecture: Hinrichs and Vybíral, J. Complexity 27 (2011), Conjecture 2
lean_statement: Lab/HinrichsVybiral/Basic.lean (all definitions stated by us)
status: solved (formalized)
---

# Hinrichs–Vybíral conjecture

## Statement
Let `f : ℝ^d → ℝ` be continuous, bounded, nonnegative and positive definite with `f(0) = 1`. Conjecture: for all `n`
and points `x_1, …, x_n`, the matrix `[f(x_j − x_k)]` dominates `J_n / n` (all-ones matrix over `n`).

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False in dimension 7: `f = P(cos x₁, …, cos x₇)`, `P = (21 + 4E₂ + 4E₃ + E₄)/280`, points `0, πe₁, …, πe₇`, coefficients `−1, 1, …, 1`: form `22/5 < 9/2` | Vybíral 2609.21733 | Yes (HV-1) |
| A strictly positive variant `(1 − δ) f + δ`, `δ < 1/316` | same | No |
| True for `f = |g|²` with `g` positive definite | Vybíral 2020 | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| HV-1 | Lean: the Hinrichs–Vybíral conjecture is false (Vybíral's 7-dimensional example) | Kyle + Claude (Opus 5.5), 2026-11-28 | proved (awaiting internal audit) | `not_hinrichsVybiralConjecture`, `f_posDef`, `f_nonneg` in `Lab/HinrichsVybiral/Basic.lean` |

Statement notes for the Auditor:
- `IsPosDef f`: for all `n`, points `x` and complex `c`, `0 ≤ ∑_{j,k} c_j c̄_k f(x_j − x_k)` in `ℂ`'s order (real and
  nonnegative), i.e. every matrix `[f(x_j − x_k)]` is Hermitian positive semidefinite. This is the standard (strongest)
  hypothesis.
- The conclusion is the real-coefficient consequence `∑ c_j c_k f(x_j − x_k) ≥ (∑ c_j)² / n` of `⪰ J_n / n`; refuting
  this weaker conclusion refutes the matrix inequality.
- `f` is written as `(1/280) ∑_S w(|S|) ∏_{ℓ∈S} cos x_ℓ` with `w = (21,0,4,4,1,0,0,0)`, which is `P(cos x)` since
  `E_r = ∑_{|S| = r} ∏_{ℓ∈S} y_ℓ`.
- Positive definiteness is proved by the real feature expansion `∏_S cos(a − b) = ∑_{t ⊆ S} φ_t(a) φ_t(b)`, not by
  Fourier series. Nonnegativity: affine in each variable, plus `decide` on the 128 sign vectors.
