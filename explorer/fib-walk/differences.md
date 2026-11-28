# Where `D_ℓ ≠ U_ℓ` (numerical and certified evidence)

`gap_differences.py LIMIT LMAX` computes `D_ℓ` and `U_ℓ` from all members below `LIMIT`. With `LIMIT = 3·10⁶`
and `ℓ ≤ 80`, the sets differ for `ℓ = 4, 7, 8, 9, 12, 15, 16` and for every `ℓ` from 17 to 80.
Many of the larger differences are single occurrences at large `n`. Those may be artefacts of the cutoff:
Mao–Zhao's density theorem (2608.19886, Thm 1.4) says gaps of positive upper density occur for both types.

`certify_differences.py L1 L2 SHIFTS THR` keeps only differences that are *certified* by this method.
Such a gap `g` is realised by one type in a window starting below `THR`, but not by the other type
in any window starting below `THR`. Every window lying entirely at or above `THR` is ruled out by the
threshold lemma and the same-type shift lemmas with shifts `f_j`, `j ∈ SHIFTS`. Feasibility is computed
in floating point, so this is evidence, not proof. Each certified case can be turned into a Lean proof
the way FW-3 does it.

| shifts | threshold | certified differences, `ℓ ≤ 24` |
| --- | --- | --- |
| `f_2..f_6` | 105 | `ℓ = 4` (`9 ∈ U \ D`), `ℓ = 7` (`17 ∈ D \ U`) |
| `f_2..f_7` | 300 | additionally `ℓ = 8, 9, 12, 15, 17, 18` |
| `f_2..f_8` | 715 | `ℓ = 4, 7, 8, 9, 12, 15, 16, 17, 18, 20, 21, 22, 23, 24` |

`ℓ = 7` is Lean-proved (FW-3, `Lab/FibWalk/Seven/Main.lean`).
