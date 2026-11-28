import Lab.EdmondsJohnson.THM6plus.Size5

/-!
# `A6plus` is totally half-modular

Stated without proof in Del Pia (arXiv:2611.28580), Section 6. Checked with one certificate for each of the 461 square submatrices with
increasing row and column indices (`isTHM_of_certs`; certificates in `Size1` … `Size5`).
-/

namespace EdmondsJohnson

/-- The certificate tables of `A6plus`, by size. -/
def tableA6plus : ℕ → CertTable
  | 1 => tableA6plus_1
  | 2 => tableA6plus_2
  | 3 => tableA6plus_3
  | 4 => tableA6plus_4
  | _ => tableA6plus_5

/-- **`A6plus` is totally half-modular.** -/
theorem isTHM_A6plus : IsTHM A6plus := by
  refine isTHM_of_certs A6plus tableA6plus (fun k h1 h5 => ?_)
  interval_cases k
  · exact certsA6plus_1
  · exact certsA6plus_2
  · exact certsA6plus_3
  · exact certsA6plus_4
  · exact certsA6plus_5

end EdmondsJohnson
