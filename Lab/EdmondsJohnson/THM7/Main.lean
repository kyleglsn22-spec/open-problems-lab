import Lab.EdmondsJohnson.THM7.Size5

/-!
# `A7` is totally half-modular

Stated without proof in Del Pia (arXiv:2611.28580), Section 6. Checked with one certificate for each of the 791 square submatrices with
increasing row and column indices (`isTHM_of_certs`; certificates in `Size1` … `Size5`).
-/

namespace EdmondsJohnson

/-- The certificate tables of `A7`, by size. -/
def tableA7 : ℕ → CertTable
  | 1 => tableA7_1
  | 2 => tableA7_2
  | 3 => tableA7_3
  | 4 => tableA7_4
  | _ => tableA7_5

/-- **`A7` is totally half-modular.** -/
theorem isTHM_A7 : IsTHM A7 := by
  refine isTHM_of_certs A7 tableA7 (fun k h1 h5 => ?_)
  interval_cases k
  · exact certsA7_1
  · exact certsA7_2
  · exact certsA7_3
  · exact certsA7_4
  · exact certsA7_5

end EdmondsJohnson
