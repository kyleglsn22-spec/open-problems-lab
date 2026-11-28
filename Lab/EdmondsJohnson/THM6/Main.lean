import Lab.EdmondsJohnson.THM6.Size5

/-!
# `A6` is totally half-modular

Del Pia (arXiv:2611.28580), Proposition 2.4. Checked with one certificate for each of the 461 square submatrices with
increasing row and column indices (`isTHM_of_certs`; certificates in `Size1` … `Size5`).
-/

namespace EdmondsJohnson

/-- The certificate tables of `A6`, by size. -/
def tableA6 : ℕ → CertTable
  | 1 => tableA6_1
  | 2 => tableA6_2
  | 3 => tableA6_3
  | 4 => tableA6_4
  | _ => tableA6_5

/-- **`A6` is totally half-modular.** -/
theorem isTHM_A6 : IsTHM A6 := by
  refine isTHM_of_certs A6 tableA6 (fun k h1 h5 => ?_)
  interval_cases k
  · exact certsA6_1
  · exact certsA6_2
  · exact certsA6_3
  · exact certsA6_4
  · exact certsA6_5

end EdmondsJohnson
